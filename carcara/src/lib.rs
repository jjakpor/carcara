#![deny(clippy::disallowed_methods)]
#![deny(clippy::self_named_module_files)]
#![deny(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::branches_sharing_code)]
#![warn(clippy::cloned_instead_of_copied)]
#![warn(clippy::copy_iterator)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::doc_markdown)]
#![warn(clippy::equatable_if_let)]
#![warn(clippy::explicit_into_iter_loop)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::from_iter_instead_of_collect)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_not_else)]
#![warn(clippy::implicit_clone)]
#![warn(clippy::inconsistent_struct_constructor)]
#![warn(clippy::index_refutable_slice)]
#![warn(clippy::inefficient_to_string)]
#![warn(clippy::items_after_statements)]
#![warn(clippy::large_types_passed_by_value)]
#![warn(clippy::manual_assert)]
#![warn(clippy::manual_ok_or)]
#![warn(clippy::map_unwrap_or)]
#![warn(clippy::match_wildcard_for_single_variants)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::multiple_crate_versions)]
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::redundant_pub_crate)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::trivially_copy_pass_by_ref)]
#![warn(clippy::unnecessary_wraps)]
#![warn(clippy::unnested_or_patterns)]
#![warn(clippy::unused_self)]

#[macro_use]
pub mod ast;
pub mod benchmarking;
pub mod checker;
pub mod elaborator;
pub mod parser;
mod resolution;
mod utils;

use crate::benchmarking::{CollectResults, OnlineBenchmarkResults, RunMeasurement};
use ast::{Proof, ProofCommand, ProofIter, ProofStep, Subproof};
use checker::{error::CheckerError, CheckerStatistics};
use parser::{ParserError, Position};
use core::{panic, slice};
use std::io;
use std::time::{Duration, Instant};
use thiserror::Error;

pub type CarcaraResult<T> = Result<T, Error>;

fn wrap_parser_error_message(e: &ParserError, pos: &Position) -> String {
    // For unclosed subproof errors, we don't print the position
    if matches!(e, ParserError::UnclosedSubproof(_)) {
        format!("parser error: {}", e)
    } else {
        format!("parser error: {} (on line {}, column {})", e, pos.0, pos.1)
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("{}", wrap_parser_error_message(.0, .1))]
    Parser(ParserError, Position),

    #[error("checking failed on step '{step}' with rule '{rule}': {inner}")]
    Checker {
        inner: CheckerError,
        rule: String,
        step: String,
    },

    // While this is a kind of checking error, it does not happen in a specific step like all other
    // checker errors, so we model it as a different variant
    #[error("checker error: proof does not conclude empty clause")]
    DoesNotReachEmptyClause,
}

pub fn check<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
) -> Result<bool, Error> {
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, parser_config)?;
    run_measures.parsing = total.elapsed();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, checker_config);
    if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&problem, &proof, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: run_measures.elaboration,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
                elaboration_pipeline: Vec::new(),
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&problem, &proof)
    }
}

pub fn check_parallel<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    collect_stats: bool,
    num_threads: usize,
    stack_size: usize,
) -> Result<bool, Error> {
    use crate::checker::Scheduler;
    use std::sync::Arc;
    let mut run_measures: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, pool) = parser::parse_instance(problem, proof, parser_config)?;
    run_measures.parsing = total.elapsed();

    // Checking
    let checking = Instant::now();
    let (scheduler, schedule_context_usage) = Scheduler::new(num_threads, &proof);
    run_measures.scheduling = checking.elapsed();
    let mut checker = checker::ParallelProofChecker::new(
        Arc::new(pool),
        checker_config,
        &problem.prelude,
        &schedule_context_usage,
        stack_size,
    );

    if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: OnlineBenchmarkResults::new(),
        };
        let res = checker.check_with_stats(&problem, &proof, &scheduler, &mut checker_stats);

        run_measures.checking = checking.elapsed();
        run_measures.total = total.elapsed();

        checker_stats.results.add_run_measurement(
            &("this".to_owned(), 0),
            RunMeasurement {
                parsing: run_measures.parsing,
                checking: run_measures.checking,
                elaboration: run_measures.elaboration,
                scheduling: run_measures.scheduling,
                total: run_measures.total,
                polyeq: checker_stats.polyeq_time,
                assume: checker_stats.assume_time,
                assume_core: checker_stats.assume_core_time,
                elaboration_pipeline: Vec::new(),
            },
        );
        // Print the statistics
        checker_stats.results.print(false);

        res
    } else {
        checker.check(&problem, &proof, &scheduler)
    }
}

pub fn check_and_elaborate<T: io::BufRead>(
    problem: T,
    proof: T,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: elaborator::Config,
    pipeline: Vec<elaborator::ElaborationStep>,
    collect_stats: bool,
) -> Result<(bool, ast::Problem, ast::Proof, ast::PrimitivePool), Error> {
    let mut run: RunMeasurement = RunMeasurement::default();

    // Parsing
    let total = Instant::now();
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, parser_config)?;
    run.parsing = total.elapsed();

    let mut stats = OnlineBenchmarkResults::new();

    // Checking
    let checking = Instant::now();
    let mut checker = checker::ProofChecker::new(&mut pool, checker_config);
    let checking_result = if collect_stats {
        let mut checker_stats = CheckerStatistics {
            file_name: "this",
            polyeq_time: Duration::ZERO,
            assume_time: Duration::ZERO,
            assume_core_time: Duration::ZERO,
            results: std::mem::take(&mut stats),
        };

        let res = checker.check_with_stats(&problem, &proof, &mut checker_stats);
        run.checking = checking.elapsed();
        run.polyeq = checker_stats.polyeq_time;
        run.assume = checker_stats.assume_time;
        run.assume_core = checker_stats.assume_core_time;

        stats = checker_stats.results;
        res
    } else {
        checker.check(&problem, &proof)
    }?;

    // Elaborating
    let elaboration = Instant::now();

    let node = ast::ProofNode::from_commands(proof.commands);
    let (elaborated, pipeline_durations) =
        elaborator::Elaborator::new(&mut pool, &problem, elaborator_config)
            .elaborate_with_stats(&node, pipeline);
    let elaborated = ast::Proof {
        commands: elaborated.into_commands(),
        ..proof
    };

    if collect_stats {
        run.elaboration = elaboration.elapsed();
        run.total = total.elapsed();
        run.elaboration_pipeline = pipeline_durations;

        stats.add_run_measurement(&("this".to_owned(), 0), run);

        stats.print(false);
    }

    Ok((checking_result, problem, elaborated, pool))
}

pub fn generate_lia_smt_instances<T: io::BufRead>(
    problem: T,
    proof: T,
    config: parser::Config,
    use_sharing: bool,
) -> Result<Vec<(String, String)>, Error> {
    use std::fmt::Write;
    let (problem, proof, mut pool) = parser::parse_instance(problem, proof, config)?;

    let mut iter = proof.iter();
    let mut result = Vec::new();
    while let Some(command) = iter.next() {
        if let ast::ProofCommand::Step(step) = command {
            if step.rule == "lia_generic" {
                if iter.depth() > 0 {
                    log::error!(
                        "generating SMT instance for step inside subproof is not supported"
                    );
                    continue;
                }

                let mut problem_string = String::new();
                write!(&mut problem_string, "{}", problem.prelude).unwrap();

                let mut bytes = Vec::new();
                ast::printer::write_lia_smt_instance(
                    &mut pool,
                    &problem.prelude,
                    &mut bytes,
                    &step.clause,
                    use_sharing,
                )
                .unwrap();
                write!(&mut problem_string, "{}", String::from_utf8(bytes).unwrap()).unwrap();

                writeln!(&mut problem_string, "(check-sat)").unwrap();
                writeln!(&mut problem_string, "(exit)").unwrap();

                result.push((step.id.clone(), problem_string));
            }
        }
    }
    Ok(result)
}

/** If command is a step, replace rule with hole. If assume, leave alone. Otherwise, panic. */
fn holeify_premise(step: ProofCommand) -> ProofCommand{
    match step {
        ProofCommand::Step(step) => 
        ProofCommand::Step(ProofStep {rule: "hole".to_string(),
         premises: Vec::new(), 
         discharge: Vec::new(),
          id: step.id.clone(), 
          clause: step.clause.clone(), 
          args:step.args.clone()}),
        ProofCommand::Assume {id:_, term:_}=> step,
        _ => panic!("Expected step or assume"),

    }
     
}
/* fn commands_at_depth(mut premises_iter: &std::slice::Iter<'_, (usize, usize)>, 
depth: usize, 
index:usize, 
mut commands: &mut Vec<ProofCommand>,
mut iter: &ProofIter<'_>) -> Option<&(usize, usize)>  {
    while let Some((d, i)) = *premises_iter.next()  {
        if *d == depth {
            commands.push(holeify_premise(iter.get_premise((*d, *i)).clone()));
        }
    }
}  */
fn commands_at_depth<'a>(depth: usize, commands: &'a mut Vec<ProofCommand>, mut next_premise: Option<&'a (usize, usize)>, new_premises: &mut Vec<(usize, usize)>, iter: &ProofIter<'a>, premises_iter: &mut std::slice::Iter<'a, (usize, usize)>) -> Option<&'a (usize, usize)> {
    let mut new_premise_index = 0;
    while let Some((d, i)) = next_premise  {
        if *d == depth {
            commands.push(holeify_premise(iter.get_premise((*d, *i)).clone()));
            new_premises.push((0, new_premise_index));
            new_premise_index += 1;
            next_premise = premises_iter.next();
        } else {
            break;
        }
    }
    next_premise
}
pub fn small_slice1b(proof: &Proof, id: &str) -> Proof {

    let mut new_proof : Proof = Proof { constant_definitions: proof.constant_definitions.clone(), commands: Vec::new()};

    let mut iter = proof.iter();
    let mut subproof_stack: Vec<&Subproof> = Vec::new();
    let mut sliced_step: Option<&ProofCommand> = None;
    while let Some(command) = iter.next() {
        if command.id() == id {
            sliced_step = Some(command);
            break;
        }
        if let ProofCommand::Subproof(subproof) = command {
            subproof_stack.push(&subproof);
        }

        if iter.is_end_step() {
            subproof_stack.pop();
        }
    }
    // println!("{:?}", sliced_step);
    // if let Some(ProofCommand::Step(proof_step)) = sliced_step
    if matches!(sliced_step, Some(ProofCommand::Step(_))) | matches!(sliced_step, Some(ProofCommand::Subproof(_))) {
        let proof_step : &ProofStep = match sliced_step {
            Some(ProofCommand::Step(step)) => step,
            Some(ProofCommand::Subproof(sp)) => {
                let last_command = sp.commands.last().unwrap();
                if let ProofCommand::Step(s) =  last_command {
                    s
                } else {
                    panic!("Subproof does not end in step")
                }
            },
            _ => panic!("Command is not step or subproof despite matching")
        };
        // println!("{:?}", proof_step);
        let mut premises = proof_step.premises.clone();
        premises.sort();

        let mut premises_iter= premises.iter();
        let mut next_premise: Option<&(usize, usize)> = premises_iter.next();

        

        let mut commands: &mut Vec<ProofCommand> = &mut new_proof.commands;

        let mut new_premises : Vec<(usize, usize)> = Vec::new();
        let mut new_premise_index: usize = 0;
        
        // next_premise = commands_at_depth(0, commands, next_premise, &mut new_premises, &iter, &mut premises_iter);
        // Code smell--just wanted to avoid missing this case
        while let Some((d, i)) = next_premise  {
            if *d == 0 {
                commands.push(holeify_premise(iter.get_premise((*d, *i)).clone()));
                new_premises.push((0, new_premise_index));
                new_premise_index += 1;
                next_premise = premises_iter.next();
            } else {
                break;
            }
        }

        

        // Collect top level premises
        // If not in subproof, that's the end.
        // If in subproof, need to get deeper premises and create subproofs
        if !iter.is_in_subproof() {
            let new_step = ProofStep {
                premises: new_premises,
                 ..proof_step.clone() // Discharges could be wrong
                };
            commands.push(ProofCommand::Step(new_step));
        }
        else {
       
        let mut depth:usize = 0;
        /* I could make top-level "level 0" */
        // println!("Subproof stack length is {}", subproof_stack.len());
        for (j, sp) in subproof_stack.iter().enumerate() {
            new_premise_index = 0;
            let new_sp = 
            Subproof { commands: Vec::new(), args: sp.args.clone(), context_id: sp.context_id.clone()};
            commands.push(ProofCommand::Subproof(new_sp));

            if let ProofCommand::Subproof(last_subproof) = commands.last_mut().unwrap() {
                commands = &mut last_subproof.commands;
            } else {
                panic!("Subproof expected.");
            }
            depth += 1;
            
            while let Some((d, i)) = next_premise  {
                if *d == depth {
                    commands.push(holeify_premise(iter.get_premise((*d, *i)).clone()));
                    new_premises.push((depth, new_premise_index));
                    new_premise_index += 1;
                    next_premise = premises_iter.next();
                }
            }

            // TODO: check that this handles the edge cases properly
            if j == subproof_stack.len() - 1 {
                commands.push(ProofCommand::Step(ProofStep { id: proof_step.id.clone(),
                     clause: proof_step.clause.clone(),
                      rule: proof_step.rule.clone(),
                       premises: new_premises.clone(),
                        args: proof_step.args.clone(),
                         discharge: proof_step.discharge.clone() }));
            }

            // DONE: make hole
            let penult = &sp.commands[sp.commands.len() - 1];
            if id != penult.id() {
                commands.push(holeify_premise(penult.clone()));
            }
            let ult = &sp.commands[sp.commands.len() - 2];
            if id != ult.id() {
            commands.push(holeify_premise(ult.clone()));
            }
        }
    }
        // println!("{:?}", new_proof);
        commands.push(ProofCommand::Step(
            ProofStep {clause: Vec::new(), 
                rule:"hole".to_string(), 
                premises :Vec::new(),
            discharge: Vec::new(),
        args: Vec::new(),
        id: proof.commands.last().unwrap().id().to_string() + "b"
    }));
        return new_proof;
    }
    else {
        panic!("Command to slice was not a step.");
    }
    

}

/* 

pub fn mini_slice2(proof: &Proof, id: &str, problem: &Problem) -> Option<(Proof, Problem)> {

    // Create a new proof with the same constant definitions but otherwise empty and a new problem with the same prelude
    let mut new_proof : Proof = Proof { constant_definitions: proof.constant_definitions.clone(), commands: Vec::new()};
    let mut new_problem : Problem = Problem { prelude: problem.prelude.clone(), premises: IndexSet::new()};

    let mut iter = proof.iter();
    let mut anchor_args_stack: Vec<&Vec<AnchorArg>> = Vec::new();
    let mut sliced_step: Option<&ProofCommand> = None;
    while let Some(command) = iter.next() {
        if command.id() == id {
            sliced_step = Some(command);
            break;
        }
        if let ProofCommand::Subproof(subproof) = command {
            anchor_args_stack.push(&subproof.args);
        }

        if iter.is_end_step() {
            anchor_args_stack.pop();
        }
    }

    if let Some(ProofCommand::Step(proof_step)) = sliced_step {

        let premises : Vec<&ProofCommand> = 
        proof_step.premises.iter().map(|(d, i)| iter.get_premise((*d, *i))).collect();

        for p in premises {
             match p {
                ProofCommand::Assume { id, term } => {
                    new_problem.premises.insert(term.clone());
                    new_proof.commands.push(ProofCommand::Assume { id: id.to_string(), term: term.clone() });
                },
                ProofCommand::Step(step) => {
                    new_proof.commands.push(
                        ProofCommand::Step(
                            ProofStep { rule: "hole".to_string(), premises: Vec::new(), ..step.clone() }));
                },
                _ => {},
            }
        }
        Some((new_proof, new_problem))
    }

    else {
        None
    }
}
    */