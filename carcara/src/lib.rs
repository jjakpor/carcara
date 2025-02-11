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
use ast::printer::proof_to_string;
use ast::{pool, Operator, PrimitivePool, Problem, Proof, ProofCommand, ProofIter, ProofStep, Rc, Subproof, Term, TermPool};
use checker::{error::CheckerError, CheckerStatistics};
use parser::{ParserError, Position};
use core::{panic, slice};
use std::collections::{HashMap, HashSet};
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

    let mut prev_was_end: bool = false;
    while let Some(command) = iter.next() {
        if command.id() == id {
            sliced_step = Some(command);
            break;
        }
        if let ProofCommand::Subproof(subproof) = command {
            subproof_stack.push(&subproof);
        }

        if iter.is_end_step() {
            prev_was_end = true;
            continue;
        }

        if prev_was_end {
            subproof_stack.pop();
            prev_was_end = false;
        }
    }
    
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
        
        let mut premises = proof_step.premises.clone();
        premises.sort();

        let mut premises_iter= premises.iter();
        let mut next_premise: Option<&(usize, usize)> = premises_iter.next();

        

        let mut commands: &mut Vec<ProofCommand> = &mut new_proof.commands;

        let mut new_premises : Vec<(usize, usize)> = Vec::new();
        let mut new_premise_index: usize = 0;
        
        // next_premise = commands_at_depth(0, commands, next_premise, &mut new_premises, iter, premises_iter);
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
                 ..proof_step.clone() // Discharges could be wrong -- actually, I think this just returns {} because if not in subproof, there should be no discharges
                };
            commands.push(ProofCommand::Step(new_step));
        }
        else {
       
        let mut depth:usize = 0;
        /* I could make top-level "level 0" */
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

                // proof_step.discharge.iter().map(|(d, i)|);
                commands.push(ProofCommand::Step(ProofStep { id: proof_step.id.clone(),
                     clause: proof_step.clause.clone(),
                      rule: proof_step.rule.clone(),
                       premises: new_premises.clone(),
                        args: proof_step.args.clone(),
                         discharge: Vec::new()/* proof_step.discharge.clone() */ })); // TODO: add discharges properly
            }

            // DONE: make hole
            let penult = &sp.commands[sp.commands.len() - 1];
            if id != penult.id() {
                commands.push(holeify_premise(penult.clone()));
            }
            // TODO: add discharges
            let ult = &sp.commands[sp.commands.len() - 2];
            if id != ult.id() {
            commands.push(holeify_premise(ult.clone()));
            }
        }
    }
        
        // Add empty clause to end
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


fn extract_step(sliced_step: Option<&ProofCommand>) -> &ProofStep {
    match sliced_step {
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
    }
}

fn termify_clause(clause: &[Rc<Term>], pool: &mut PrimitivePool) -> Rc<Term> {
    if clause.is_empty() {
        pool.add(Term::new_bool(false))
    } else if clause.len() == 1 {
        clause[0].clone()
    } else {
        pool.add(Term::Op(Operator::Or, clause.to_vec()))
    }  
}

/**
 * clause: a clause
 * pool: The term pool to add the negations to
 * 
 * Returns: a vector containing the negation of each disjunct in a clause
 */
fn negation_conjuncts(clause: &[Rc<Term>], pool: &mut PrimitivePool) -> Vec<Rc<Term>> {
    let negs : Vec<Rc<Term>> = clause.iter().map(|t| pool.add(Term::Op(Operator::Not, [t.clone()].to_vec()))).collect();
    negs
}
/* 
problem: string (or should I add printing capacity)?
proof: Use data structure, then convert

*/

pub fn small_slice2(problem: &Problem, proof: &Proof, id: &str, pool: &mut PrimitivePool) -> (Proof, String, String) {
    use std::fmt::Write;

    struct Premise {
        termified: Rc<Term>,
        singleton: bool, // Cases considered are single and multiple, not empty,
        assumption_index: Option<(usize, usize)>,
        premise_index: Option<(usize, usize)>
    }

    let mut premise_map: HashMap<(usize, usize), Premise> = HashMap::new();

    let mut new_proof : Proof = Proof { constant_definitions: proof.constant_definitions.clone(), commands: Vec::new()};

    let mut iter = proof.iter();
    let mut sliced_step: Option<&ProofCommand> = None;

    while let Some(command) = iter.next() {
        if command.id() == id {
            sliced_step = Some(command);
            break;
        }
    }
    
    let proof_step = extract_step(sliced_step);


    for (i, premise) in proof_step.premises.iter().enumerate() {
        let premise_clause = iter.get_premise(*premise).clause();
        let termified = termify_clause(premise_clause, pool);
        premise_map.insert(*premise, Premise {termified: termified, singleton: premise_clause.len() == 1, assumption_index: None, premise_index: None});
    }

    // Add the negation of the goal
    let negated_goal = negation_conjuncts(&proof_step.clause, pool);
    let mut resolution_premises: Vec<(usize, usize)> = Vec::new();

    let negation_base_index = premise_map.len();

    for i  in 0..negated_goal.len() {
        resolution_premises.push((0, negation_base_index + i)); // If we do add a resolution step. I think last step of proof is special case
    }
    

    // Add termified premises as assumptions
    // Need to fix this to be deterministic order
    let mut processed_premises: HashSet<(usize, usize)> = HashSet::new();
    for premise in &proof_step.premises {
        if processed_premises.insert(*premise) {

            let entry_opt = premise_map.get_mut(premise);
            let entry = entry_opt.unwrap();
            let premise_command = iter.get_premise(*premise);
            new_proof.commands.push(ProofCommand::Assume { id: premise_command.id().to_string(), term: entry.termified.clone()});
            entry.assumption_index = Some((0, new_proof.commands.len() - 1));
            if entry.singleton {
                entry.premise_index = entry.assumption_index;
            }
        }
    }
   
    // Add negated goal as assumptions
    for (i, conjunct) in negated_goal.iter().enumerate() {
        new_proof.commands.push(ProofCommand::Assume { id: format!("n{}.{}", proof_step.id, i), term: conjunct.clone() })
    }
    
    for (premise, entry) in &mut premise_map {
        if !entry.singleton {
            let premise_command = iter.get_premise(*premise);
            let step = ProofStep {
                clause: premise_command.clause().to_vec(),
                rule: "or".to_string(),
                premises: [entry.assumption_index.unwrap()].to_vec(), 
                id: format!("{}'", premise_command.id()), 
                args: Vec::new(), discharge: Vec::new()
            };

            new_proof.commands.push(ProofCommand::Step(step));
            entry.premise_index = Some((0, new_proof.commands.len() - 1));
            
    }
    }

    let mut new_premises: Vec<(usize, usize)> = Vec::new();
    for premise in &proof_step.premises {

            // println!("Inserting premise {:?}", *premise);
        new_premises.push(premise_map.get(premise).unwrap().premise_index.unwrap());
        
        
    }
     
    let goal_step = ProofStep {id: proof_step.id.clone(), clause: proof_step.clause.clone(), rule: proof_step.rule.clone(), premises: new_premises, args: Vec::new(), discharge: Vec::new()};
    new_proof.commands.push(ProofCommand::Step(goal_step));
    resolution_premises.push((0, new_proof.commands.len() - 1));
    
    if proof_step.clause.len() != 0 {
        let final_step = ProofStep {id: "t.end".to_string(), clause: Vec::new(), premises: resolution_premises, rule: "resolution".to_string(), args: Vec::new(), discharge: Vec::new()};
        new_proof.commands.push(ProofCommand::Step(final_step));
    }
    
    let proof_string = proof_to_string(pool, &problem.prelude, &new_proof, false);

    let mut asserts = Vec::new();
    processed_premises.clear();
    for premise in &proof_step.premises {
        if processed_premises.insert(*premise) {
            asserts.push(premise_map.get(&premise).unwrap().termified.clone()); 
        }
    }
    for conjunct in negated_goal {
        asserts.push(conjunct);
    }

    let mut problem_string = String::new();
    write!(&mut problem_string, "{}", problem.prelude).unwrap();

    let mut bytes = Vec::new();
    ast::printer::write_asserts(pool, &problem.prelude, &mut bytes, &asserts, false);
    
    write!(&mut problem_string, "{}", String::from_utf8(bytes).unwrap()).unwrap();
    writeln!(&mut problem_string, "(check-sat)").unwrap();
    writeln!(&mut problem_string, "(exit)").unwrap();


    (new_proof, problem_string, proof_string)

    }
