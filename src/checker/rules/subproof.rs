use super::{get_single_term_from_command, to_option, RuleArgs};
use crate::ast::*;
use std::collections::HashSet;

pub fn bind(
    RuleArgs {
        conclusion,
        pool,
        context,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(subproof_commands.len() >= 2 && conclusion.len() == 1);

    // The last command in the subproof is the one we are currently checking, so we look at the one
    // before that
    let previous_command = &subproof_commands[subproof_commands.len() - 2];
    let (phi, phi_prime) =
        match_term!((= p q) = get_single_term_from_command(previous_command)?, RETURN_RCS)?;

    let (left, right) = match_term!((= l r) = conclusion[0])?;
    let ((l_bindings, left), (r_bindings, right)) = match (left, right) {
        // While the documentation indicates this rule is only called with "forall" quantifiers, in
        // some of the tests examples it is also called with the "exists" quantifier
        (Term::Quant(_, l_binds, l_term), Term::Quant(_, r_binds, r_term)) => {
            ((l_binds, l_term.as_ref()), (r_binds, r_term.as_ref()))
        }
        _ => return None,
    };
    let l_bindings: HashSet<_> = l_bindings.iter().map(|(var, _)| var.as_str()).collect();
    let r_bindings: HashSet<_> = r_bindings.iter().map(|(var, _)| var.as_str()).collect();

    // The terms in the quantifiers must be phi and phi'
    rassert!(left == phi.as_ref() && right == phi_prime.as_ref());

    // None of the bindings in the right side can appear as free variables in phi
    let free_vars = pool.free_vars(phi);
    rassert!(r_bindings
        .difference(&l_bindings)
        .all(|&y| !free_vars.contains(y)));

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let context = context.last()?;

    // The quantifier binders must be the xs and ys of the context substitutions
    let (xs, ys): (HashSet<_>, HashSet<_>) = context
        .substitutions
        .iter()
        // We skip terms which are not simply variables
        .filter_map(|(x, y)| Some((x.try_as_var()?, y.try_as_var()?)))
        .chain(
            // Sometimes, the context bindings also appear as bindings in the quantifiers, so we
            // include them in the "xs" and "ys"
            context
                .bindings
                .iter()
                .map(|(var, _)| (var.as_str(), var.as_str())),
        )
        .unzip();
    to_option(
        l_bindings.len() == r_bindings.len()
            && l_bindings.is_subset(&xs)
            && r_bindings.is_subset(&ys),
    )
}

pub fn r#let(
    RuleArgs {
        conclusion,
        context,
        premises,
        pool,
        subproof_commands,
        ..
    }: RuleArgs,
) -> Option<()> {
    rassert!(conclusion.len() == 1);

    // Since we are closing a subproof, we only care about the substitutions that were introduced
    // in it
    let substitutions = &context.last()?.substitutions;

    let (let_term, u_prime) = match_term!((= l u) = conclusion[0], RETURN_RCS)?;
    let (let_bindigns, u) = match let_term.as_ref() {
        Term::Let(b, t) => (b, t),
        _ => return None,
    };

    // The u and u' in the conclusion must match the u and u' in the previous command in the
    // subproof
    let previous_term =
        get_single_term_from_command(&subproof_commands[subproof_commands.len() - 2])?;
    let (previous_u, previous_u_prime) = match_term!((= u u_prime) = previous_term, RETURN_RCS)?;
    rassert!(u == previous_u && u_prime == previous_u_prime);

    rassert!(let_bindigns.len() == substitutions.len());

    let mut premises = premises.iter();
    for (x, t) in let_bindigns {
        let x_term = terminal!(var x; pool.add_term(t.sort().clone()));
        let s = substitutions.get(&pool.add_term(x_term))?;
        if s != t {
            let premise = premises.next()?;
            let premise_equality = match_term!((= a b) = get_single_term_from_command(premise)?)?;
            rassert!(premise_equality == (s, t) || premise_equality == (t, s));
        }
    }
    to_option(premises.next().is_none())
}

#[cfg(test)]
mod tests {
    #[test]
    fn bind() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun r () Bool)
                (declare-fun s () Bool)
                (declare-fun y () Real)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": true,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust_me)
                (step t1 (cl (= (forall ((x1 Real) (x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": true,
            }
            "Examples with binding arguments" {
                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real) (z Real)) p)
                    (forall ((y Real) (z Real)) q))) :rule bind)": true,
            }
            "y_i appears in phi as a free variable" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) (= y x))
                    (forall ((y Real)) (= y y)))) :rule bind)": false,

                "(anchor :step t1 :args ((z Real) (:= (x Real) y)))
                (step t1.t1 (cl (= (= y x) (= y y))) :rule trust_me)
                (step t1 (cl (= (forall ((z Real) (x Real)) (= y z))
                    (forall ((z Real) (y Real)) (= y z)))) :rule bind)": false,
            }
            "Terms in conclusion clause don't match terms in previous command" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1.t2 (cl (= r s)) :rule trust_me) ; This step shouldn't be here!
                (step t1 (cl (= (forall ((x Real)) p) (forall ((y Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((x Real)) q) (forall ((y Real)) p))) :rule bind)": false,
            }
            "Context substitutions don't match quantifier bindings" {
                "(anchor :step t1 :args ((:= (x Real) y)))
                (step t1.t1 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (forall ((y Real)) p) (forall ((x Real)) q))) :rule bind)": false,

                "(anchor :step t1 :args ((:= (x1 Real) y1) (:= (x2 Real) y2)))
                (step t1.t1 (cl (= (= x1 x2) (= y1 y2))) :rule trust_me)
                (step t1 (cl (= (forall ((x2 Real)) (= x1 x2))
                    (forall ((y1 Real) (y2 Real)) (= y1 y2)))) :rule bind)": false,
            }
        }
    }

    #[test]
    fn r#let() {
        test_cases! {
            definitions = "
                (declare-fun p () Bool)
                (declare-fun q () Bool)
                (declare-fun i () Int)
                (declare-fun j () Int)
                (declare-fun k () Int)
            ",
            "Simple working examples" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": true,

                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= k z)) :rule trust_me)
                (step t1.t3 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1 t1.t2))": true,
            }
            "Premise equalities may be flipped" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= x i)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": true,
            }
            "Wrong number of premises" {
                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1))": false,

                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= y y)) :rule trust_me)
                (step t1.t3 (cl (= k z)) :rule trust_me)
                (step t1.t4 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b y) (c k)) p) q))
                    :rule let :premises (t1.t1 t1.t2))": false,
            }
            "Number of bindings is `let` term doesn't match number of substitutions in context" {
                "(anchor :step t1 :args (
                    (:= (a Int) x) (:= (b Int) y) (:= (c Int) z)
                ))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= j y)) :rule trust_me)
                (step t1.t3 (cl (= p q)) :rule trust_me)
                (step t1 (cl (= (let ((a i) (b j)) p) q)) :rule let :premises (t1.t1 t1.t2))": false,
            }
            "u and u' don't match equality in previous command" {
                "(anchor :step t1 :args ((:= (a Int) x)))
                (step t1.t1 (cl (= i x)) :rule trust_me)
                (step t1.t2 (cl (= p (= i j))) :rule trust_me)
                (step t1 (cl (= (let ((a i)) p) q)) :rule let :premises (t1.t1))": false,
            }
        }
    }
}
