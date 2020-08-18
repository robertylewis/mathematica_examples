/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import datatypes mathematica
import analysis.special_functions.trigonometric

/-!
`sanity_check` tries to find an assignment to the free variables that appear in the context
such that all hypotheses are true but the target is false.
In this case, the tactic will fail, since the target is not provable.
-/

open  tactic native tactic.mathematica
section
open expr native

/-- An auxiliary function that finds all local constants in an expression. -/
meta def find_locals : expr → expr_set :=
λ e, e^.fold (mk_expr_set) (λ e' _ l, if is_local_constant e' then l^.insert e' else l)

/-- Constructs the proposition to send to Mathematica and calls `FindInstance`. -/
meta def sanity_check_aux (hs : list expr) (xs : list expr) : tactic unit :=
do t ← target, nt ← to_expr ```(¬ %%t),
   hs'' ← monad.foldl (λ a b, to_expr ```(%%a ∧ %%b)) `(true) (nt::hs),
   l ← run_command_on_list
      (λ e, "With[{ls=Map[Activate[LeanForm[#]]&,"++e++"]}, Length[FindInstance[ls[[1]], Drop[ls, 1]]]]")
      (hs''::xs),
   n ← to_expr ```(%%l : ℕ) >>= eval_expr ℕ,
   if n > 0 then
      fail "sanity check: the negation of the goal is consistent with hypotheses"
   else skip

/-- The main `sanity_check` tactic. -/
meta def tactic.interactive.sanity_check : tactic unit :=
do hyps ← local_context,
   phyp ← monad.filter is_proof hyps,
   hypt ← monad.mapm infer_type phyp,
   t ← target,
   vars ← return $ rb_map.keys $ list.foldr (λ e s, rb_set.union s (find_locals e)) mk_expr_set (t::hypt),
   sanity_check_aux hypt vars
end

open real

/-- This goal is plausible, so the tactic succeeds. -/
example (x : ℤ) (h : x < 0) : x < 0 :=
by sanity_check; admit

/--
This goal is not plausible: Mathematica finds an `x` such that
* `sin x = 0`
* `cos x > 0`
* `x ≠ 0`
so the tactic fails. -/
example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0) : x = 0 :=
by sanity_check; admit

/--
Adding an extra condition to the above example,
the goal becomes plausible,
so the tactic succeeds.
-/
example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0) (h3 : -pi < x ∧ x < pi) : x = 0 :=
by sanity_check; admit

end
