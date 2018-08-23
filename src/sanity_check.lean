/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import datatypes mathematica
open  tactic native.rb_set tactic.mathematica
section
open expr native
meta def find_locals : expr → expr_set :=
λ e, e^.fold (mk_expr_set) (λ e' _ l, if is_local_constant e' then l^.insert e' else l)

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

meta def sanity_check' (xs : list name) : tactic unit :=
do hyps ← local_context,
   phyp ← monad.filter is_proof hyps,
   hypt ← monad.mapm infer_type phyp,
   xs' ← monad.mapm get_local xs,
   sanity_check_aux hypt xs'

meta def sanity_check : tactic unit :=
do hyps ← local_context, 
   phyp ← monad.filter is_proof hyps,
   hypt ← monad.mapm infer_type phyp, 
   t ← target,
   vars ← return $ rb_map.keys $ list.foldr (λ e s, rb_map.union s (find_locals e)) mk_expr_set (t::hypt),
   sanity_check_aux hypt vars


example (x : ℤ) (h : x < 0) : x < 0 :=
by sanity_check; admit

example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0)
 : x = 0 :=
by sanity_check; admit

example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0) (h3 : -_root_.pi < x ∧ x < pi)
 : x = 0 :=
by sanity_check; admit 

end
