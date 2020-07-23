
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import mathematica
import tactic.core tactic.find tactic.norm_num
import data.real.pi
open expr tactic int

meta def pexpr_of_list_expr : list expr → pexpr 
| [] := ``([])
| (h::t) := ``(%%h::%%(pexpr_of_list_expr t) : list _)

meta def expr_of_list_expr : list expr → tactic expr :=
to_expr ∘ pexpr_of_list_expr

meta def dest_list_fst (e : expr) : tactic expr :=
do _::k::_ ← match_app_of e `list.cons, return k

meta def expr_list_of_list_expr : expr → tactic (list expr)
| (app (app (app (const `list.cons _) _) h) t) := 
do t' ← expr_list_of_list_expr t,
   return $ h :: t'
| (app (const `list.nil _) _) := return []
| _ := failed


meta def mk_local_lambdas : expr → tactic (list expr × expr)
| (expr.lam n bi d b) := do
  p ← mk_local' n bi d,
  (ps, r) ← mk_local_lambdas (expr.instantiate_var b p),
  return ((p :: ps), r)
| e := return ([], e)

meta def exists_to_lambda : expr → expr 
| (app (app (const `Exists _) _) (lam nm bi tp bod)) := lam nm bi tp (exists_to_lambda bod)
| a := a 

meta def find_sols : tactic unit :=
do lamd ← exists_to_lambda <$> target,
   (lcls, bod) ← mk_local_lambdas lamd,
   lcls' ← expr_of_list_expr lcls,
   sol ← mathematica.run_command_on_2_using 
      (λ s t, "Solve[ " ++ s ++ "// LeanForm // Activate, " ++  t ++" // LeanForm // Activate, Reals] // LUnrule")
        bod lcls' "poly.m",
   tp ← infer_type lcls.head,
   intes ← to_expr ``(%%sol : list (list %%tp)) >>= dest_list_fst >>= expr_list_of_list_expr,
   intes.mmap' existsi,
   `[norm_num]

lemma e1 : ∃ x y : ℤ, x*x*x-y=0 ∧ y-8=0 := by find_sols 

lemma e2 : ∃ r : ℝ, r+r = 3 := by find_sols

