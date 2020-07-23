
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import mathematica
import tactic.core tactic.find tactic.norm_num
import data.real.pi
open expr tactic int

meta def expr_of_list_expr : list expr → tactic expr
| [] := to_expr ```([])
| (h :: t) := do t' ← expr_of_list_expr t, to_expr ```(%%h :: %%t')

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
  trace sol,
   tp ← infer_type lcls.head,
   trace tp,
   to_expr ``(%%sol : list (list %%tp)) >>= dest_list_fst >>= expr_list_of_list_expr >>= trace,
   intes ← to_expr ``(%%sol : list (list %%tp)) >>= dest_list_fst >>= expr_list_of_list_expr,
   intes.mmap' existsi,
   `[simp; norm_num]

-- lemma e1 : ∃ x y : ℤ, x*x*x-y=0 ∧ y-8=0 := by find_sols 
set_option trace.mathematica true 
lemma e2 : ∃ r : ℝ, r+r = 3 := by find_sols

@[sym_to_pexpr]
meta def pi_to_expr : mathematica.sym_trans_pexpr_rule :=
⟨"Pi", ``(real.pi)⟩


lemma e3 : ∃ r : ℝ, 1 < r ∧ r < 4 ∧ real.sin r = 1 := by try_for 1000 {find_sols}