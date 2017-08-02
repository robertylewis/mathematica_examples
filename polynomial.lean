
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import mathematica
open expr tactic int

meta def lam_bod : expr → tactic expr
| (lam nm bi tp bd) :=
  do head_beta $ app (lam nm bi tp bd) (local_const nm nm bi tp)
| e := return e

meta def lam_bod_rec : expr → tactic expr
| (lam nm bi tp bd) := lam_bod (lam nm bi tp bd) >>= lam_bod_rec
| e := return e

meta def expr_of_list_expr : list expr → tactic expr
| [] := to_expr ```([])
| (h :: t) := do t' ← expr_of_list_expr t, to_expr ```(%%h :: %%t')

meta def dest_list_fst (e : expr) : tactic expr :=
do l ← match_app_of e `list.cons,
   match list.nth l 1 with
   | some k := return k
   | none := failed
   end

meta def dest_list_snd (e : expr) : tactic (expr × expr) := 
do l ← match_app_of e `list.cons,
   match (list.nth l 1, list.nth l 2) with
   | (some k1, some l') := do k2 ← dest_list_fst l', return (k1, k2)
   | _ := failed
   end

meta def count_poly_vars : expr → nat
| (lam _ _ _ bd) := count_poly_vars bd + 1
| _ := 0

meta def get_poly_vars : expr → list expr
| (lam nm bi tp bd) := local_const nm nm bi tp :: get_poly_vars bd
| _ := []

meta def expr_list_of_list_expr : expr → tactic (list expr)
| (app (app (app (const `list.cons _) _) h) t) := 
do t' ← expr_list_of_list_expr t,
   return $ h :: t'
| (app (const `list.nil _) _) := return []
| _ := failed

meta def fold_apps : expr → list expr → expr
| e [] := e
| e (h :: t) := fold_apps (app e h) t

meta def multi_exact : list expr → tactic unit
| [] := done
| (t :: ts) := exact t >> multi_exact ts

-- returns an expr k encoding a list ks and a list of proofs ps such that ps[i] proves l[i](ks) = 0
meta def solve_polys : list expr → tactic (expr × list expr)
| [] := fail "solve_polys failed, no functions given"
| (h :: t) := 
  let vs' := get_poly_vars h in
  if bnot (list.all (h::t) (λ p, if count_poly_vars p = count_poly_vars h then tt else ff)) 
     then fail "solve_polys failed, functions have different arities"
  else 
  do l' ← monad.mapm lam_bod_rec (h::t),
     conj ← monad.foldl (λ e1 e2, to_expr ```(%%e1 ∧ (%%e2 = 0))) (const `true []) l',
     vs ← expr_of_list_expr vs',
     sol ← mathematica.run_command_on_2_using 
      (λ s t, "Solve[ " ++ s ++ "// LeanForm // Activate, " ++  t ++" // LeanForm // Activate, Reals] // LUnrule")
        conj vs "E:\\Dropbox\\lean\\mathematica_examples\\poly.m", --"~/lean/lean/extras/mathematica/poly.m",
     tp ← infer_type $ list.head vs',
     r ← to_expr ```((%%sol : list (list %%tp))),
     fstsol ← dest_list_fst r,
     intes ← expr_list_of_list_expr fstsol,
     apps ← monad.mapm head_beta $ list.map ((λ e, fold_apps e intes)) (h::t),
     zrprs ← monad.mapm (λ e, do e' ← norm_num e, return e'.2) apps,
     return (fstsol, zrprs)

meta def strip_ex : expr → expr 
| (app (app (const `Exists _) _) (lam _ _ _ bod)) := strip_ex bod
| a := a

def e1 : ∃ x y : ℤ, x*x*x-y=0 ∧ y-8=0 := by
do f ← to_expr ```(λ x y : ℤ, x*x*x-y),
   g ← to_expr ```(λ x y : ℤ, y-8),
   (_, prs) ← solve_polys [f, g],
   constructor, constructor, constructor,
   multi_exact prs
