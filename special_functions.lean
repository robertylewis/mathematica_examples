/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import mathematica .datatypes
open tactic

/-constant real : Type
notation `ℝ` := real
constant rof : linear_ordered_field ℝ
attribute [instance] rof-/

constant deriv : (ℝ → ℝ) → (ℝ → ℝ)

constant BesselJ (n : ℝ) (z : ℝ) : ℝ

axiom BesselJ_def (n : ℝ) (z : ℝ) : z*z*(deriv (deriv (BesselJ n)) z) + z*(deriv (BesselJ n) z) + (z*z-n*n)*(BesselJ n z) = 0

section
open mathematica

@[sym_to_pexpr]
meta def BesselJ_trans : sym_trans_pexpr_rule :=
⟨"BesselJ", ```(BesselJ)⟩

@[sym_to_expr]
meta def pi_trans : sym_trans_expr_rule :=
⟨"Pi", `(pi)⟩

@[sym_to_pexpr]
meta def sin_trans : sym_trans_pexpr_rule :=
⟨"Sin", ```(sin)⟩

run_cmd mathematica.load_file "~/Dropbox/lean/mathematica_examples/bessel.m"

end

meta def make_bessel_fn_eq (e : expr) : tactic (expr × expr) := do
 pe ← mathematica.run_command_on (λ t, t ++ "// LeanForm // Activate // FullSimplify") e,
 val ← to_expr ```(%%pe : ℝ),
 tp ← to_expr ```(%%e = %%val),
 nm ← new_aux_decl_name,
 let nm' := `mathematica_axiom ++ nm,
 l ← local_context,
 l' ← mfilter (kdepends_on tp) l,
 gls ← get_goals,
 m ← mk_meta_var tp,
 set_goals [m],
 generalizes l',
 tp' ← target,
 set_goals gls,
 let dcl := declaration.ax nm' [] tp',
 add_decl dcl,
 prf ← mk_const nm',
 return (val, prf)

meta def approx (e q : expr) : tactic (expr × expr) :=
do pe ← mathematica.run_command_on_2 
     (λ e q, "Rationalize[" ++ e ++ " // LeanForm // Activate // N, " ++ q ++ "// LeanForm // Activate]") 
     e q,
   val ← to_expr ```(%%pe : ℝ),
   (lb, _) ← to_expr ```(%%val - %%q) >>= norm_num,
   (ub, _) ← to_expr ```(%%val + %%q) >>= norm_num,
   tgt ← to_expr ```(%%lb < %%e ∧ %%e < %%ub),
   nm ← new_aux_decl_name,
   let nm' := `approx_axiom ++ nm,
   let dcl := declaration.ax nm' [] tgt,
   add_decl dcl,
   prf ← mk_const nm',
   return (val, prf)

namespace tactic
namespace interactive
section
open expr lean lean.parser interactive.types interactive

meta def approx (e : parse qexpr) (q : parse qexpr) : itactic := 
do e' ← i_to_expr e,
   q' ← i_to_expr q,
   (_, prf) ← _root_.approx e' q',
   n ← get_unused_name `approx none,
   tactic.note n none prf, skip

end
end interactive
end tactic


variable x : ℝ

def f1 : x*BesselJ 2 x + x*BesselJ 0 x = 2*BesselJ 1 x := by do
 (t, _) ← target >>= match_eq,
 (_, prf) ← make_bessel_fn_eq t,
 apply prf


#check mathematica_axiom.f1._aux_1

--run_cmd approx ```(100*BesselJ 2 0.52) ```(0.001 : ℝ) >>= (λ e, infer_type e.2) >>= trace

theorem apr : true :=
begin
approx (100*BesselJ 2 0.52) (0.00001 : ℝ),
trace_state,
triv
end

#print axioms 

--run_cmd mathematica.run_command_on (λ t, "Rationalize[" ++t ++ "//LeanForm // Activate // N, .01]") ```(100*BesselJ 2 0.52) >>= λ t, to_expr `((%%t : ℝ)) >>= trace 

#exit
--run_cmd mathematica.run_command_on (λ t, t ++ "//LeanForm//Activate") ```(2+2) >>= λ t, to_expr `((%%t : ℕ)) >>= trace

run_cmd mathematica.run_command_on_using (λ t, t ++ "// LeanForm // Activate") ```(BesselJ (1/2) x) "~/Dropbox/lean/mathematica_examples/bessel.m" >>= λ t, to_expr `((%%t : ℝ)) >>= trace



run_cmd mathematica.run_command_on_using (λ t, t ++ "// LeanForm // Activate // FullSimplify") ```(x*BesselJ 2 x + x*BesselJ 0 x) "~/Dropbox/lean/mathematica_examples/bessel.m" >>= λ t, to_expr `((%%t : ℝ)) >>= trace
⟩
