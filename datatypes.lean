/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import init.meta.mathematica
constant real : Type
notation `ℝ` := real
constant rof : linear_ordered_field ℝ
attribute [instance] rof
constants (sin cos tan : ℝ → ℝ) (pi : ℝ)
def {u} npow {α : Type u} [has_mul α] [has_one α] : α → ℕ → α
| r 0 := 1
| r (n+1) := r*npow r n
infix `^` := npow

@[simp] lemma rpow_zero (r : ℝ) : r^0 = 1 := rfl
@[simp] lemma rpow_succ (r : ℝ) (n : ℕ) : r^(n+1) = r*r^n := rfl

lemma sq_nonneg {α : Type} [linear_ordered_ring α] (a : α) : a^2 ≥ 0 := 
begin
unfold npow, rw mul_one, apply mul_self_nonneg
end

section
open mathematica
@[sym_to_pexpr]
meta def pow_to_pexpr : sym_trans_pexpr_rule :=
⟨"Power", `(npow)⟩
end 

@[instance] def {u} inhabited_of_has_zero {α : Type u} [has_zero α] : inhabited α := ⟨0⟩ -- works

open tactic
meta def mk_inhabitant_using (A : expr) (t : tactic unit) : tactic expr :=
do m ← mk_meta_var A,
   gs ← get_goals,
   set_goals [m],
   t,
   n ← num_goals,
   if n > 0 then fail "mk_inhabitant_using failed" else do
   r ← instantiate_mvars m,
   set_goals gs,
   return r

meta definition eq_by_simp (e1 e2 : expr) : tactic expr := 
do gl ← mk_app `eq [e1, e2],
   mk_inhabitant_using gl simp <|> fail "unable to simplify"
