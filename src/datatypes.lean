
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import mathematica data.real.basic tactic.ring
open native 

constants (sin cos tan : ℝ → ℝ) (pi : ℝ)

/-def {u} npow {α : Type u} [has_mul α] [has_one α] : α → ℕ → α
| r 0 := 1
| r (n+1) := r*npow r n
local infix `^` := npow-/

--noncomputable instance real.has_pow : has_pow ℝ ℕ := ⟨npow⟩ 

--@[simp] lemma rpow_zero (r : ℝ) : r^0 = 1 := rfl
--@[simp] lemma rpow_succ (r : ℝ) (n : ℕ) : r^(n+1) = r*r^n := rfl

lemma sq_nonneg {α : Type*} [linear_ordered_ring α] (a : α) : a^2 ≥ 0 := 
show a * (a * 1) ≥ 0, by rw mul_one; apply mul_self_nonneg

section
open mathematica
@[sym_to_pexpr]
meta def pow_to_pexpr : sym_trans_pexpr_rule :=
⟨"Power", ```(has_pow.pow)⟩
end 

@[instance] def {u} inhabited_of_has_zero {α : Type u} [has_zero α] : inhabited α := ⟨0⟩ -- works

open tactic
meta def mk_inhabitant_using (A : expr) (t : tactic unit) : tactic expr :=
do m ← mk_meta_var A,
   gs ← get_goals,
   set_goals [m],
   t,
   n ← num_goals,
   if n > 0 then trace_state >> fail "mk_inhabitant_using failed" else do
   r ← instantiate_mvars m,
   set_goals gs,
   return r

meta definition eq_by_simp (e1 e2 : expr) : tactic expr := 
do gl ← mk_app `eq [e1, e2],
   --mk_inhabitant_using gl `[ring] <|> (fail "unable to simplify")
   prod.snd <$> solve_aux gl (`[ring] >> done) <|> (fail "unable to simplify")

meta def rb_map.union {key data : Type} (m1 m2 : rb_map key data) : rb_map key data :=
m1^.fold m2 (λ k d m, m^.insert k d)
