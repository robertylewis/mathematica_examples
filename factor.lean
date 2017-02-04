
/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import init.meta.mathematica

open expr tactic nat


meta definition eq_by_simp (e1 e2 : expr) : tactic expr := do
 gl ← mk_app `eq [e1, e2],
 nm ← mk_fresh_name,
 assert nm gl,
 simp,
 tactic_orelse
  (get_local nm)
  (fail "unable to simplify")

theorem foo (a b c : ℕ) : a * (b + c) = a * b + a * c := sorry
theorem foo2 (a b c : ℕ) : (b + c) * a = b * a + c * a := sorry

attribute [simp] foo foo2

instance : add_group ℕ := sorry

def npow (x : ℕ) : ℕ → ℕ
| 0 := 1
| (k+1) := x*(npow k)

infix `^` := npow
open mmexpr

@[simp] lemma pow_zero (x : ℕ) : x^0=1 := rfl
@[simp] lemma pow_succ (x n : ℕ) : x^(n+1)=x*(x^n) := rfl
@[simp] lemma nn1 : (-1 : ℕ) * -1 = 1 := sorry
@[simp] lemma n2a (x : ℕ) : x*(-1) + x*(-1) = -(x*2) := sorry
@[simp] lemma stn (a x : ℕ) : a - x = a + (-x) := sorry

meta instance mmexpr_has_to_pexpr_power (b e : mmexpr) [mmexpr_has_to_pexpr b] [mmexpr_has_to_pexpr e] :
         mmexpr_has_to_pexpr (app (sym "Power") [b, e]) :=
⟨_, `(%%(pexpr_of_mmexpr b) ^ %%(pexpr_of_mmexpr e))⟩


example (x : ℕ) : true :=
by do
--x ← get_local `x,
e ← to_expr  `(x*x - 2*x + 1),
t ← run_mm_command_on_expr (λ s, s ++" // LeanForm // Activate // Factor // ArithConvert") e,
ts ← to_expr t,
pr ← eq_by_simp e ts,
trace ts,
to_expr `(trivial) >>= apply
