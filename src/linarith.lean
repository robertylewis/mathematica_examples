/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.core
import mathematica
import tactic.linarith

/-!
This demo shows how we can use Mathematica as a certificate oracle for mathlib's `linarith` tactic.
`linarith` implements a certificate checker, and it doesn't matter where this certificate comes from.
If the checker succeeds then we have a complete proof (with no new axioms).
-/

section
open native tactic tactic.mathematica mathematica linarith

/-- Auxiliary function that produces a string to pass to Mathematica. -/
meta def sum_for_var_i (l : list (ℕ × comp)) (i : ℕ) : string :=
let ls : list string := l.map $ λ ⟨hs, c⟩, to_string (c.coeffs.zfind i) ++ "* x" ++ to_string hs in
" + ".intercalate ls ++ " == 0"

/--
A `linarith.certificate_oracle` is a function `list_comp → ℕ → rb_map ℕ ℕ`.
Given a list of comparisons, it tries to find a coefficient for each comparison
such that summing together the linear combination of these comparisons
gives a proof of `0 < 0`.
-/
meta def mm_oracle : linarith.certificate_oracle :=
λ hs max_var,
let cstrs := (list.range max_var.succ).map (λ i, (sum_for_var_i hs.enum i)),
    cstrs := " && ".intercalate cstrs,
    nngs := (list.range hs.length).map $ λ i, "x" ++ to_string i ++ " >= 0",
    nngs := " && ".intercalate nngs,
    poss := hs.enum.filter_map $ λ ⟨i, c⟩,
      if c.str = ineq.lt then some ("x" ++ to_string i) else none,
    poss := " + ".intercalate poss ++ " > 0",
    vars := ", ".intercalate $ (list.range hs.length).map (λ i, "x" ++ to_string i),
    cmd := to_string $ format!"L = Part[#, 2] & /@ FindInstance[{cstrs} && {nngs} && {poss}, " ++ "{" ++ vars ++ "}, Rationals][[1]]; (LCM @@ Denominator@L)*L" in
do v ← execute_and_eval cmd,
   e ← pexpr_of_mmexpr trans_env.empty v,
   e ← to_expr e,
   e ← eval_expr (list ℕ) e,
   return $ rb_map.of_list e.enum

end

/- A simple example of `linarith` using our new oracle. -/
example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith {oracle := mm_oracle}

/- The `nlinarith` variant creates bigger problems,
where more efficient algorithms in Mathematica can shine. -/
example (u v x y A B : ℚ) : (0 < A) → (A ≤ 1) → (1 ≤ B)
→ (x ≤ B) → ( y ≤ B)
→ (0 ≤ u ) → (0 ≤ v )
→ (u < A) → ( v < A)
→ (u * y + v * x + u * v < 3 * A * B) :=
begin
  intros,
  nlinarith {oracle := mm_oracle}
 end

/- `linarith` works over arbitrary types with the right algebraic and order structure. -/
example {α : Type}
  [linear_ordered_field α]
  {a b c : α}
  (ha : a < 0)
  (hb : ¬b = 0)
  (hc' : c = 0)
  (h : (1 - a) * (b * b) ≤ 0)
  (hc : 0 ≤ 0)
  (this : -(a * -b * -b + b * -b + 0) = (1 - a) * (b * b))
  (h : (1 - a) * (b * b) ≤ 0) :
  0 < 1 - a :=
begin
  linarith {oracle := mm_oracle}
end