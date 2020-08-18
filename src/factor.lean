/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import mathematica
import datatypes
import data.real.basic
open expr tactic nat mmexpr

/--
`factor e nm` takes an expression representing a polynomial, like `` `(x^2-1)``.
It gets translated to Mathematica, factored, and reconstructed.
The `ring` tactic is called to prove that the input `e` is equal to the result,
and this equality is added to the context as a hypothesis with name `nm`.
-/
meta def factor (e : expr) (nm : option name) : tactic unit :=
do t ← mathematica.run_command_on (λ s, s ++" // LeanForm // Activate // Factor") e,
   ts ← to_expr t,
   pf ← eq_by_ring e ts,
   match nm with
   | some n := note n none pf >> skip
   | none := do n ← get_unused_name `h none, note n none pf, skip
   end


namespace tactic
namespace interactive

setup_tactic_parser

meta def factor (e : parse texpr) (nm : parse using_ident) : tactic unit :=
do e' ← i_to_expr e,
   _root_.factor e' nm

end interactive
end tactic

/-
In these first two examples we prove that polynomials are nonnegative
by factoring them into squares.
-/
example (x : ℝ) : 1 - 2*x + 3*x^2 - 2*x^3 + x^4 ≥ 0 :=
begin
 factor  1 - 2*x + 3*x^2 - 2*x^3 + x^4  using h,
 rewrite h,
 apply pow_two_nonneg
end

example (x : ℝ) : x^2-2*x+1 ≥ 0 :=
begin
factor x^2-2*x+1 using q,
rewrite q,
apply pow_two_nonneg
end

/-
Here we factor a larger polynomial and trace the state afterward:

x y : ℝ,
h :
  x ^ 10 - y ^ 10 =
    (x + (-1) * y) * (x + y) * (x ^ 4 + (-1) * x ^ 3 * y + x ^ 2 * y ^ 2 + (-1) * x * y ^ 3 + y ^ 4) *
      (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4)
⊢ true
-/
example (x y : ℝ) : true :=
begin
factor (x^10-y^10),
trace_state,
triv
end
