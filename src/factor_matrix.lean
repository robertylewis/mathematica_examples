/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import  datatypes mathematica
open expr tactic

/-!
In this demo we use a brief computable representation of matrices
to verify instances of LU decomposition done by Mathematica.

With some extra glue, this could operate on mathlib's matrix representation.

The LU algorithm is only specified up to permutation, which we do not address here,
so this is only correct for simple cases.
-/

def {u} dot_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] : list α → list α → α
| [a] [b] := a*b
| (h1::t1) (h2::t2) := h1*h2 + dot_lists t1 t2
| _ _ := 0

def {u} mul_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] [inhabited α]
       (m1 m2 : list (list α))  : list (list α) :=
list.map (λ i, (list.map (λ j, dot_lists (list.inth m1 i) (list.inth (list.transpose m2) j))
         (list.range (list.inth m1 0).length))) (list.range m1.length)

infix `**`:50 := mul_lists

local attribute [instance]
def inhabited_of_has_zero {α} [has_zero α] : inhabited α := ⟨0⟩

@[reducible]
def {u} is_lower_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i < m^.length, ∀ j < (list.inth m i)^.length, i < j → list.inth (list.inth m i) j = 0

@[reducible]
def {u} is_upper_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i < m^.length, ∀ j < (list.inth m i)^.length, i > j → list.inth (list.inth m i) j = 0


meta def lu_tac : tactic unit :=
do t ← target,
   (lam _ _ _ bd) ← return $ app_arg t,
   (lam _ _ _ ande) ← return $ app_arg bd,
   `(%%_ ∧ %%_ ∧ %%_ = %%e) ← return $ ande,
   tp ← infer_type e,
   m ← mathematica.run_command_on_using
      (λ e, e ++ " // LeanForm // Activate // LUDecomp")
       e
      "matrix_factor.m",
   m2 ← to_expr ```((%%m : list %%tp)),
   lhs ← to_expr ```(list.inth %%m2 0), rhs ← to_expr ```(list.inth %%m2 1),
   existsi lhs, existsi rhs,
   `[refine ⟨dec_trivial, dec_trivial, _⟩], reflexivity

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u
             ∧ l ** u = [[(1 : ℤ), 2], [3, 4]] :=
by lu_tac

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u
             ∧ l ** u = [[1, 2, 3], [1, 4, 9], [1, 8, 27]] :=
by lu_tac
