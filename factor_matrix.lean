/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import .bquant .datatypes
open expr tactic


@[reducible]
def {u} ith {α : Type u} [inhabited α] (l : list α) (i : ℕ) : α :=
match l^.nth i with
| some a := a
| none   := default α
end

def {u} transpose_list {α : Type u} [inhabited α] (m : list (list α)) : list (list α) :=
list.map (λ i, m^.map (λ l, ith l i)) (native.upto (ith m 0)^.length)

def {u} dot_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] : list α → list α → α
| [a] [b] := a*b
| (h1::t1) (h2::t2) := h1*h2 + dot_lists t1 t2
| _ _ := 0

def {u} mul_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] [inhabited α]
       (m1 m2 : list (list α))  : list (list α) :=
list.map (λ i, (list.map (λ j, dot_lists (ith m1 i) (ith (transpose_list m2) j)) 
         (native.upto (ith m1 0)^.length))) (native.upto m1^.length)
   
infix `**`:50 := mul_lists

@[reducible]
def {u} is_lower_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i < m^.length, ∀ j < (ith m i)^.length, i < j → ith (ith m i) j = 0

@[reducible]
def {u} is_upper_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i < m^.length, ∀ j < (ith m i)^.length, i > j → ith (ith m i) j = 0

meta def dec_triv_tac : tactic unit :=
do t ← target,
   to_expr ```(dec_trivial : %%t) >>= apply

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
   lhs ← to_expr ```(ith %%m2 0), rhs ← to_expr ```(ith %%m2 1),
   existsi lhs, existsi rhs,
   split, dec_triv_tac, split, dec_triv_tac, reflexivity

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u ∧ mul_lists l u = [[(1 : ℤ), 2], [3, 4]] := 
by lu_tac

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u
             ∧ l ** u = [[1, 2, 3], [1, 4, 9], [1, 8, 27]] := 
by lu_tac
