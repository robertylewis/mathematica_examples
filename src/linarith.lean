import tactic.core
import mathematica
import tactic.linarith 


section 
open native tactic tactic.mathematica mathematica linarith 

meta def sum_for_var_i (l : list (ℕ × comp)) (i : ℕ) : string :=
let ls : list string := l.map $ λ ⟨hs, c⟩, to_string (c.coeffs.zfind i) ++ "* x" ++ to_string hs in
" + ".intercalate ls ++ " == 0"

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


example (x y z : ℚ) (h1 : 2*x  < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : false :=
by linarith {oracle := mm_oracle} 

example (u v x y A B : ℚ) : (0 < A) → (A ≤ 1) → (1 ≤ B)
→ (x ≤ B) → ( y ≤ B)
→ (0 ≤ u ) → (0 ≤ v )
→ (u < A) → ( v < A)
→ (u * y + v * x + u * v < 3 * A * B) :=
begin
  intros,
  nlinarith {oracle := mm_oracle}
 end 

example {α : Type} (_inst : Π (a : Prop), decidable a) 
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