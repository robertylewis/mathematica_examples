import tactic.core
import mathematica
import data.complex.exponential
import tactic.interactive_expr

reserve notation `begin_mm_block`
reserve notation `end_mm_block`
reserve notation `as`
reserve notation `image`
reserve notation `unfolding`

section
open widget


#check component

/-- This is a helper that should really be in core. You can't use component.stateless on
tactic_state because you can't decide equality on them. -/

meta def component.stateless' {π α} (view : π → list (html α)) : component π α :=
component.with_should_update (λ _ _, tt) $ component.pure view /- component.mk
  α
  unit
  (λ _ _, ())
  (λ _ _ a, (⟨⟩, some a))
  (λ p _, view p )
  (λ _ _, ff) -- ⟵ this means that the component should not attempt to check that
              -- the props are equal and just always update -/

meta def url_component (src : string) : component tactic_state empty :=
component.stateless' $ λ ts,
  [h "h1" [] ["Mathematica output"],
    h "img" [attr.val "src" src] []
  ]

meta def expr_widget (src : expr) : tactic (component tactic_state empty) :=
do s ← tactic.pp src,
  return $ component.stateless' $ λ ts,
    [h "h1" [] ["Mathematica output"],
    h "p" [] [s]
  ]

end

section
setup_tactic_parser
open tactic

meta inductive command_comp
| cmd : string → command_comp
| antiquot : expr → command_comp

meta def command_comp.to_string : command_comp → string
| (command_comp.cmd s) := "command: " ++ s
| (command_comp.antiquot s) := "antiquot: " ++ to_string s

meta instance : has_repr command_comp :=
⟨command_comp.to_string⟩

meta def parse_string_component : lean.parser string :=
do s ← parser.pexpr 10000,
   to_expr s >>= ↑(eval_expr string)

meta def parse_antiquote : lean.parser pexpr :=
parser.pexpr 10000

meta def parse_component : lean.parser command_comp :=
do pe ← parser.pexpr 10000,
   e ← to_expr pe,
   tpe ← infer_type e,
   if tpe = `(string) then do  s ← eval_expr' string e, return $ command_comp.cmd s
   else return $ command_comp.antiquot e

meta def parse_cmd_list_aux : lean.parser $ list command_comp :=
tk ";" >> return  [] <|>
do c ← parse_component, cs ← parse_cmd_list_aux, return (c::cs)

meta def parse_cmd_list : lean.parser $ bool × pos × list command_comp :=
do pos ← cur_pos,
   is_img ← option.is_some <$> (tk "as" >> tk "image")?,
   prod.mk is_img <$> prod.mk pos <$> parse_cmd_list_aux

meta def command_comp.translate (to_unfold : list name) : command_comp → tactic string
| (command_comp.cmd s) := return s
| (command_comp.antiquot p) :=
  do s ← mathematica.form_of_expr <$> dunfold to_unfold p {fail_if_unchanged := ff},
     return $ "Activate[LeanForm[" ++ s ++ "]]"

meta def execute_list (to_unfold : list name) (is_img : bool) (l : list command_comp) : tactic pexpr :=
do l ← l.mmap (command_comp.translate to_unfold), --tactic.trace $ string.join l,
   let cmd := if is_img then "MakeDataUrlFromImage[" ++ string.join l ++ "]" else string.join l,
   s ← mathematica.execute_and_eval cmd,
   mathematica.pexpr_of_mmexpr mathematica.trans_env.empty s

-- return ``(())

meta def string_of_pos_comp (to_unfold : list name) :
  bool × pos × list command_comp → tactic (pos × (string ⊕ expr))
| ⟨is_img, p, c⟩ :=
do e ← execute_list to_unfold is_img c >>= to_expr,
   prod.mk p <$> if is_img then  sum.inl <$> eval_expr string e else return (sum.inr e)
-- prod.mk is_img <$> prod.mk p <$> (execute_list is_img c >>= to_expr >>= eval_expr string)

meta def make_widget (to_unfold : list name) (p : bool × pos × list command_comp) :
  tactic $ pos × (widget.component tactic_state empty) :=
do (loc, data) ← string_of_pos_comp to_unfold p,
match data with
| sum.inl s := return $ ⟨loc, url_component s⟩
| sum.inr e := prod.mk loc <$> expr_widget e
end

@[user_command] meta def parse_test (_ : parse (tk "begin_mm_block")) : lean.parser unit :=
do --⟨ln, c⟩ ← cur_pos,
   to_unfold ← (tk "(" >> tk "unfolding" >> ident* <* tk ")")?,
   l ← parse_cmd_list*,
   tk "end_mm_block",
   l ← l.mmap (λ e, make_widget (to_unfold.get_or_else []) e),
   l.mmap' $ λ ⟨⟨ln, c⟩, w⟩,
     trace "saving at " >> trace (⟨ln, c - ("begin_mm_block".length - 1)⟩ : pos) >>
     save_widget ⟨ln, c - ("begin_mm_block".length - 1)⟩  w

open widget
 -- #find component tactic_state empty

run_cmd save_widget ⟨125, 0⟩ $ widget.component.with_should_update (λ _ _, tt) $ component.pure $
λ _,
/- [h "ul" [] [
     h "li" [] ["this is list item 1"],
     h "li" [] ["this is list item 2"],
     h "hr" [] [],
     h "li" [] [
          h "span" [] ["there is a button here"],
          h "button" [on_click (λ _, 3)] ["click me!"]
     ]
]] -- -/[h "p" [attr.style [("color", "blue")]] ["hi"]]



end

constant x : ℝ
open real

noncomputable def f : ℝ → ℝ := λ x, sin x + cos x

begin_mm_block  (unfolding f)
"4+4";

-- as image "Plot3D[x^2-y, {x,-3,3}, {y,-3,3}]";

-- as image
-- "PlotOverX["((sin x)^2 - x)", {"x",-10,10}]";

-- "Factor["(x^2-2*x+1)"]";

-- as image
-- "Plot["f"[y], {y,-2,2}]";

end_mm_block

#exit








begin_mm_block

"MakeDataUrlFromImage[

    Plot[Sin[x]^2-x,{x,-10,10}]

]"

end_mm_block







/- begin_mm_block

"MakeDataUrlFromImage[
    PlotOverX["(x^3-2*x+1)", {"x",-5,5}]
]"

end_mm_block
 -/