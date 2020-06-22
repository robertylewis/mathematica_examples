import tactic.core
import mathematica
import data.complex.exponential
/- import data.buffer.parser

inductive command_comp
| cmd : string → command_comp
| antiquot : string → command_comp

def command_comp.to_string : command_comp → string
| (command_comp.cmd s) := "command: " ++ s
| (command_comp.antiquot s) := "antiquot: " ++ s

instance : has_repr command_comp :=
⟨command_comp.to_string⟩

def antiquot_delim : char := '♭'
open parser

def until_antiquot : parser string :=
many_char $ sat $ λ c, c ≠ antiquot_delim

def antiquoted : parser string :=
ch antiquot_delim >>
until_antiquot <*
ch antiquot_delim

meta def components : parser (list command_comp) :=
do s ← command_comp.cmd <$> until_antiquot,
   (eof >> return [s]) <|>
   (do aq ← command_comp.antiquot <$> antiquoted, cmps ← components, return $ s::aq::cmps)

#eval run_string components "abcd ef ♭ee♭ee" -/

reserve notation `♭`
reserve notation `end_mm_block`

section
open widget

/-- This is a helper that should really be in core. You can't use component.stateless on
tactic_state because you can't decide equality on them. -/
meta def component.stateless' {π α} (view : π → list (html α)) : component π α :=
component.mk
  α
  unit
  (λ _ _, ())
  (λ _ _ a, (⟨⟩, some a))
  (λ p _, view p )
  (λ _ _, ff) -- ⟵ this means that the component should not attempt to check that
              -- the props are equal and just always update

meta def url_component (src : string) : component tactic_state string :=
component.stateless' $ λ ts,
  [h "h1" [] ["Mathematica output"],
    h "img" [attr.val "src" src] []
  ]


--component.mk unit unit (λ _ _, ()) (λ _ _ _, ((), none)) (λ _ _, [widget_renderer2]) (λ _ _, tt)
--component.mk_simple unit unit () (λ _ _ _, ((), none)) (λ _ _, [widget_renderer])

-- @component.mk_simple unit unit _ unit unit () (λ _ _ _ , ((), none)) (λ _ _, [widget_renderer])


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
/- tk "♭" >>  -/parser.pexpr 10000 /- <* tk "♭" -/

meta def parse_component : lean.parser command_comp :=
do pe ← parser.pexpr 10000,
   e ← to_expr pe,
   tpe ← infer_type e,
   if tpe = `(string) then do  s ← eval_expr' string e, return $ command_comp.cmd s
   else return $ command_comp.antiquot e

meta def parse_cmd_list : lean.parser $ list command_comp :=
tk "end_mm_block" >> return [] <|>
list.cons <$> parse_component <*> parse_cmd_list

/-
meta def run_command_on (cmd : string → string) (e : expr) : tactic pexpr :=
do rval ← execute_and_eval $ cmd $ form_of_expr e,
   --rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval

-/
meta def command_comp.translate : command_comp → tactic string
| (command_comp.cmd s) := return s
| (command_comp.antiquot p) := let s := mathematica.form_of_expr  p in
return $ "Activate[LeanForm[" ++ s ++ "]]"

meta def execute_list (l : list command_comp) : tactic pexpr :=
do l ← l.mmap command_comp.translate, --tactic.trace $ string.join l,
   s ← mathematica.execute_and_eval $ string.join l,
   mathematica.pexpr_of_mmexpr mathematica.trans_env.empty s

-- return ``(())

@[user_command] meta def parse_test (_ : parse (tk "begin_mm_block")) : lean.parser unit :=
do ⟨ln, c⟩ ← cur_pos, l ← parse_cmd_list, e ← execute_list l, e ← to_expr e,--, parser.of_tactic (to_expr e >>= tactic.trace )
--   tactic.trace "e", tactic.trace e,
   e ← eval_expr string e,
   save_widget ⟨ln, c - ("begin_mm_block".length - 1)⟩ (url_component e) --    save_widget p mycomp
.

end

begin_mm_block

"MakeDataUrlFromImage[

    4+4

]"

end_mm_block

#exit
constant x : ℝ
open real

begin_mm_block

"MakeDataUrlFromImage[

    PlotOverX["((sin x)^2 - x)",{"x",-10,10}]

]"

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