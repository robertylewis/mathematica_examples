/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.core
import mathematica
import data.complex.exponential
import data.real.pi
import tactic.interactive_expr

/-!

This demo shows how we can mimic a Mathematica notebook from within Lean.

The syntax here is somewhat hackish; better syntax will be possible in Lean 4.

A section of Mathematica code is entered between `begin_mm_block` and `end_mm_block`.
Mathematica commands are entered in quotes `""`, with each line terminated by a semicolon `;`
corresponding to a `shift-enter` in the standard notebook frontend.
Lean expressions can be inserted as antiquotes between quoted Mathematica expressions.
For parsing reasons, compound Lean expressions must appear in parentheses `()`.

The evaluation of these commands will happen sequentially in the same Mathematica environment.

By default, the output of a line will be translated to a Lean expression and traced.
To display the output as an image instead,
prefix the line with `as image`.

Since Mathematica has no access to Lean's definitional reduction, it is sometimes necessary
to unfold definitions before sending them to Mathematica.
You can begin the block with `begin_mm_block (unfolding f g)` to unfold `f` and `g`
in all antiquoted Lean expressions.

-/

reserve notation `begin_mm_block`
reserve notation `end_mm_block`
reserve notation `as`
reserve notation `image`
reserve notation `unfolding`

@[sym_to_expr]
meta def pi_to_expr : mathematica.sym_trans_expr_rule :=
⟨"Pi", `(real.pi)⟩

@[sym_to_expr]
meta def null_to_expr : mathematica.sym_trans_expr_rule :=
⟨"Null", `(())⟩

/-!
This section develops the widgets for displaying results from Mathematica as images.
-/

section
open widget

meta def component.stateless' {π α} (view : π → list (html α)) : component π α :=
component.with_should_update (λ _ _, tt) $ component.pure view

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

/-!
This section develops the parser for Mathematica blocks.
-/

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

/-!
This section translates, evaluates, and displays the result of a parsed Mathematica command.
-/

meta def command_comp.translate (to_unfold : list name) : command_comp → tactic string
| (command_comp.cmd s) := return s
| (command_comp.antiquot p) :=
  do s ← mathematica.form_of_expr <$> dunfold to_unfold p {fail_if_unchanged := ff},
     return $ "Activate[LeanForm[" ++ s ++ "]]"

meta def execute_list (to_unfold : list name) (is_img : bool) (l : list command_comp) : tactic pexpr :=
do l ← l.mmap (command_comp.translate to_unfold), --tactic.trace $ string.join l,
   let cmd := if is_img then "MakeDataUrlFromImage[" ++ string.join l ++ "]" else string.join l,
   s ← mathematica.execute_global cmd >>= parse_mmexpr_tac,
   mathematica.pexpr_of_mmexpr mathematica.trans_env.empty s

meta def string_of_pos_comp (to_unfold : list name) :
  bool × pos × list command_comp → tactic (pos × (string ⊕ expr))
| ⟨is_img, p, c⟩ :=
do e ← execute_list to_unfold is_img c >>= to_expr,
   prod.mk p <$> if is_img then  sum.inl <$> eval_expr string e else return (sum.inr e)

meta def make_widget (to_unfold : list name) (p : bool × pos × list command_comp) :
  tactic $ pos × (widget.component tactic_state empty) :=
do (loc, data) ← string_of_pos_comp to_unfold p,
match data with
| sum.inl s := return $ ⟨loc, url_component s⟩
| sum.inr e := prod.mk loc <$> expr_widget e
end

@[user_command] meta def parse_mm_block (_ : parse (tk "begin_mm_block")) : lean.parser unit :=
do to_unfold ← (tk "(" >> tk "unfolding" >> ident* <* tk ")")?,
   l ← parse_cmd_list*,
   tk "end_mm_block",
   l ← l.mmap (λ e, make_widget (to_unfold.get_or_else []) e),
   l.mmap' $ λ ⟨⟨ln, c⟩, w⟩, save_widget ⟨ln, c - ("begin_mm_block".length - 1)⟩  w
end


/-!
In this example we show a Mathematica block with three image plots.
Put the cursor on the first characters of the `as image` lines to see the output.

In the second line, we plot a Lean function given as a lambda expression.
In the third, we plot a Lean definition, that we have marked to unfold at the beginning.
-/

open real
noncomputable def f : ℝ → ℝ := λ x, sin x + cos x

begin_mm_block (unfolding f)

as image
"Plot3D[x^2-y, {x,-3,3}, {y,-3,3}]";

as image
"Plot["(λ y, (sin y)^2 - y^2)"[x], {x,-10,10}]";

as image
"Plot["f"[y], {y,-2,2}]";

end_mm_block

/-!
This example gets output from Mathematica as expressions instead of images.

First, we define a symbol `MyPoly` as a Lean expression and factor it.

Then we directly factor a Lean expression.

Uncommenting the `pp` line above shows that we really are seeing full Lean expressions in the output.
-/

-- set_option pp.all true

constants y z : ℝ

begin_mm_block 

"MyPoly ="(z^2-2*z+1);
"Factor[MyPoly]";

"Factor["(y^10-z^10)"]";

end_mm_block