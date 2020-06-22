import tactic.core
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
setup_tactic_parser
open tactic

meta inductive command_comp
| cmd : string → command_comp
| antiquot : pexpr → command_comp

meta def command_comp.to_string : command_comp → string
| (command_comp.cmd s) := "command: " ++ s
| (command_comp.antiquot s) := "antiquot: " ++ to_string s

meta instance : has_repr command_comp :=
⟨command_comp.to_string⟩

meta def parse_string_component : parser string :=
do s ← parser.pexpr 10000,
   to_expr s >>= ↑(eval_expr string)

meta def parse_antiquote : parser pexpr :=
/- tk "♭" >>  -/parser.pexpr 10000 /- <* tk "♭" -/

meta def parse_cmd_list : parser $ list command_comp :=
(do pe ← command_comp.antiquot <$> parse_antiquote,
    rst ← parse_cmd_list,
    return $ pe::rst) <|>
(do cmd ← command_comp.cmd <$> parse_string_component,
    rst ← parse_cmd_list,
    return $ cmd::rst) <|>
tk "end_mm_block" >> return []

@[user_command] meta def parse_test (_ : parse (tk "begin_mm_block")) : parser unit :=
do l ← parse_cmd_list, tactic.trace $ repr l
.

end

begin_mm_block
 "hi"  ℕ  "oops"
end_mm_block

begin_mm_block
"Factor["λ x, x^2 -2*x + 1"]"
end_mm_block

#check ℕ
