import system.io provers.ljt provers.tableaux parser
open tactic expr io mathematica name task

section
variable [io.interface]
def write_file (fn : string) (cnts : string) (mode := io.mode.write) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h
end

meta def peek_type (e : expr) : tactic string :=
infer_type e >>= λ t, return $ to_string t

meta def write_string (s : string) : tactic unit :=
run_io (λ ioi, (@write_file ioi "temp.txt" s io.mode.write))

meta def mm_check : expr → tactic unit := 
λ e, peek_type e >>= λ s, write_string s

meta def mm_write (s : name) (b := ff) : tactic unit :=
get_decl s >>= λ e, write_string $ cond b (form_of_expr e.value) e.value.to_string

meta def mm_prover : tactic unit := intuit <|> pl_prover

------------------------------------------------------

