/-
Copyright (c) 2017 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu
-/

import system.io provers.ljt provers.tableaux mathematica
open tactic expr io mathematica name task

meta def peek_type (e : expr) : tactic string :=
infer_type e >>= λ t, return $ to_string t

meta def write_string (s : string) : tactic unit :=
run_io (λ ioi, (@write_file ioi "temp.txt" s io.mode.write))

meta def mm_check : expr → tactic unit := 
λ e, peek_type e >>= λ s, write_string s

meta def mm_write (s : name) (b := ff) : tactic unit :=
get_decl s >>= λ e, write_string $ cond b e.value.to_string (form_of_expr e.value)

meta def mm_prover : tactic unit := intuit <|> pl_prover

meta def prove_mm_prop_fml (mm_fml : string) (b := ff) : tactic string :=
do m ← parse_mmexpr_tac $ string.to_char_buffer mm_fml,
   e ← pexpr_of_mmexpr trans_env.empty m >>= to_expr,
   n ← get_unused_name `h,
   assert n e >> intros >> mm_prover >> result >>= λ r,
   match r with
   | macro _ l := return $ cond b (l.head.to_string) (form_of_expr l.head) 
   | _ := return "failed"
   end

