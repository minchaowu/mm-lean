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
run_io $ λ ioi, @write_file ioi "temp.txt" s io.mode.write

meta def mm_check : expr → tactic unit := 
λ e, peek_type e >>= λ s, write_string s

meta def mm_write (s : name) (b := ff) : tactic unit :=
get_decl s >>= λ e, write_string $ cond b e.value.to_string (form_of_expr e.value)

meta def mm_prover : tactic unit := intuit <|> pl_prover

meta def preprocess (mm_fml : string) : tactic expr :=
do m ← parse_mmexpr_tac $ string.to_char_buffer mm_fml,
   trace m,
   pexpr_of_mmexpr trans_env.empty m >>= to_expr

meta def prove_mm_prop_fml (mm_fml : string) (b := ff) : tactic string :=
(do e ← preprocess mm_fml,
   n ← get_unused_name `h,
   assert n e >> intros >> mm_prover >> result >>= λ r,
   match r with
   | macro _ l := return $ cond b (l.head.to_string) (form_of_expr l.head) 
   | _ := return "failed"
   end) <|> return "failed"

meta def mm_smt (mm_fml : string) (b := ff) : tactic string :=
(do e ← preprocess mm_fml,
   n ← get_unused_name `h,
   assert n e >> target >>= trace >> intros >> using_smt skip >> result >>= λ r,
   match r with
   | macro _ l := return $ cond b (l.head.to_string) (form_of_expr l.head) 
   | _ := return "failed"
   end) <|> return "failed"

meta def prove_using_tac (tac : tactic unit) (mm_fml  : string) (b := ff) : tactic string :=
(do trace mm_fml, e ← preprocess mm_fml, trace e,
    (_, pf) ← solve_aux e tac, infer_type pf >>= trace, pf ← instantiate_mvars pf, trace (form_of_expr pf),
    return $ if b then form_of_expr pf else pf.to_string) 
<|> return "failed"


---------------------------------------------------------------------------------

open mmexpr level binder_info

meta def mmexpr_to_string : mmexpr → string
| e := format.to_string $ mmexpr_to_format e

meta def mk_local_const (n : name) (tp : pexpr): expr :=
local_const n n binder_info.default (pexpr.to_raw_expr tp)

private meta def sym_to_lcs_using (env : trans_env) (e : mmexpr) : mmexpr → tactic (string × expr)
| (sym s) := do p ← pexpr_of_mmexpr env e,
                return $ (s, mk_local_const s p)
| _ := failed

private meta def sym_to_lcp : mmexpr → tactic (string × expr)
| (sym s) := return $ (s, mk_local_const_placeholder s)
| _ := failed

@[sym_to_pexpr]
meta def type_to_pexpr : sym_trans_pexpr_rule :=
⟨"Type", ```(Type)⟩

@[sym_to_pexpr]
meta def prop_to_pexpr : sym_trans_pexpr_rule :=
⟨"Prop", ```(Prop)⟩

@[sym_to_pexpr]
meta def true_to_pexpr : sym_trans_pexpr_rule :=
⟨"True", ```(true)⟩

@[sym_to_pexpr]
meta def equal_to_pexpr : sym_trans_pexpr_rule :=
⟨"Equal", ```(eq)⟩

@[app_to_pexpr_keyed]
meta def forall_typed_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"ForAllTyped",
λ env args, match args with
| [sym x, bd] := 
  do v ← return $ mk_local_const_placeholder x, 
     bd' ← pexpr_of_mmexpr (env.insert x v) bd,
     return $ mk_pi' v bd' 
| [app (sym "List") l, t, bd] :=
  do vs ← list.mfor l (sym_to_lcs_using env t),
     bd' ← pexpr_of_mmexpr (env.insert_list vs) bd,
     return $ mk_pis (list.map prod.snd vs) bd'
| [sym x, t, bd] := 
  do v ← return $ mk_local_const_placeholder x,
     bd' ← pexpr_of_mmexpr (env.insert x v) (app (sym "Implies") [t,bd]),
     return $ mk_pi' v bd'
| _ := failed
end⟩

