/-
Copyright (c) 2017 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Minchao Wu
-/

import system.io provers.ljt provers.tableaux mathematica data.set.basic
open tactic expr io mathematica name task mmexpr

namespace tactic
meta def solve_fully_aux {α : Type} (ex : expr) (tac : tactic α) : tactic (α × expr) :=
do (a, e) ← solve_aux ex tac,
   e' ← instantiate_mvars e,
   guard $ bnot e'.has_meta_var,
   return (a, e')
end tactic

meta def peek_type (e : expr) : tactic string :=
infer_type e >>= λ t, return $ to_string t

meta def write_string (s : string) : tactic unit :=
run_io $ λ ioi, @write_file ioi "temp.txt" s io.mode.write

meta def mm_check : expr → tactic unit := 
λ e, peek_type e >>= λ s, write_string s

meta def mm_write (s : name) (b := ff) : tactic unit :=
get_decl s >>= λ e, write_string $ cond b e.value.to_string (form_of_expr e.value)

meta def mm_prover : tactic unit := intuit <|> pl_prover

/--
 Solve goal using mm_prover and unfold listed constants in the resulting proof
-/
meta def mm_prover_unfold (to_unfold : list name) : tactic unit :=
do t ← target,
   (_, pf) ← tactic.solve_fully_aux t mm_prover,
   dunfold to_unfold pf {fail_if_unchanged := ff} >>= apply

meta def preprocess (mm_fml : string) : tactic expr :=
do m ← parse_mmexpr_tac $ string.to_char_buffer mm_fml,
   pexpr_of_mmexpr trans_env.empty m >>= to_expr

meta def prove_using_tac (tac : tactic unit) (mm_fml  : string) (b := ff) : tactic string :=
(do e ← preprocess mm_fml,
    (_, pf) ← tactic.solve_fully_aux e tac, 
    return $ if b then form_of_expr pf else pf.to_string) 
<|> return "failed"

meta def prove_mm_prop_fml (mm_fml : string) (b := ff) : tactic string :=
prove_using_tac (intros >> mm_prover_unfold ljt_lemmas) mm_fml b

meta def mk_smt_simp_lemmas : tactic simp_lemmas :=
local_context >>= simp_lemmas.append simp_lemmas.mk

meta def mm_smt (mm_fml : string) (b := ff) : tactic string :=
prove_using_tac (intros >> using_smt (do s ← mk_smt_simp_lemmas, simp_target s)) mm_fml b

---------------------------------------------------------------------------------

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

@[app_to_pexpr_keyed]
meta def forall_typed_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"ForAllTyped",
λ env args, match args with
| [sym x, t, bd] := 
  do (n, pe) ← sym_to_lcs_using env t (sym x),
     bd' ← pexpr_of_mmexpr (env.insert n pe) bd,
     return $ mk_pi' pe bd'
| [app (sym "List") l, t, bd] :=
  do vs ← l.mfor (sym_to_lcs_using env t),
     bd' ← pexpr_of_mmexpr (env.insert_list vs) bd,
     return $ mk_pis (vs.map prod.snd) bd'
| _ := failed
end⟩

meta def normalize_set (mm_fml : string) (b := ff) : tactic string :=
do e ← preprocess mm_fml,
   s ← simp_lemmas.mk_default,
   (t, _) ← solve_aux e target,
   pt ← simplify s [] t {} `eq failed >>= pp,
   return $ pt.to_string

@[sym_to_pexpr]
meta def inter_to_pexpr : sym_trans_pexpr_rule :=
⟨"SetInter", ```(has_inter.inter)⟩

@[sym_to_pexpr]
meta def union_to_pexpr : sym_trans_pexpr_rule :=
⟨"SetUnion", ```(has_union.union)⟩

@[sym_to_pexpr]
meta def empty_to_pexpr : sym_trans_pexpr_rule :=
⟨"EmptySet", ```(∅)⟩
