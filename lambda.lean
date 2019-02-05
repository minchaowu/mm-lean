import mathematica
open mathematica mmexpr tactic

@[app_to_pexpr_keyed]
meta def lam_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"LambdaFunction",
λ env args, match args with
| [app (sym "Typed") [sym e, t], bd] := 
  do ltp ← pexpr_of_mmexpr env t,
     v ← mk_local' e binder_info.default (pexpr.to_raw_expr ltp),--return $ mk_local_const_placeholder x, 
     bd' ← pexpr_of_mmexpr (env.insert e v) bd,
     return $ mk_lambda' v bd' 
| [sym e, bd] := pexpr_of_mmexpr env (app (sym "Function") [sym e, bd])
| _ := failed
end⟩

@[sym_to_expr]
meta def startype_to_expr : sym_trans_expr_rule :=
⟨"StarType", `(Type)⟩

@[sym_to_expr]
meta def proptype_to_expr : sym_trans_expr_rule :=
⟨"PropType", `(Type)⟩

@[app_to_expr_keyed]
meta def typeu_to_expr : app_trans_expr_keyed_rule :=
⟨"TypeU",
λ env args, match args with
| [n] := do n' ← pexpr_of_mmexpr env n,
       to_expr ``(Sort %%n')
| _ := failed
end⟩

@[app_to_pexpr_keyed]
meta def pair_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Pair",
λ env args, match args with
| [t1, t2] :=
   do t1' ← pexpr_of_mmexpr env t1,
      t2' ← pexpr_of_mmexpr env t2,
      return ``((%%t1', %%t2'))
| _ := failed
end⟩

@[app_to_pexpr_keyed]
meta def tuple_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Tuple", 
λ env args, do args' ← list.mmap (pexpr_of_mmexpr env) args, return $ pexpr_fold_op ``(()) ``(prod.mk) args'⟩

@[app_to_pexpr_keyed]
meta def prod_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"ProductType", 
λ env args, do args' ← list.mmap (pexpr_of_mmexpr env) args, return $ pexpr_fold_op ``(()) ``(prod) args'⟩

@[app_to_pexpr_keyed]
meta def arrow_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"ArrowType",
λ env args, match args with
| [t1, t2] :=
  do t1' ← pexpr_of_mmexpr env t1,
     t2' ← pexpr_of_mmexpr env t2,
     return ``(%%t1' → %%t2')
| _ := failed
end⟩

@[app_to_pexpr_keyed]
meta def pi_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"PiType",
λ env args, match args with
| [app (sym "Typed") [sym e, t], bd] := 
  do ltp ← pexpr_of_mmexpr env t,
     v ← mk_local' e binder_info.default (pexpr.to_raw_expr ltp),
     bd' ← pexpr_of_mmexpr (env.insert e v) bd,
     return $ mk_pi' v bd' 
| [sym e, bd] := 
  do v ← return $ mk_local_const_placeholder e, 
     bd' ← pexpr_of_mmexpr (env.insert e v) bd,
     return $ mk_pi' v bd'
| _ := failed
end⟩

