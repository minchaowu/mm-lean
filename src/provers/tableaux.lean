import .utils

open tactic expr

meta def is_conj' (e : expr) : tactic bool :=
do t ← infer_type e, return $ is_app_of t `and

meta def add_facts (prf : expr) : tactic unit :=
do n ← get_unused_name `h none,
t ← infer_type prf,
assertv n t prf >> return ()

meta def split_conjs_at : expr → tactic unit | e :=
do b ← is_conj' e,
if b then do e₁ ← mk_app `and.left [e],
             e₂ ← mk_app `and.right [e],
             add_facts e₁ >> add_facts e₂,
             split_conjs_at e₁ >> split_conjs_at e₂
     else return ()

meta def split_conjs : tactic unit :=
do ctx ← local_context, list.mmap split_conjs_at ctx, return ()

meta def find_disj : tactic (option expr) :=
do ctx ← local_context,
(first $ ctx.map (λ e, do t ← infer_type e, 
                       if is_app_of t `or then return $ some e else 
                                               failed)) <|> return none

meta def pl_prover_aux : ℕ → tactic unit
| 0 := fail "pl prover max depth reached"
| (n + 1) := do split_conjs, contradiction <|>
                do (some h) ← find_disj | fail "unprovable goal",
                   cases h,
                   pl_prover_aux 30,
                   pl_prover_aux 30

meta def pl_prover : tactic unit :=
do repeat (intro_fresh >> skip), 
   deny_conclusion, nnf_hyps,
   pl_prover_aux 30

