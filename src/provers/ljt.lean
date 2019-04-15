import .utils tactic.finish
open tactic expr

/- the intuitionitsic prover -/

-- Assumes pr is a proof of t. Adds the consequences of t to the context
-- and returns tt if anything nontrivial has been added.
meta def add_consequences : expr → expr → tactic bool :=
λ pr t,
let assert_consequences := λ e t, mcond (add_consequences e t) skip (assertv_fresh t e >> pure ()) in
match t with
| `(¬ %%a) :=
  do e ← mk_mapp ``imp_false_of_not [some a, some pr],
     na ← to_expr ``(%%a → false),
     assert_consequences e na,
     return tt
| `(%%a ∧ %%b) :=
  do e₁ ← mk_app ``and.left [pr],
     assert_consequences e₁ a,
     e₂ ← mk_app ``and.right [pr],
     assert_consequences e₂ b,
     return tt
| `(%%a → %%b) :=
  do ctx ← local_context,
     (do h ← find_same_type a ctx,
         assert_consequences (pr h) b,
         return tt) <|>
     match a with
     | `(%%c ∨ %%d) :=
       do e₁ ← mk_mapp ``imp_of_or_imp_left [some c, some d, some b, pr],
          t₁ ← to_expr ``(%%c → %%b),
          assert_consequences e₁ t₁,
          e₂ ← mk_mapp ``imp_of_or_imp_right [some c, some d, some b, pr],
          t₂ ← to_expr ``(%%d → %%b),
          assert_consequences e₂ t₂,
          return tt
     | `(%%c ∧ %%d) :=
       do e ← mk_mapp ``uncurry [some c, some d, some b, pr],
          t ← to_expr ``(%%c → (%%d → %%b)),
          assertv_fresh t e,
          return tt
     | _ := return ff
     end
| _ := return ff
end

-- return tt if any progress is made
meta def process_hyp (h : expr) : tactic bool :=
do t ← infer_type h,
   mcond (add_consequences h t) (clear h >> return tt) (return ff)

-- return tt if any progress is made
meta def process_hyps_aux : list expr → tactic bool
| []        := return ff
| (h :: hs) := do b₁ ← process_hyp h,
                  b₂ ← process_hyps_aux hs,
                  return (b₁ || b₂)

-- fail if no progress is made
meta def process_hyps : tactic unit :=
do ctx ← local_context,
   mcond (process_hyps_aux ctx) skip failed

meta def apply_nonsplitting_rules : tactic unit :=
do repeat (intro_fresh >> skip),
   repeat process_hyps

-- test it
example {p q r s : Prop} (h : p ∨ q → r) (h' : q ∧ r ∧ (s ∨ r → p)) : true :=
by do apply_nonsplitting_rules, triv

meta def is_nested_imp (e : expr) : bool :=
match e with
| `((%%a → %%b) → %%c) := tt
| `(¬%%a → %%c)         := tt
| _                      := ff
end

meta def find_hyp_aux (p : expr → bool) : list expr → tactic expr
| []        := failed
| (h :: hs) := do t ← infer_type h,
                  if p t then return h else find_hyp_aux hs

meta def find_hyp (p : expr → bool) : tactic expr :=
do local_context >>= find_hyp_aux p

meta def apply_splitting_rule : tactic unit :=
(applyc ``and.intro) <|> (applyc ``iff.intro) <|>
(do h ← find_hyp (λ e, is_app_of e `or),
    e ← to_expr ``(or.elim %%h),
    apply e >> clear h)

meta def elim_nested_imp (cont : tactic unit) : list expr → tactic unit
| []        := failed
| (h :: hs) := do t ← infer_type h,
                  (guard (is_nested_imp t) >>
                     (do e ← to_expr ``(nested_imp_elim %%h),
                         apply e >> clear h >> try intros; cont)) <|>
                     (elim_nested_imp hs)

meta def apply_backtracking_rule (cont : tactic unit) : tactic unit :=
do t ← target,
   (guard (is_app_of t `or) >> ((left >> cont) <|> (right >> cont))) <|>
   (local_context >>= elim_nested_imp cont)

meta def intuit : tactic unit :=
do finish <|> 
   (apply_nonsplitting_rules >>
     (finish <|>
       apply_splitting_rule >>
         (intuit >> intuit) <|>
         (apply_backtracking_rule intuit)))

meta def glivenko : tactic unit :=
do repeat (intro_fresh >> skip), deny_conclusion, intuit
