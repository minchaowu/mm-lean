import mathematica
open expr tactic classical

-- namespace list
-- variables {α β : Type} 
-- universes u v w

-- def for : list α → (α → β) → list β := flip map

-- def mfor {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (l : list α) (f : α → m β) : m (list β) :=
-- mmap f l

-- end list

section logical_equivalences
  local attribute [instance] prop_decidable
  variables {a b : Prop}

  theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
  iff.intro classical.by_contradiction not_not_intro

  theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
  iff.intro
    (λ h, if ha : a then or.inr (h ha) else or.inl ha)
    (λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

  theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
  iff.intro
    (λ h, if ha : a then or.inr (λ hb, h ⟨ha, hb⟩) else or.inl ha)
    (λ h, λ ⟨ha, hb⟩, or.elim h (λ hna, hna ha) (λ hnb, hnb hb))

  theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
  assume h₁, or.elim h₁ (assume ha, h^.left ha) (assume hb, h^.right hb)

  theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
  and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

  theorem not_or_iff (a b : Prop) : (¬ (a ∨ b)) = (¬ a ∧ ¬ b) :=
  propext (iff.intro not_and_not_of_not_or not_or_of_not_and_not)

  theorem and_or_distrib (a b c : Prop) : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  iff.intro
    (λ ⟨ha, hbc⟩, or.elim hbc (λ hb, or.inl ⟨ha, hb⟩) (λ hc, or.inr ⟨ha, hc⟩))
    (λ h, or.elim h (λ ⟨ha, hb⟩, ⟨ha, or.inl hb⟩) (λ ⟨ha, hc⟩, ⟨ha, or.inr hc⟩))

  theorem and_or_distrib₂ (a b c : Prop) : (b ∨ c) ∧ a ↔ (b ∧ a) ∨ (c ∧ a) :=
  by rw [and.comm, and_or_distrib, @and.comm a, @and.comm a]

  theorem or_and_distrib (a b c : Prop) : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  begin
    apply iff.intro,
    { intro h, cases h with h₁ h₂, split; left; assumption, cases h₂, split; right; assumption },
    intro h, cases h with h₁ h₂, cases h₁, left, assumption, cases h₂, left, assumption,
    right, split; assumption
  end

  theorem or_and_distrib₂ (a b c : Prop) : (b ∧ c) ∨ a ↔ (b ∨ a) ∧ (c ∨ a) :=
  by rw [or.comm, or_and_distrib, @or.comm a, @or.comm a]

end logical_equivalences

/- the necessary logical principles for ljt-/

theorem imp_of_or_imp_left {p q r : Prop} (h : p ∨ q → r) : p → r :=
λ hp, h (or.inl hp)

theorem imp_of_or_imp_right {p q r : Prop} (h : p ∨ q → r) : q → r :=
λ hq, h (or.inr hq)

theorem uncurry {p q r : Prop} (h : p ∧ q → r) : p → q → r :=
λ hp hq, h ⟨hp, hq⟩

theorem imp_false_of_not {p : Prop} (h : ¬ p) : p → false := h

theorem nested_imp_elim {a b c d : Prop}
  (h : (c → d) → b) (h₀ : (d → b) → c → d) (h₁ : b → a) : a :=
begin
  apply h₁,
  apply h,
  apply h₀,
  intro h₂,
  apply h,
  intro h₃,
  apply h₂
end

def ljt_lemmas := [`imp_of_or_imp_left,
                   `imp_of_or_imp_right,
                   `uncurry,
                   `imp_false_of_not,
                   `nested_imp_elim,
                   `id_locked,
                   `absurd]

/- some generally useful things -/

def {u} list.first {α : Type u} (l : list α) (p : α → Prop) [decidable_pred p] : option α :=
list.rec_on l none (λ h hs recval, if p h then some h else recval)

meta def assertv_fresh (t : expr) (v : expr) : tactic unit :=
do n ← get_unused_name `h none,
   assertv n t v >> return ()

meta def intro_fresh : tactic expr :=
get_unused_name `h none >>= intro

meta def deny_conclusion : tactic unit :=
do apply `(@classical.by_contradiction),
n ← get_unused_name `h none,
intro n >> return ()

meta def simplify_goal (S : simp_lemmas) (cfg : simp_config := {}) : tactic unit :=
do t ← target,
  (new_t, pr) ← simplify S [] t cfg,
  replace_target new_t pr

meta def simp (cfg : simp_config := {}) : tactic unit :=
do S ← simp_lemmas.mk_default,
simplify_goal S cfg >> try triv >> try (reflexivity reducible)

meta def simp_only (hs : list expr) (cfg : simp_config := {}) : tactic unit :=
do S ← simp_lemmas.mk.append hs,
   simplify_goal S cfg >> try triv

meta def simp_only_at (h : expr) (hs : list expr := []) (cfg : simp_config := {}) :
  tactic expr :=
do when (expr.is_local_constant h = ff)
     (fail "tactic simp_only_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk^.append hs,
   (new_htype, heq) ← simplify S [] htype cfg,
   newh ← assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   try $ clear h,
   return newh

meta def simph (cfg : simp_config := {}) : tactic unit :=
collect_ctx_simps >>= simp_only >> simp

meta def finish : tactic unit :=
assumption <|> contradiction <|> triv

/- negation normal form, disjunctive normal form, and conjunctive normal form -/

meta def elim_imp_lemmas : tactic (list expr) :=
  monad.mapm to_expr [``(iff_iff_implies_and_implies), ``(implies_iff_not_or)]

meta def nnf_lemmas : tactic (list expr) :=
  monad.mapm to_expr [``(not_and_iff), ``(not_or_iff), ``(not_not_iff), ``(not_true_iff),
                       ``(not_false_iff), ``(true_and), ``(and_true), ``(false_and),
                       ``(and_false), ``(true_or), ``(or_true), ``(false_or),
                       ``(or_false), ``(not_false_iff), ``(not_true_iff)]

meta def dnf_lemmas : tactic (list expr) :=
  monad.mapm to_expr [``(and_or_distrib), ``(and_or_distrib₂)]

meta def cnf_lemmas : tactic (list expr) :=
  monad.mapm to_expr [``(or_and_distrib), ``(or_and_distrib₂)]

meta def and_or_assoc : tactic (list expr) :=
  monad.mapm to_expr [``(@and_comm), ``(@and_assoc), ``(@or_comm), ``(@or_assoc)]

meta def nnf : tactic unit :=
do hs ← elim_imp_lemmas,
   try $ simp_only hs,
   hs ← nnf_lemmas,
   try $ simp_only hs

meta def cnf : tactic unit :=
do nnf,
   hs ← cnf_lemmas,
   try $ simp_only hs,
   hs ← and_or_assoc,
   try $ simp_only hs

meta def dnf : tactic unit :=
do nnf,
   hs ← dnf_lemmas,
   try $ simp_only hs,
   hs ← and_or_assoc,
   try $ simp_only hs

meta def nnf_at (h : expr) : tactic expr :=
do hs ← elim_imp_lemmas,
   h₁ ← (simp_only_at h hs <|> return h),
   hs ← nnf_lemmas,
   (simp_only_at h₁ hs <|> return h₁)

meta def cnf_at (h : expr) : tactic expr :=
do h₁ ← nnf_at h,
   hs ← cnf_lemmas,
   h₂ ← (simp_only_at h₁ hs <|> return h₁),
   hs ← and_or_assoc,
   (simp_only_at h₂ hs <|> return h₂)

meta def dnf_at (h : expr) : tactic expr :=
do h₁ ← nnf_at h,
   hs ← dnf_lemmas,
   h₂ ← (simp_only_at h₁ hs <|> return h₁),
   hs ← and_or_assoc,
   (simp_only_at h₂ hs <|> return h₂)

meta def nnf_hyps : tactic unit :=
do hyps ← local_context,
list.mfor hyps nnf_at >> return ()
