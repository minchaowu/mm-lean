open tactic expr

/-
meta def expr.mfold' {α : Type}  : Π (e : expr) (a : α) (f : expr → α → tactic α), tactic α 
| (var e) a f := f (var e) a
| (sort l) a f := f (sort l) a
| (const nm l) a f := f (const nm l) a
| (mvar nm ppnm tp) a f:= (f (mvar nm ppnm tp) a) >>= λ a', expr.mfold' tp a' f 
| (local_const nm ppnm bi tp) a f := (f (local_const nm ppnm  bi tp) a) >>= λ a', expr.mfold' tp a' f 
| (app e1 e2) a f := do v1 ← (f (app e1 e2) a) >>= λ a', expr.mfold' e1 a' f, expr.mfold' e2 v1 f
| (lam nm bi e1 e2) a f := 
  do v1 ← (f (lam nm bi e1 e2) a) >>= λ a', expr.mfold' e1 a' f, 
     lc ← mk_local' nm bi e1, 
     e2' ← return $ e2.instantiate_var lc,
     expr.mfold' e2' v1 f
| (pi nm bi e1 e2) a f := 
  do v1 ← (f (pi nm bi e1 e2) a) >>= λ a', expr.mfold' e1 a' f, 
     lc ← mk_local' nm bi e1, 
     e2' ← return $ e2.instantiate_var lc,
     expr.mfold' e2' v1 f
| (elet n e1 e2 e3) a f := do v1 ← (f (elet n e1 e2 e3) a) >>= λ a', expr.mfold' e1 a' f, v2 ← expr.mfold' e2 v1 f, expr.mfold' e3 v2 f
| (macro c b) a f := f (macro c b) a

meta def prop_subterms (e : expr) : tactic (rb_set expr) :=
e.mfold' mk_rb_set 
 (λ e s, 
  do ip ← is_proof e,
  return $ if ip then s.insert e else s)

meta def is_forall : expr → tactic bool
| (pi nm bi tp bd) := do sort l ← infer_type tp, return $ bnot (l = level.zero)
| _ := return ff

meta def lemmas_used (e : expr) : tactic (list expr) :=
do pst ← prop_subterms e,
   pst.to_list.mmap infer_type >>= mfilter (λ x, bnot <$> is_forall x)

/-#check list.filter
run_cmd
do dcl ← get_decl `add_le_add,
   pst ← prop_subterms dcl.value,
--   trace pst,
   pst.to_list.mmap infer_type >>= mfilter (λ x, bnot <$> is_forall x) >>= trace
--   (pst.to_list.mfilter (λ x, bnot <$> (is_forall x))) >>= mmap infer_type >>= trace-/

-/

meta def is_prop_concl_tp : expr → tactic bool
--| `(Prop) := tt
| `(Π _ : %%T, %%b) := do m ← mk_meta_var T, is_prop_concl_tp (b.instantiate_var m)
| t := do  tp ← infer_type t, return $ tp = `(Prop)

meta def is_prop_concl (e : expr) : tactic unit :=
do tp ← infer_type e,
   b ← is_prop_concl_tp tp,
if b then skip else failed

run_cmd is_prop_concl `(nat.mod_lt)

meta def list_prop_consts : expr → tactic (list name)
| (var _) := return []
| (sort _) := return []
| (const nm l) := (is_prop_concl (const nm l) >> return [nm]) <|> return []
| (mvar _ _ tp) := list_prop_consts tp
| (local_const _ _ _ tp) := list_prop_consts tp
| (app e1 e2) := do l1 ← list_prop_consts e1, l2 ← list_prop_consts e2, return $ l1 ++ l2
| (lam _ _ e1 e2) := do l1 ← list_prop_consts e1, l2 ← list_prop_consts e2, return $ l1 ++ l2
| (pi _ _ e1 e2) := do l1 ← list_prop_consts e1, l2 ← list_prop_consts e2, return $ l1 ++ l2
| (elet _ e1 e2 e3) := do l1 ← list_prop_consts e1, l2 ← list_prop_consts e2, l3 ← list_prop_consts e3, return $ l1 ++ l2 ++ l3
| (macro _ _) := return []


meta def rb_set.of_list {α : Type} [has_ordering α] : list α → rb_set α
| [] := mk_rb_set
| (h::t) := (rb_set.of_list t).insert h

meta def is_app_of_int_const (ics : name_set) : expr → bool
| (const nm _) := ics.contains nm
| (app e1 e2) := is_app_of_int_const e1
| _ := ff

meta def apps_of_interesting_consts (ics : name_set) : expr → tactic (list expr)
| (var _) := return []
| (sort _) := return []
| (const nm l) := return []
| (mvar _ _ tp) := apps_of_interesting_consts tp
| (local_const _ _ _ tp) := apps_of_interesting_consts tp
| (app e1 e2) := if is_app_of_int_const ics e1 then do l1 ← apps_of_interesting_consts e2, rv ← whnf $ app e1 e2, return $ [rv] ++ l1 else  do l1 ← apps_of_interesting_consts e1, l2 ← apps_of_interesting_consts e2, return $ l1 ++ l2
| (lam nm bi e1 e2) := do l1 ← apps_of_interesting_consts e1, l2 ← apps_of_interesting_consts (e2.instantiate_var (local_const nm nm binder_info.default e1)), return $ l1 ++ l2
| (pi _ _ e1 e2) := do l1 ← apps_of_interesting_consts e1, l2 ← apps_of_interesting_consts e2, return $ l1 ++ l2 
| (elet _ e1 e2 e3) :=do l1 ← apps_of_interesting_consts e1, l2 ← apps_of_interesting_consts e2, l3 ← apps_of_interesting_consts e3, return $ l1 ++ l2 ++ l3
| (macro _ _) := return []


section
open name

meta def is_recursor : name → bool
| (mk_string "rec" n) := tt
| (mk_string "rec_on" n) := tt
| (mk_string "cases_on" n) := tt
| (mk_string "case_strong_induction_on" n) := tt
| _ := ff

private meta def boring_consts : name_set :=
name_set.of_list [`id_locked, `congr, `forall_congr_eq, `congr_arg, `propext, `forall_const, `eq_self_iff_true]

meta def is_boring : name → bool
| (mk_string _ (mk_string "eq" _)) := tt
| (mk_string _ (mk_string "or" _)) := tt
| (mk_string _ (mk_string "and" _)) := tt
| (mk_string _ (mk_string "decidable" _)) := tt
| (mk_string _ (mk_string "iff" _)) := tt
| (mk_string _ (mk_string "not" _)) := tt
| n := boring_consts.contains n

end

meta def is_interesting (n : name) : bool :=
bnot (is_recursor n || is_boring n)

meta def name_set.filter (s : name_set) (P : name → bool) : name_set :=
s.fold s (λ v s', if P v then s' else s'.erase v)

meta def get_interesting_consts (e : expr) : tactic name_set :=
do ns ← name_set.of_list <$> list_prop_consts e,
   return $ ns.filter is_interesting

meta def get_interesting_lemmas_used (e : expr) : tactic (list (name × expr)) :=
do ns ← get_interesting_consts e,
   ns.mfold [] (λ n l, do tp ← mk_const n >>= infer_type, return ((n, tp)::l))
   
meta def print_lemmas_used (e : expr) : tactic string :=
do exs ← get_interesting_lemmas_used e,
   --pex ← exs.mmap pp,
   string.join <$> exs.mmap (λ s, do pps ← pp s.2, return $ s.1.to_string ++ " : " ++ pps.to_string ++ "\n")

/-
run_cmd 
do l ← get_decl `nat.mod_lt,
   ns ← name_set.of_list <$> list_prop_consts l.value,
   trace $  (ns.filter is_interesting),
   print_lemmas_used l.value >>= trace

run_cmd 
do l ← get_decl `nat.mod_lt,
   nms ← name_set.of_list <$> (list_prop_consts l.value),
   exps ← apps_of_interesting_consts nms l.value,
   exps.mmap infer_type >>= trace
-/
