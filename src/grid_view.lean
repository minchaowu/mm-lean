import tactic.explode system.io tactic.interactive tactic.doc_commands
open expr tactic tactic.explode

meta def  to_mm_grid_aux : list string → list string → list string → list entry → tactic string
| (line :: lines) (dep :: deps) (thm :: thms) (en :: es) := do
  fmt ← do {
    p ← infer_type en.expr >>= pp,
    let lhs :=  "{" ++ line ++ "," ++ dep ++ "," ++ "\"" ++ thm ++ "\"" ++ ",",
    return $ lhs ++ "\"" ++ to_string p ++ "\"" ++ "}," },
  (++ fmt) <$> to_mm_grid_aux lines deps thms es
| _ _ _ _ := return ""

meta def mm_grid_cmd : string → string :=
λ s, "Grid[{{Steps, References, Applications, Theorems}," ++ s.pop_back ++ "}, Frame -> All]"

meta def to_mm_grid : entries → tactic string :=
λ es : entries,
  let lines := es.l.map (λ en, to_string en.line),
      deps  := es.l.map (λ en, "{" ++ string.intercalate "," (en.deps.map to_string) ++ "}"),
      thms  := es.l.map entry.thm in
  mm_grid_cmd <$> (to_mm_grid_aux lines deps thms es.l)

meta def explode_mm (n : name) (hide_non_prop := tt) : tactic string :=
do const n _ ← resolve_name n | fail "cannot resolve name",
  d ← get_decl n,
  v ← match d with
  | (declaration.defn _ _ _ v _ _) := return v
  | (declaration.thm _ _ _ v)      := return v.get
  | _                  := fail "not a definition"
  end,
  t ← pp d.type,
  explode_expr v hide_non_prop >>= to_mm_grid

meta def explode_grid (n : name) (hide_non_prop := tt) : tactic entries :=
do const n _ ← resolve_name n | fail "cannot resolve name",
  d ← get_decl n,
  v ← match d with
  | (declaration.defn _ _ _ v _ _) := return v
  | (declaration.thm _ _ _ v)      := return v.get
  | _                  := fail "not a definition"
  end,
  t ← pp d.type,
  explode_expr v hide_non_prop

meta def mm_stringfy (s : string) : string :=
"\"" ++ s ++ "\""

meta def view_info (n : name) : tactic string :=
do const n _ ← resolve_name n | fail "cannot resolve name",
  d ← get_decl n,
  match d with
  | (declaration.defn _ _ t v _ _) := do ts ← pp t, ds ← (tactic.doc_string n <|> return "No doc strings found"), 
                                         return $ "Grid[{{Category, Definition}, {Type," ++ (mm_stringfy $ to_string ts) ++ "}, {Description, OpenerView[{Documentation," ++ (mm_stringfy ds) ++ "}]" ++ "}}, Background -> {{LightGray}, None}, Frame -> All]"
-- "Definition | Type: " ++ to_string ts ++ " | Description: " ++ ds
  | (declaration.thm _ _ t v)      := do ts ← pp t, ds ← (tactic.doc_string n <|> return "No doc strings found"), 
                                         return $ "Grid[{{Category, Theorem}, {Type," ++ (mm_stringfy $ to_string ts) ++ "}, {Description, OpenerView[{Documentation," ++ (mm_stringfy ds) ++ "}]" ++ "}}, Background -> {{LightGray}, None}, Frame -> All]"
-- "Theorem | Type: " ++ to_string ts ++ " | Description: " ++ ds
  | _                  := fail "Not a definition"
  end

meta def lookup_lines : entries → nat → entry
| ⟨_, []⟩ n := ⟨default _,0,0,status.sintro,"",[]⟩
| ⟨rb, (hd::tl)⟩ n := if hd.line = n then hd else lookup_lines ⟨rb, tl⟩ n

meta def unfold_proof_aux (es : entries) : entry → tactic string
| ⟨e, l, d, status.sintro, t, ref⟩ := do 
e' ← infer_type e >>= pp,
return $ "Grid[{{Goal," ++ mm_stringfy (e.to_string ++ " : " ++ e'.to_string) ++ "}, {ID," ++ to_string l ++ "}, {Rule, Assumption}}, Background -> {{LightBlue}, None}, Frame -> All]"
| ⟨e, l, d, status.intro, t, ref⟩ := do 
e' ← infer_type e >>= pp,
return $ "Grid[{{Goal," ++ mm_stringfy (e.to_string ++ " : " ++ e'.to_string) ++ "}, {ID," ++ to_string l ++ "}, {Rule, Assumption}}, Background -> {{LightBlue}, None}, Frame -> All]"
| ⟨e, l, d, st, t, ref⟩ := do 
e' ← infer_type e >>= pp,
let el : list entry := list.map (lookup_lines es ) ref, 
ls ← monad.mapm unfold_proof_aux el,
let c := "{" ++ string.intercalate "," ls ++ "}",
return $ "Grid[{{Goal," ++ mm_stringfy e'.to_string ++ "}, {ID," ++ to_string l ++ "}, {Rule," ++ mm_stringfy t ++ "},{Proofs, OpenerView[{Arguments, Column["++ c ++ "]}]}}, Background -> {{LightBlue}, None}, Frame -> All]"

meta def unfold_proof (es : entries) : tactic string := 
let concl := lookup_lines es (es.l.length - 1) in 
unfold_proof_aux es concl

open interactive lean lean.parser

@[user_command]
meta def explode_mm_cmd (_ : parse $ tk "#explode_mm") : lean.parser unit :=
do n ← ident,
   s ← explode_mm n,
   unsafe_run_io $ io.put_str s,
   skip
   .

@[user_command]
meta def grid_view (_ : parse $ tk "#grid_view") : lean.parser unit :=
do n ← ident,
   es ← explode_grid n,
   s ← unfold_proof es,
   unsafe_run_io $ io.put_str s,
   skip
   .

@[user_command]
meta def info_view (_ : parse $ tk "#view_info") : lean.parser unit :=
do n ← ident,
   s ← view_info n,
   unsafe_run_io $ io.put_str s,
   skip
   .
