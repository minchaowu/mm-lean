-- import imports k_nn main

-- open tactic

-- meta def find_relevant_facts (mm_fml : string) (b := ff) : tactic string :=
-- do e ← preprocess mm_fml,
--    (contents_map, features_map, names) ← get_all_decls,
--    let relevant_facts := find_k_most_relevant_facts_to_expr e contents_map features_map names.snd 10,
--    relevant_facts.mmap (λ f, do tp ← mk_const f.1 >>= infer_type, return (f.1, tp)) >>= print_name_type_list
