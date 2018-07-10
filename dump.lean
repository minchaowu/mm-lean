import imports mathematica system.io

open native tactic mathematica

meta def gen_thm : tactic $ list (name × expr) :=
do env ← get_env,
   return $ env.fold [] 
   (λ dcl l, 
    match dcl with
     | declaration.defn nm _ tp val _ tt := (nm, tp) :: l
     | declaration.thm nm _ tp val := (nm, tp) :: l
     | _ := l
    end)

meta def gen_thm_by_name (ln : list name) : tactic $ list (name × expr) :=
do env ← get_env,
   return $ env.fold [] 
   (λ dcl l, 
    match dcl with
     | declaration.defn nm _ tp val _ tt := 
       if nm ∈ ln then (nm, tp) :: l else l
     | declaration.thm nm _ tp val :=     
       if nm ∈ ln then (nm, tp) :: l else l
     | _ := l
    end)

meta def write_string (s : string) : tactic unit :=
unsafe_run_io $ @write_file "temp.txt" s io.mode.write

meta def dump (n : ℕ) : tactic format := 
do l ← gen_thm,
   let f := λ e : name × expr, (e.1, e.2, form_of_expr e.2) in do
   tactic.pp $ list.map f $ list.take n l >>= return

meta def dump_all : tactic format := 
do l ← gen_thm,
   let f := λ e : name × expr, (e.1, e.2, form_of_expr e.2) in do
   tactic.pp $ list.map f $ l >>= return

meta def dump_search (l : list string) : tactic format :=
do l ← monad.mapm parse_name_tac l,
   l ← gen_thm_by_name l,
   let f := λ e : name × expr, (e.1, e.2, form_of_expr e.2) in do
   tactic.pp $ list.map f $ l >>= return

/- save the buffer manually -/

-- run_cmd dump 2 >>= trace

-- run_cmd dump_all >>= trace

def thms := ["add_comm", 
             "add_assoc", 
             "nat.lt_add_left"]

-- run_cmd dump_search thms >>= trace


/- dump with writing to files -/

-- run_cmd do 
-- d ← dump 2,
-- write_string d.to_string

-- run_cmd do 
-- d ← dump_all,
-- write_string d.to_string

-- run_cmd do 
-- d ← dump_search thms,
-- write_string d.to_string
