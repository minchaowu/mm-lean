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

-- meta def write_string (s : string) : tactic unit :=
-- unsafe_run_io $ @write_file "temp.txt" s io.mode.write

meta def dump (n : ℕ) : tactic format := 
do l ← gen_thm,
   let f := λ e : name × expr, (e.1, e.2, form_of_expr e.2) in do
   tactic.pp $ list.map f $ list.take n l >>= return

meta def dump_all : tactic format := 
do l ← gen_thm,
   let f := λ e : name × expr, (e.1, e.2, form_of_expr e.2) in do
   tactic.pp $ list.map f $ l >>= return

-- run_cmd dump 2 >>= trace

-- run_cmd dump_all >>= trace
