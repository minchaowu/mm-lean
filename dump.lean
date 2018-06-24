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

meta def write_string (s : string) : tactic unit :=
unsafe_run_io $ @write_file "temp.txt" s io.mode.write

meta def dump (n : ℕ) : tactic string := 
do l ← gen_thm,
   return (to_fmt (list.map (λ e : name × expr, (e.1, form_of_expr e.2)) (list.take n l))).to_string

meta def dump_all : tactic string := 
do l ← gen_thm,
   return (to_fmt (list.map (λ e : name × expr, (e.1, form_of_expr e.2)) l)).to_string

-- run_cmd dump 2 >>= write_string

-- run_cmd dump_all >>= write_string
