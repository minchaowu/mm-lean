OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] := 
  "A" <> OutputFormat[h] <> "[" <> 
    StringRiffle[Apply[List, Map[OutputFormat, Hold[args]]], ","] <> 
  "]"
  
RunLeanTactic[x_, t_String, p_String, b_?BooleanQ, i_?StringQ]:=Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd `1` \"`2`\" `3` >>= write_string",t,x // OutputFormat, If[b, "tt", "ff"]]; WriteString[s, StringForm["import main `1`", i], "\n", cmd]; Close[s];RunThrough[p <> " temp.lean",0];Import["temp.txt", CharacterEncoding -> "UTF8"]];

RunLeanTactic[x_,t_,p_]:=RunLeanTactic[x,t,p,False,""]
RunLeanTactic[x_,t_,p_,b_?BooleanQ] := RunLeanTactic[x,t,p,b,""]
RunLeanTactic[x_,t_,p_,i_String] := RunLeanTactic[x,t,p,False,i]

ProveUsingLeanTactic[x_, t_String, p_String, b_?BooleanQ] := Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd prove_using_tac (`1`) \"`2`\" `3` >>= write_string",t,x // OutputFormat, If[b, "tt", "ff"]]; WriteString[s, "import main", "\n", cmd]; Close[s];RunThrough[p <> " temp.lean",0];Import["temp.txt", CharacterEncoding -> "UTF8"]];

ProveUsingLeanTactic[x_,t_,p_] := ProveUsingLeanTactic[x,t,p,False]

ProveInteractively[e_] := Module[{s,t,cmd,ts}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; t=OpenWrite["interactive_temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd translate \"`1`\" >>= write_string",e // OutputFormat]; WriteString[s, "import main", "\n", cmd]; Close[s];RunThrough[p <> " temp.lean",0];ts=Import["temp.txt", CharacterEncoding -> "UTF8"]; cmd=StringForm["example : `1` := _", ts]; WriteString[t, cmd]; Close[t]; RunProcess[{"emacs","interactive_temp.lean"}];];

SelectLeanPremises[e_] := RunLeanTactic[e, "find_relevant_facts", "premise_selection"]

SetAttributes[OutputFormat, HoldFirst];
SetAttributes[RunLeanTactic, HoldFirst];
SetAttributes[ProveUsingLeanTactic, HoldFirst];
SetAttributes[ProveInteractively, HoldFirst];
SetAttributes[SelectLeanPremises, HoldFirst];

LeanProof[t_String, exe_String]:=Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["#grid_view `1`", t]; WriteString[s, "import grid_view", "\n", "set_option pp.beta true", "\n", "open tactic.interactive", "\n", cmd]; Close[s]; Import[exe <> " temp.lean", "Text"] // ToExpression];
