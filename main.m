OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] := 
  "A" <> OutputFormat[h] <> "[" <> 
    StringRiffle[Apply[List, Map[OutputFormat, Hold[args]]], ","] <> 
  "]"
  
RunLeanTactic[x_, t_String, b_?BooleanQ, i_?StringQ]:=Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd `1` \"`2`\" `3` >>= write_string",t,x // OutputFormat, If[b, "tt", "ff"]]; WriteString[s, StringForm["import main `1`", i], "\n", cmd]; Close[s];RunThrough["lean temp.lean", 0];Import["temp.txt", CharacterEncoding -> "UTF8"]];

RunLeanTactic[x_,t_]:=RunLeanTactic[x,t,False,""]
RunLeanTactic[x_,t_,b_?BooleanQ] := RunLeanTactic[x,t,b,""]
RunLeanTactic[x_,t_,i_String] := RunLeanTactic[x,t,False,i]

ProveUsingLeanTactic[x_, t_String, b_?BooleanQ] := Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd prove_using_tac (`1`) \"`2`\" `3` >>= write_string",t,x // OutputFormat, If[b, "tt", "ff"]]; WriteString[s, "import main", "\n", cmd]; Close[s];RunThrough["lean temp.lean", 0];Import["temp.txt", CharacterEncoding -> "UTF8"]];

ProveUsingLeanTactic[x_,t_] := ProveUsingLeanTactic[x,t,False]

ProveInteractively[e_] := Module[{s,t,cmd,ts}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; t=OpenWrite["interactive_temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd translate \"`1`\" >>= write_string",e // OutputFormat]; WriteString[s, "import main", "\n", cmd]; Close[s];RunThrough["lean temp.lean", 0];ts=Import["temp.txt", CharacterEncoding -> "UTF8"]; cmd=StringForm["example : `1` := _", ts]; WriteString[t, cmd]; Close[t]; RunProcess[{"emacs","interactive_temp.lean"}];];

SetAttributes[OutputFormat, HoldFirst];
SetAttributes[RunLeanTactic, HoldFirst];
SetAttributes[ProveUsingLeanTactic, HoldFirst];

SetAttributes[ProveInteractively, HoldFirst];