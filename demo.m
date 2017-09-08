OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] := 
 "A" <> OutputFormat[h] <> "[" <> 
  StringRiffle[Map[OutputFormat, List[args]], ","] <> "]"

RunLeanTactic[x_, t_String]:=Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd `1` \"`2`\" >>= write_string",t,x // OutputFormat]; WriteString[s, "import demo", "\n", cmd]; Close[s];RunThrough["lean temp.lean", 0];ReadString["temp.txt"]];

ProveUsingLeanTactic[x_, t_String] :=
                                                                                                                                                         Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd prove_using_tac (`1`) \"`2`\" >>= write_string",t,x // OutputFormat]; WriteString[s, "import demo", "\n", cmd]; Close[s];RunThrough["lean temp.lean", 0];ReadString["temp.txt"]];