TypeOf[x_String]:=Module[{s},s=OpenWrite["temp.lean"];WriteString[s,"import demo", "\n", StringForm["run_cmd tactic.to_expr `1`(@`2`) >>= mm_check","``",x]];Close[s];RunThrough["lean temp.lean", 0];ReadString["temp.txt"]];

(* This is a workaround. The InputForm of Implies[a, b] should be symbolic *)
GenVars[x_]:=StringCases[x // StandardForm // ToString // StringReplace[#1, "\[Implies]"->" "]& // ToString, RegularExpression["\\w+"]] // DeleteDuplicates // ToString // StringReplace[#1, {","->"", "}"->" : Prop}"}]&;

GenGoals[x_]:= x // StandardForm // ToString // StringReplace[#1, {"&&"->"\[And]", "||"->"∨", "!"->"\[Not]", "\[Implies]"->"→"}]&;

Genthms[x_]:=StringForm["def mm_thm `1` : `2` := by mm_prover", GenVars[x], GenGoals[x]];

(* GenLeanInput[x_]:=Module[{s}, s=OpenWrite["temp.lean"]; StringForm["import demo \n `1`",Genthms[x]] // WriteString[s,#1]&; Close[s]]; *)

Prove[x_, b_:False]:=Module[{s}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"];WriteString[s, "import demo", "\n", Genthms[x], "\n", If[b, "run_cmd mm_write `mm_thm tt", "run_cmd mm_write `mm_thm"]]; Close[s];RunThrough["lean temp.lean", 0];ReadString["temp.txt"]];

ShowProof[x_String,b_:False]:=Module[{s,cmd}, s=OpenWrite["temp.lean", CharacterEncoding -> "UTF8"]; cmd=StringForm["run_cmd mm_write `1``2`","`",x]; WriteString[s, "import demo", "\n", If[b, {cmd // ToString," tt"} // StringJoin, cmd]]; Close[s];RunThrough["lean temp.lean", 0];ReadString["temp.txt"]];
