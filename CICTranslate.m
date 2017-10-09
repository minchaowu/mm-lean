Val[i_Integer] := i
Val[_] := -1

CICTranslate[LeanLambda[name_, _, type_, body_], env_] := 
 LambdaFunction[
  Typed[Symbol[StringOfName[name]], CICTranslate[type, env]], 
  CICTranslate[body, Prepend[env, Symbol[StringOfName[name]]]]]
CICTranslate[LeanSort[n_], env_] := 
 With[{n1 = Val[LeanForm[n, env]]}, 
  If[n1 == 0, PropType, If[n1 > 1, TypeU[n1], StarType]]]
CICTranslate[LeanVar[i_], v_] := 
 If[Length[v] > i, v[[i + 1]], LeanVar[i]]
CICTranslate[LeanPi[name_, _, type_, body_], env_] := 
 PiType[Typed[Symbol[StringOfName[name]], CICTranslate[type, env]], 
  CICTranslate[body, Prepend[env, Symbol[StringOfName[name]]]]]
CICTranslate[
  LeanApp[LeanApp[LeanConst[LeanName["prod", "mk"], _], t_], s_], 
  env_] := Tuple[CICTranslate[t, env], CICTranslate[s, env]]
CICTranslate[LeanApp[LeanApp[LeanConst[LeanName["prod"], _], t_], s_],
   env_] := ProductType[CICTranslate[t, env], CICTranslate[s, env]]
CICTranslate[e_] := CICTranslate[e, {}]