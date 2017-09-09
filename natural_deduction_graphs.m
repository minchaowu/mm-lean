(* ::Package:: *)

GraphUnionWithLabels[a1_, a2_] := 
 GraphUnion[a1, a2, 
  VertexLabels -> Flatten[VertexLabels /. {Options[a1], Options[a2]}]] 
VertexAddWithLabel[g_, Labeled[v_, l_]] := 
 Graph[VertexAdd[g, v], 
  VertexLabels -> Append[VertexLabels /. Options[g], v -> l]]
EdgeAddWithLabel[g_, Labeled[v_, l_]] := 
 Graph[EdgeAdd[g, v], EdgeLabels -> Append[EdgeLabels /. Options[g], v -> l]]

RootNode[g_Graph] := Last[VertexList[g]]

GetSecondFromPlaced[Placed[{_, t_}, _]] := t
ProofType[g_Graph] := 
 RootNode[g] /. PropertyValue[g, VertexLabels] // GetSecondFromPlaced

VertexNameCntr = 0;


NewVertexName[] := VertexNameCntr = VertexNameCntr + 1; Symbol[
 "v" <> ToString[VertexNameCntr]];


ExtendContext[ctx_, rl_] := Join[{rl}, ctx]

ImpliesConclusion[Implies[_, b_]] := b
ImpliesConclusion[Not[a_]] := False



ProofToGraph[AndIntro[lhs_, rhs_], ctx_] := 
 With[{plhs = ProofToGraph[lhs, ctx], prhs = ProofToGraph[rhs, ctx]}, 
  With[{rlhs = RootNode[plhs], rrhs = RootNode[prhs], nvx = NewVertexName[]}, 
   EdgeAdd[VertexAddWithLabel[GraphUnionWithLabels[plhs, prhs], 
     Labeled[nvx, 
      Placed[{"\[And]I", And[ProofType[plhs], ProofType[prhs]]}, {Above, 
        Below}]]], {rlhs \[DirectedEdge] nvx, rrhs \[DirectedEdge] nvx}]]]

ProofToGraph[AndElimLeft[pand_], ctx_] :=
 With[{prf = ProofToGraph[pand, ctx]}, 
  With[{r = RootNode[prf], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prf, 
     Labeled[nvx, Placed[{"\[And]EL", ProofType[prf][[1]]}, {Above, Below}]]],
     r \[DirectedEdge] nvx]]]

ProofToGraph[AndElimRight[pand_], ctx_] :=
 With[{prf = ProofToGraph[pand, ctx]}, 
  With[{r = RootNode[prf], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prf, 
     Labeled[nvx, Placed[{"\[And]ER", ProofType[prf][[2]]}, {Above, Below}]]],
     r \[DirectedEdge] nvx]]]

ProofToGraph[OrIntroLeft[trhs_, plhs_], ctx_] :=
 With[{prf = ProofToGraph[plhs, ctx]}, 
  With[{r = RootNode[prf], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prf, 
     Labeled[nvx, 
      Placed[{"\[Or]IL", Or[ProofType[prf], trhs]}, {Above, Below}]]], 
    r \[DirectedEdge] nvx]]]

ProofToGraph[OrIntroRight[tlhs_, prhs_], ctx_] :=
 With[{prf = ProofToGraph[prhs, ctx]}, 
  With[{r = RootNode[prf], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prf, 
     Labeled[nvx, 
      Placed[{"\[Or]IR", Or[tlhs, ProofType[prf]]}, {Above, Below}]]], 
    r \[DirectedEdge] nvx]]]

ProofToGraph[ImpliesElim[pimp_, phyp_], ctx_] :=
 With[{prfi = ProofToGraph[pimp, ctx], prfh = ProofToGraph[phyp, ctx]}, 
  With[{rimp = RootNode[prfi], rhyp = RootNode[prfh], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[GraphUnionWithLabels[prfi, prfh], 
     Labeled[nvx, 
      Placed[{"\[Implies]E", ImpliesConclusion[ProofType[prfi]]}, {Above, 
        Below}]]], {rimp \[DirectedEdge] nvx, rhyp \[DirectedEdge] nvx}]]]

ProofToGraph[ImpliesIntro[hyp_, nm_, pf_], ctx_] :=
 With[{prf = ProofToGraph[pf, ExtendContext[ctx, nm -> LocalHyp[nm, hyp]]]}, 
  With[{r = RootNode[prf], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prf, 
     Labeled[nvx, 
      Placed[{"\[Implies]I  [" <> ToString[nm] <> "]", 
        Implies[hyp, ProofType[prf]]}, {Above, Below}]]], 
    r \[DirectedEdge] nvx]]]

ProofToGraph[LocalHyp[nm_, tp_], ctx_] :=
 Graph[{Labeled[NewVertexName[], 
    Placed[{"Hyp: " <> ToString[nm], tp}, {Above, Below}]]}, {}]

ProofToGraph[OrElim[por_, plhs_, prhs_], ctx_] := 
 With[{prfo = ProofToGraph[por, ctx], prfl = ProofToGraph[plhs, ctx], 
   prfr = ProofToGraph[prhs, ctx]}, 
  With[{ror = RootNode[prfo], rlhs = RootNode[prfl], rrhs = RootNode[prfr], 
    nvx = NewVertexName[]}, 
   EdgeAdd[VertexAddWithLabel[
     GraphUnionWithLabels[GraphUnionWithLabels[prfo, prfl], prfr], 
     Labeled[nvx, 
      Placed[{"\[Or]E", ImpliesConclusion[ProofType[prfl]]}, {Above, 
        Below}]]], {ror \[DirectedEdge] nvx, rlhs \[DirectedEdge] nvx, 
     rrhs \[DirectedEdge] nvx}]]]

ProofToGraph[TrueIntro, ctx_] := 
 Graph[{Labeled[NewVertexName[], Placed[{"TI", True}, {Above, Below}]]}, {}]

ProofToGraph[FalseElim[tgt_, prf_], ctx_] :=
 With[{prff = ProofToGraph[prf, ctx]}, 
  With[{r = RootNode[prff], nvx = NewVertexName[]},
   EdgeAdd[
    VertexAddWithLabel[prff, 
     Labeled[nvx, Placed[{"FE", tgt}, {Above, Below}]]], 
    r \[DirectedEdge] nvx]]]

ProofToGraph[t_, ctx_] := 
 If[KeyExistsQ[ctx, t], ProofToGraph[t /. ctx, {}], 
  Graph[{Labeled[NewVertexName[], 
     Placed[{"Assum", ToString[t]}, {Above, Below}]]}, {}]]

IsPropProofWithVars[AndIntro[plhs_, prhs_], vs_, ctx_] := 
 IsPropProofWithVars[plhs, vs, ctx] && IsPropProofWithVars[prhs, vs, ctx]
IsPropProofWithVars[AndElimLeft[pand_], vs_, ctx_] := 
 IsPropProofWithVars[pand, vs, ctx]
IsPropProofWithVars[AndElimRight[pand_], vs_, ctx_] := 
 IsPropProofWithVars[pand, vs, ctx]
IsPropProofWithVars[OrIntroRight[_, por_], vs_, ctx_] := 
 IsPropProofWithVars[por, vs, ctx]
IsPropProofWithVars[OrIntroLeft[_, por_], vs_, ctx_] := 
 IsPropProofWithVars[por, vs, ctx]
IsPropProofWithVars[OrElim[por_, plhs_, prhs_], vs_, ctx_] := 
 IsPropProofWithVars[plhs, vs] && IsPropProofWithVars[prhs, vs, ctx] && 
  IsPropProofWithVars[por, vs, ctx]
IsPropProofWithVars[ImpliesIntro[_, _, prhs_], vs_, ctx_] := 
 IsPropProofWithVars[prhs, vs, ctx]
IsPropProofWithVars[ImpliesElim[plhs_, prhs_], vs_, ctx_] := 
 IsPropProofWithVars[plhs, vs, ctx] && IsPropProofWithVars[prhs, vs, ctx]
IsPropProofWithVars[TrueIntro, vs_, ctx_] := True
IsPropProofWithVars[FalseElim[_, plhs_], vs_, ctx_] := 
 IsPropProofWithVars[plhs, vs, ctx]
IsPropProofWithVars[LocalHyp[_, _], vs_, ctx_] := True
IsPropProofWithVars[t_, vs_, ctx_] := MemberQ[vs, t] || MemberQ[ctx, t]||MatchQ[t,_Symbol]
IsPropProofWithVars[Inactive[h_][t_], vs_, ctx_] := 
 IsPropProofWithVars[h[t], vs, ctx]
IsPropProofWithVars[t_, ctx_] := IsPropProofWithVars[t, {}, ctx]

IsPropWithVars[And[t1_, t2_], vs_] := 
 And[IsPropWithVars[t1, vs], IsPropWithVars[t2, vs]]
IsPropWithVars[Or[t1_, t2_], vs_] := 
 And[IsPropWithVars[t1, vs], IsPropWithVars[t2, vs]]
IsPropWithVars[Implies[t1_, t2_], vs_] := 
 And[IsPropWithVars[t1, vs], IsPropWithVars[t2, vs]]
IsPropWithVars[Not[t1_], vs_] := IsPropWithVars[t1, vs]
IsPropWithVars[True, vs_] := True
IsPropWithVars[False, vs_] := True
IsPropWithVars[t_, vs_] := MemberQ[vs, t] || MatchQ[t, _Symbol]
IsPropWithVars[Inactive[h_][t_], vs_] := IsPropWithVars[h[t], vs]
IsPropWithVars[t_] := IsPropWithVars[t, {}]


LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[
       LeanNameMkString["intro", 
        LeanNameMkString["and", LeanNameAnonymous]], _], P_], Q_], HP_], HQ_],
   env_] :=
 AndIntro[LeanForm[HP, env], LeanForm[HQ, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["elim_left", 
       LeanNameMkString["and", LeanNameAnonymous]], _], P_], Q_], Hand_], 
  env_] :=
 AndElimLeft[LeanForm[Hand, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["left", 
       LeanNameMkString["and", LeanNameAnonymous]], _], P_], Q_], Hand_], 
  env_] :=
 AndElimLeft[LeanForm[Hand, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["elim_right", 
       LeanNameMkString["and", LeanNameAnonymous]], _], P_], Q_], Hand_], 
  env_] :=
 AndElimRight[LeanForm[Hand, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["right", 
       LeanNameMkString["and", LeanNameAnonymous]], _], P_], Q_], Hand_], 
  env_] :=
 AndElimRight[LeanForm[Hand, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["inl", LeanNameMkString["or", LeanNameAnonymous]], _], 
     P_], Q_], HP_], env_] :=
 OrIntroLeft[LeanForm[Q, env], LeanForm[HP, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanConst[
      LeanNameMkString["inr", LeanNameMkString["or", LeanNameAnonymous]], _], 
     P_], Q_], HQ_], env_] :=
 OrIntroRight[LeanForm[P, env], LeanForm[HQ, env]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanApp[
       LeanApp[LeanConst[
         LeanNameMkString["elim", 
          LeanNameMkString["or", LeanNameAnonymous]], _], P_], Q_], R_], 
     Hor_], HPR_], HQR_], env_] :=
 OrElim[LeanForm[Hor, env], LeanForm[HPR, env], LeanForm[HQR, env]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["false", "rec"], _], Q_], p_], 
  env_] := FalseElim[LeanForm[Q, env], LeanForm[p, env]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["false", "elim"], _], Q_], p_], 
  env_] := FalseElim[LeanForm[Q, env], LeanForm[p, env]]

LeanForm[LeanConst[LeanName["false"], _], env_] := False

LeanForm[LeanConst[LeanNameMkString["A", LeanNameAnonymous], 
   LeanLevelListNil], env_] := P
LeanForm[LeanConst[LeanNameMkString["B", LeanNameAnonymous], 
   LeanLevelListNil], env_] := Q
LeanForm[LeanConst[LeanNameMkString["C", LeanNameAnonymous], 
   LeanLevelListNil], env_] := R

LeanForm[LeanApp[f_, a_], env_] := 
 With[{av = LeanForm[a, env]}, 
  If[IsPropProofWithVars[Activate[av], env], 
   ImpliesElim[LeanForm[f, env], LeanForm[a, env]],
   Print["isn't prop proof with vars: " <> ToString[Activate[av]]]; 
   LeanForm[f, env][LeanForm[a, env]]]]

LeanForm[LeanLambda[nm_, bi_, tp_, bd_], v_] := 
 With[{sn = Symbol[StringReplace[StringOfName[nm], "_" -> ""]]},
   If[MemberQ[v, sn], 
     LeanForm[LeanLambda[UnderscoreName[nm], bi, tp, bd], v], 
     With[{tpf = Activate[LeanForm[tp, v]]},
    If[IsPropWithVars[tpf],
     ImpliesIntro[tpf, sn, LeanForm[bd, Prepend[v, sn]]], Apply[Function, 
         List[sn, LeanForm[bd, Prepend[v, sn]]]]]]]]

LeanForm[LeanPi[nm_, bi_, tp_, bd_], v_] := 
 With[{sn = Symbol[StringReplace[StringOfName[nm], "_" -> ""]]},
   If[MemberQ[v, sn], 
     LeanForm[LeanPi[UnderscoreName[nm], bi, tp, bd], v], 
     With[{tpf = Activate[LeanForm[tp, v]]},
    If[IsPropWithVars[tpf],
     Implies[tpf, LeanForm[bd, Prepend[v, sn]]], Apply[ForAll, 
         List[sn, LeanForm[bd, Prepend[v, sn]]]]]]]]

FoldApps[f_, {}] := f
FoldApps[f_, vs_] := FoldApps[f[First[vs]], Rest[vs]]

DiagramOfFormula[p_, vs_] := 
 ProofToGraph[
  FoldApps[ProveUsingLeanTactic[p, "tactic.intros >> mm_prover_unfold [`imp_of_or_imp_left, `imp_of_or_imp_right,`imp_false_of_not, `uncurry, `id_locked, `absurd]", True] // ToExpression // LeanForm, vs], {}]
