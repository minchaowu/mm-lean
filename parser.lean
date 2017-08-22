/-
Author: Robert Y. Lewis
-/

open expr string name level binder_info

meta def expand_let : expr → expr
| (elet nm tp val bod) := expr.replace bod (λ e n, match e with |var n := some val | _ := none end)
| e := e

namespace mathematica

meta def form_of_name : name → string
| anonymous         := "LeanNameAnonymous"
| (mk_string s nm)  := "LeanNameMkString[\"" ++ s ++ "\", " ++ form_of_name nm ++ "]"
| (mk_numeral i nm) := "LeanNameMkNum[" ++ to_string i ++ ", " ++ form_of_name nm ++ "]"

meta def form_of_lvl : level → string
| zero              := "LeanZeroLevel"
| (succ l)          := "LeanLevelSucc[" ++ form_of_lvl l ++ "]"
| (level.max l1 l2) := "LeanLevelMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (imax l1 l2)      := "LeanLevelIMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (param nm)        := "LeanLevelParam[" ++ form_of_name nm ++ "]"
| (mvar nm)         := "LeanLevelMeta[" ++ form_of_name nm ++ "]"

meta def form_of_lvl_list : list level → string
| []       := "LeanLevelListNil"
| (h :: t) := "LeanLevelListCons[" ++ form_of_lvl h ++ ", " ++ form_of_lvl_list t ++ "]"

meta def form_of_binder_info : binder_info → string
| binder_info.default := "BinderInfoDefault"
| implicit            := "BinderInfoImplicit"
| strict_implicit     := "BinderInfoStrictImplicit"
| inst_implicit       := "BinderInfoInstImplicit"
| other               := "BinderInfoOther"

meta def form_of_expr : expr → string
| (var i)                     := "LeanVar[" ++ (format.to_string (to_fmt i) options.mk) ++ "]"
| (sort lvl)                  := "LeanSort[" ++ form_of_lvl lvl ++ "]"
| (const nm lvls)             := "LeanConst[" ++ form_of_name nm ++ ", " ++ form_of_lvl_list lvls ++ "]"
| (mvar nm nm' tp)                := "LeanMetaVar[" ++ form_of_name nm ++ "," ++ form_of_name nm' ++ ", " ++ form_of_expr tp ++ "]"
| (local_const nm ppnm bi tp) := "LeanLocal[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_name ppnm ++ ", " ++ form_of_binder_info bi ++ 
                                     ", " ++ form_of_expr tp ++ "]"
| (app f e)                   := "LeanApp[" ++ form_of_expr f ++ ", " ++ form_of_expr e ++ "]"
| (lam nm bi tp bod)          := "LeanLambda[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ 
                                     form_of_expr tp ++ ", " ++ form_of_expr bod ++ "]"
| (pi nm bi tp bod)           := "LeanPi[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ form_of_expr tp ++
                                     ", " ++ form_of_expr bod ++ "]"
| (elet nm tp val bod)        := form_of_expr $ expand_let $ elet nm tp val bod
| (macro mdf mlst)           := "LeanMacro"

end mathematica
