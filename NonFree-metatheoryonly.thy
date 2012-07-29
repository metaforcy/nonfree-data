theory NonFree
imports Main
begin

(* hide_const tl  *)



section{* Combinators *}


definition
  setfunspace :: "'a set => 'b set => ('a => 'b) set" (infixr "->" 60)
where
  "(A -> B) == {f . ALL x : A. f x : B}"
lemma setfunspaceI[intro!]: "(ALL x:A. f x:B) ==> f : (A->B)"
  by (simp add: setfunspace_def)

definition setcons where
  "setcons A As == { Cons x xs | x xs . x : A & xs : As }"

fun product where 
  product_nil:  "product [] = {[]}"
| product_cons: "product (Cons A As) = setcons A (product As)"


fun holdsAll where
  "holdsAll phi [] = True"
| "holdsAll phi (Cons x xs) = (phi x & holdsAll phi xs)"


lemma holdsAll_char: "holdsAll phi xs = (ALL x : set xs. phi x)"
  apply (induct xs)
  by simp+

fun holdsAll2 where
  "holdsAll2 R [] ys = (ys = [])"
| "holdsAll2 R (Cons x xs) ys = (EX y ys'. ys = Cons y ys'  &  R x y  &  holdsAll2 R xs ys')"

lemma holdsAll2_char: "length xs = length ys ==> holdsAll2 R xs ys = (ALL (x,y) : set (zip xs ys). R x y)"
  apply (induct xs arbitrary: ys)
  apply simp+
  oops


fun map2 where
  "map2 f Nil Nil = Nil"
| "map2 f (Cons x xs) (Cons y ys) = Cons (f x y) (map2 f xs ys)"






section {* Horn theory *}



datatype var = var nat
datatype pvar = pvar nat
  (* terms are either variables or term operations (Op) applied to terms: *)
  (* parameter variablen seien so gesorted wie von arOfP vorgeschrieben *)
  (* Sortierung ist Teil der Identitaet von Variablen *)
datatype ('sort,'opsym) trm = 
  Var 'sort var | Op 'opsym "pvar list" "('sort,'opsym) trm list" 

  (* atomic formulas (atoms) are either equational or relational atoms: *)
  (* die Sorten der pvars werden durch die psorts beschrieben
     und die Interpretation der parameter condition ist fix, steht also gleich als
     Praedikat auf Parametern drin *)
  (* Pconds are relations on parameters with a fixed semantic interpretation;
     they are not characterized via horn clauses *)
datatype ('sort,'opsym,'rlsym,'psort,'param) atm = 
  Pcond "'param list \<Rightarrow> bool" "'psort list" "pvar list" | 
  Eq 'sort "('sort,'opsym) trm" "('sort,'opsym) trm" |
  Rl 'rlsym "pvar list" "('sort,'opsym) trm list"

(* Horn clauses: *)
datatype ('sort,'opsym,'rlsym,'psort,'param) hcl = 
Horn "('sort,'opsym,'rlsym,'psort,'param) atm list" 
     "('sort,'opsym,'rlsym,'psort,'param) atm"



locale Signature = 
  fixes stOf :: "'opsym \<Rightarrow> 'sort"
    and arOfP :: "'opsym \<Rightarrow> 'psort list" 
    and arOf :: "'opsym \<Rightarrow> 'sort list" 
    and rarOf :: "'rlsym \<Rightarrow> 'sort list"
    and rarOfP :: "'rlsym \<Rightarrow> 'psort list"
    and params :: "'psort \<Rightarrow> 'paramuni set"
    and prels :: "(('paramuni list \<Rightarrow> bool) * 'psort list) set"
begin


lemma holdsAll_mono: "(ALL x. P x --> Q x) ==> holdsAll P xs --> holdsAll Q xs"
  apply (induct xs) by simp+
(* lemma holdsAll2_mono: "(ALL x y. R x y --> R2 x y) ==> holdsAll2 R xs ys --> holdsAll2 R2 xs ys"
  unfolding holdsAll2_def by auto *)

inductive
  trms :: "'sort => ('sort,'opsym) trm \<Rightarrow> bool"
where
  trms_VarI:  "trms s (Var s x)"
| trms_OpI: "[| stOf sigma = s  ;  length ps = length (arOfP sigma)  ;  (ALL (x,s):set (zip xs (arOf sigma)). trms s x)  |]
  ==> trms s (Op sigma ps xs)"

inductive
  inhab :: "'sort => bool"
where
  inhabI: "[|  stOf sigma = s  ;  ALL s2 : set (arOf sigma). inhab s2 |]
    ==> inhab s"

lemma inhabI2: "[|  stOf sigma = s  ;  holdsAll inhab (arOf sigma) |]
    ==> inhab s"
  apply (simp add: holdsAll_char)  
  by (rule inhabI)


definition compat where 
"compat intSt intOp \<equiv> 
 \<forall> sigma. \<forall> pl \<in> product (map params (arOfP sigma)). 
          \<forall> al \<in> product (map intSt (arOf sigma)).           
    intOp sigma pl al \<in> intSt (stOf sigma)"

(* more useful in this formulation:
     ALL sigma. intOp sigma : product (map params (arOfP sigma))
       -> product (map intSt (arOf sigma)) -> intSt (stOf sigma) *)

(* A model is a triple (intSt, intOp, intRl) where compat intSt intOp holds *)

(* interpretation of terms in a model, parameterized by an interpretation of 
variables *)
fun intTrm :: 
"('sort \<Rightarrow> 'a set) \<Rightarrow> ('opsym \<Rightarrow> 'paramuni list \<Rightarrow> 'a list \<Rightarrow> 'a) 
  \<Rightarrow> ('psort \<Rightarrow> pvar \<Rightarrow> 'paramuni) \<Rightarrow> ('sort \<Rightarrow> var \<Rightarrow> 'a) 
  \<Rightarrow> ('sort,'opsym) trm \<Rightarrow> 'a"
where 
"intTrm intSt intOp intPvar intVar (Var s x) = intVar s x"
|
"intTrm intSt intOp intPvar intVar (Op sigma pvl ts) = 
 intOp sigma 
   (map2 intPvar (arOfP sigma) pvl) 
   (map (intTrm intSt intOp intPvar intVar) ts)"

(* compatible variable interpretations *)
definition compatVar where 
"compatVar intSt intVar \<equiv> \<forall> s x. intVar s x \<in> intSt s"

definition compatPvar where 
"compatPvar intPvar \<equiv> \<forall> ps px. intPvar ps px \<in> params ps"

lemma intTrm_intSt:
assumes "compatVar intSt intVar" and "compatPvar intPvar"
and "compat intSt intOp" 
and "t \<in> trms s"
shows "intTrm intSt intOp intPvar intVar t \<in> intSt s"
sorry

(* satisfaction of an equational atom by a model under a variable interpretation *) 
definition satPcond where 
"satPcond intPvar R psl pxl \<equiv> R (map2 intPvar psl pxl)"

definition satEq where  
"satEq intSt intOp intPvar intVar t1 t2 \<equiv> 
 intTrm intSt intOp intPvar intVar t1 = intTrm intSt intOp intPvar intVar t2"

(* satisfaction of an relational atom by a model *) 
definition satRl where 
"satRl intSt intOp intRl intPvar intVar \<pi> pxl ts \<equiv> 
 intRl \<pi> 
   (map2 intPvar (rarOfP \<pi>) pxl) 
   (map (intTrm intSt intOp intPvar intVar) ts)"

(* satisfaction of an atom by a model: *)
definition satAtm where 
"satAtm intSt intOp intRl intPvar intVar atm \<equiv> 
 case atm of
   Pcond R psl pxl \<Rightarrow> satPcond intPvar R psl pxl
 | Eq s t1 t2 \<Rightarrow> satEq intSt intOp intPvar intVar t1 t2
 | Rl \<pi> pxl ts \<Rightarrow> satRl intSt intOp intRl intPvar intVar \<pi> pxl ts"

(* satisfaction of a Horn clause by a model: *)
definition satHcl where 
"satHcl intSt intOp intRl hcl \<equiv> 
 case hcl of Horn atml atm \<Rightarrow> 
 \<forall> intPvar intVar. 
    compatPvar intPvar \<and> compatVar intSt intVar \<longrightarrow> 
    holdsAll (satAtm intSt intOp intRl intPvar intVar) atml \<longrightarrow> 
    satAtm intSt intOp intRl intPvar intVar atm"
  (* vermutlich besser in der Form:
     ALL intPvar : compatPvar. ALL intVar : compatVar intST.
        holdsAll (satAtm intSt ...) atml --> satAtm intST ... atm *)

definition compatAtm where  
  "compatAtm atm \<equiv> 
 case atm of
   Pcond R psl pxl \<Rightarrow> (R, psl) \<in> prels \<and> length psl = length pxl 
 | Eq s t1 t2 \<Rightarrow> t1 \<in> trms s \<and> t2 \<in> trms s
 | Rl \<pi> pxl ts \<Rightarrow>
     length pxl = length (rarOfP \<pi>) \<and> 
     ts \<in> product (map trms (rarOf \<pi>))"

definition
  compatHcl
where 
  "compatHcl hcl \<equiv> 
    case hcl of Horn atml atm \<Rightarrow> 
      (\<forall> R psl pxl. atm \<noteq> Pcond R psl pxl) \<and> 
      holdsAll compatAtm atml \<and> compatAtm atm"

end (* context Signature *)
(**************************)






(* the factored type will consists of equiv. classes, i.e., of sets: *)
type_synonym ('sort,'opsym,'paramuni) trmHCL = (* irrelevant for you *)
"('paramuni * ('sort,'opsym) trm) set"


(* NB: HOL types have to be nonempty, so we might have to invent
   dummy psorts, rlsyms. (sorts, opsyms can be assumed) *)
locale HornTheory = Signature stOf arOfP arOf rarOf rarOfP params 
  for stOf :: "'opsym \<Rightarrow> 'sort"
  and arOfP :: "'opsym \<Rightarrow> 'psort list"
  and arOf :: "'opsym \<Rightarrow> 'sort list" 
  and rarOf :: "'rlsym \<Rightarrow> 'sort list" 
  and rarOfP :: "'rlsym \<Rightarrow> 'psort list" 
  and params :: "'psort \<Rightarrow> 'paramuni set" + 
  fixes HCL :: "('sort,'opsym,'rlsym,'psort,'paramuni) hcl set"
  assumes "\<forall> hcl \<in> HCL. compatHcl hcl"
      and inhab_assm: "ALL s. inhab s"
      and params_inhab: "ALL ps. params ps ~= {}"
begin

lemma "trms s ~= {}"
using inhab_assm params_inhab
sorry

(* terms modulo HCL *)
definition trmsHCL :: "'sort \<Rightarrow> ('sort,'opsym,'paramuni) trmHCL set"
where "trmsHCL s \<equiv> undefined"

definition intOpHCL :: 
"'opsym \<Rightarrow> 'paramuni list \<Rightarrow> ('sort,'opsym,'paramuni) trmHCL list \<Rightarrow> ('sort,'opsym,'paramuni) trmHCL"
where "intOpHCL sigma \<equiv> undefined"

definition 
intRlHCL :: "'rlsym \<Rightarrow> 'paramuni list \<Rightarrow> ('sort,'opsym,'paramuni) trmHCL list \<Rightarrow> bool"
where "intRlHCL sigma \<equiv> undefined"

lemma compat_HCL:
"compat trmsHCL intOpHCL"
sorry   

lemma intOpHCL_softtype:
  "intOpHCL sigma : product (map params (arOfP sigma)) -> product (map trmsHCL (arOf sigma)) -> trmsHCL (stOf sigma)"
using compat_HCL[simplified compat_def] by auto 


theorem sat_HCL:
"hcl \<in> HCL \<Longrightarrow> satHcl trmsHCL intOpHCL intRlHCL hcl"
sorry

theorem induct_HCL:
assumes "T \<in> trmsHCL s" 
"\<And> sigma pl Tl. 
  \<lbrakk>pl \<in> product (map params (arOfP sigma)); 
   Tl \<in> product (map trmsHCL (arOf sigma)); 
   holdsAll2 \<phi> (arOf sigma) Tl\<rbrakk> \<Longrightarrow> 
  \<phi> (stOf sigma) (intOpHCL sigma pl Tl)"
shows "\<phi> s T"
sorry

(* better in this formulation:
  ALL (P :: sort => trms => bool), s :: sort, x : trmsHCL s.
    (ALL sigma, ps : product (map params (arOfP sigma)), xs : product (map trmsHCL (arOf sigma)).
      holdsAll2 P (arOf sigma) xs --> P (stOf sigma) (intOpHcl sigma ps xs))
    --> P s x
*)

(* iterator: *)
definition iterHCL :: 
"('sort \<Rightarrow> 'a set) \<Rightarrow> ('opsym \<Rightarrow> 'paramuni list \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 
 ('rlsym \<Rightarrow> 'paramuni list \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'sort =>
 ('sort,'opsym,'paramuni) trmHCL \<Rightarrow> 'a"
where "iterHCL intSt intOp intRl s T \<equiv> undefined"

lemma iterHCL_intSt:
  assumes "ALL s. intSt s  ~= {}"
  and "ALL sigma. intOp sigma : product (map params (arOfP sigma)) -> product (map intSt (arOf sigma)) -> intSt (stOf sigma)"
  and "ALL rl. intRl rl : product (map params (rarOfP rl)) -> product (map intSt (rarOf rl)) -> (UNIV :: bool set)"
and "T \<in> trmsHCL s"
shows "iterHCL intSt intOp intRl s T \<in> intSt s"
sorry

lemma iterHCL_softtype: "[|
    ALL s. intSt s  ~= {}  ;
    ALL sigma. intOp sigma : product (map params (arOfP sigma)) -> product (map intSt (arOf sigma)) -> intSt (stOf sigma) |] ==>
  iterHCL intSt intOp intRl s : trmsHCL s -> intSt s  "
 using iterHCL_intSt
sorry


theorem iter_HCL:
assumes "compat intSt intOp"
  and "ALL hcl. hcl : HCL --> satHcl intSt intOp intRl hcl"
and "pl \<in> product (map params (arOfP sigma))"
and "Tl \<in> product (map trmsHCL (arOf sigma))"
shows 
"iterHCL intSt intOp intRl (stOf sigma) (intOpHCL sigma pl Tl) = 
 intOp sigma pl (map2 (iterHCL intSt intOp intRl) (arOf sigma) Tl)"
sorry

theorem iter_HCL':
  "[|  ALL sigma. intOp sigma : product (map params (arOfP sigma)) -> product (map intSt (arOf sigma)) -> intSt (stOf sigma)  ;
       ALL hcl : HCL. satHcl intSt intOp intRl hcl  |] ==>
  ALL sigma. ALL ps : product (map params (arOfP sigma)).  ALL ts : product (map trmsHCL (arOf sigma)).
    iterHCL intSt intOp intRl (stOf sigma) (intOpHCL sigma ps ts) = 
      intOp sigma ps (map2 (iterHCL intSt intOp intRl) (arOf sigma) ts)  "
  using iter_HCL sorry



end (* context HornTheory *)


thm HornTheory.induct_HCL
thm HornTheory.iter_HCL











end
