theory GenParam
imports HOLMetaRec
begin


definition
  funpred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a2 \<Rightarrow> 'b2 \<Rightarrow> bool)
              \<Rightarrow> ('a \<Rightarrow> 'a2) \<Rightarrow> ('b \<Rightarrow> 'b2) \<Rightarrow> bool" ("_ #> _")
where
  "funpred R1 R2 \<equiv> (% f1 f2. (\<forall> x1 x2. R1 x1 x2 \<longrightarrow> R2 (f1 x1) (f2 x2)))"


datatype label = Label "nat"


(* t in primary position because of non-patterns *)
definition
  termTrans :: "'a \<Rightarrow> 'label \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where  
  [MRjud 2 2]: "termTrans t l t' R \<equiv> R t t'"
abbreviation
  termTransAbbrev :: "'label \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" ("_: _ to _ by _") where
  "l: t to t' by R  \<equiv>  termTrans t l t' R" 

(* produces the composition of the FPreds of mappers corresponding to type constructors in tau *)
(* leave l in primary position because we don't expect non-patterns in types *)
definition
  typTrans :: "'label \<Rightarrow> 'a itself \<Rightarrow> 'b itself \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
                ("_: _ to _ via _") where
  [MRjud 2 2]: "typTrans l tau tau' R \<equiv> (\<forall> t1. \<exists> t2. R t1 t2) "




(* rules that are generic in the label *)

lemma [MR]: "\<lbrakk>
    l: t1 to t1' by R1 #> R2 ;
    l: t2 to t2' by R1  \<rbrakk>  \<Longrightarrow>
 l: (t1 t2) to (t1' t2') by R2"
 by (simp add: funpred_def termTrans_def)

lemma [MR]: "\<lbrakk>
    l: TYPE('tau) to TYPE('tau') via R1  ;
    \<And> x x'. l: x to x' by R1  \<Longrightarrow>  l: (t x) to (t' x') by R2  \<rbrakk> \<Longrightarrow>
  l: (% x::'tau. t x) to (% x'::'tau'. t' x') by R1 #> R2"
  by (simp add: funpred_def termTrans_def)



(* is not true! we have to sharpen the  l: tau to tau' via R  judgement
   to preserve left-totality under funpred *)
lemma [MR]: "\<lbrakk>
    l: TYPE('tau) to TYPE('tau') via R1  ;
    l: TYPE('tau2) to TYPE('tau2') via R2  \<rbrakk> \<Longrightarrow>
  l: TYPE('tau \<Rightarrow> 'tau2) to TYPE('tau' \<Rightarrow> 'tau2') via R1 #> R2"
  apply (simp add: typTrans_def funpred_def)
  sorry







datatype name = Name "nat"

definition
  liftalong :: "'label \<Rightarrow> 'a \<Rightarrow> name \<Rightarrow> bool" where
  [MRjud 3 0]: "liftalong l t n \<equiv> True"


(* NB: in our lifting examples R will always be a function, because the mapper
     functor is applied to functions,
     but in general this is a restriction on the  l: tau to tau' via R  judgement *)
lemma [expl_frule]: "\<lbrakk>
    liftalong l (t :: 'tau) n   ;
    l: TYPE('tau) to TYPE('tau') via R   ;
    R ismapper f : A -> B  ;
    t :> A  ;
    define n := f t giving c'  \<rbrakk>
  \<Longrightarrow>  l: t to c' by R"
apply (simp add: define_const_def termTrans_def typTrans_def)
apply (erule allE)
apply (erule exE)
by (rule someI)



R ismapper f : A -> A'  :=  f = graph R & dom R = A & codom R = A'  ???


     R1 ismapper f : A -> A'
     R2 ismapper g : B -> B' ==>
  (R1 #> R2) ismapper ??? : (A->B) -> (A'->B')










definition
  myl where
  "myl = Label 0"

schematic_lemma
  assumes [MRassm]: " myl: TYPE('a) to TYPE('a') via R1 "
     and  [MRassm]: " myl: (c::'a) to (c'::'a') by R1 "
  shows "myl: (% f :: 'a \<Rightarrow> 'a. f c) to (?res :: ('a' \<Rightarrow> 'a') \<Rightarrow> 'a') by ?rel"
  by (tactic {* MetaRec.metarec_tac_debug @{context} 1 *})





end
