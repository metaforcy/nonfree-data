theory NonFree
imports "SetoidIsotrans" "~~/src/HOL/Library/FuncSet" Equiv_Relation2
begin

section{* Combinators *}

term list_all2

definition map2 where
"map2 f xl yl \<equiv> map (split f) (zip xl yl)"

lemma list_all2_Nil_iff:
assumes "list_all2 R xs ys"
shows "xs = [] \<longleftrightarrow> ys = []"
using assms by (cases xs, cases ys) auto

lemma list_all2_NilL[simp]:
"list_all2 R [] ys \<longleftrightarrow> ys = []"
using list_all2_Nil_iff by auto

lemma list_all2_NilR[simp]:
"list_all2 R xs [] \<longleftrightarrow> xs = []"
using list_all2_Nil_iff by auto

lemma list_all2_ConsL:
assumes "list_all2 R (x # xs') ys"
shows "\<exists> y ys'. ys = y # ys' \<and> R x y \<and> list_all2 R xs' ys'"
using assms by(cases ys) auto

lemma list_all2_elimL[elim, consumes 2, case_names Cons]:
assumes xs: "xs = x # xs'" and h: "list_all2 R xs ys"
and Cons: "\<And> y ys'. \<lbrakk>ys = y # ys'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsL assms by metis

lemma list_all2_elimL2[elim, consumes 1, case_names Cons]:
assumes h: "list_all2 R (x # xs') ys"
and Cons: "\<And> y ys'. \<lbrakk>ys = y # ys'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsL assms by metis

lemma list_all2_ConsR:
assumes "list_all2 R xs (y # ys')"
shows "\<exists> x xs'. xs = x # xs' \<and> R x y \<and> list_all2 R xs' ys'"
using assms by(cases xs) auto

lemma list_all2_elimR[elim, consumes 2, case_names Cons]:
assumes ys: "ys = y # ys'" and h: "list_all2 R xs ys"
and Cons: "\<And> x xs'. \<lbrakk>xs = x # xs'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsR assms by metis

lemma list_all2_elimR2[elim, consumes 1, case_names Cons]:
assumes h: "list_all2 R xs (y # ys')"
and Cons: "\<And> x xs'. \<lbrakk>xs = x # xs'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsR assms by metis

lemma ex_list_all2:
assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. f x y"
shows "\<exists> ys. list_all2 f xs ys"
using assms apply(induct xs)
apply fastforce
by (metis set.simps insertCI list_all2_Cons)

lemma list_all2_cong[fundef_cong]:
assumes "xs1 = ys1" and "xs2 = ys2"
and "\<And> i . i < length xs2 \<Longrightarrow> R (xs1!i) (xs2!i) \<longleftrightarrow> R' (ys1!i) (ys2!i)"
shows "list_all2 R xs1 xs2 \<longleftrightarrow> list_all2 R' ys1 ys2"
by (metis assms list_all2_conv_all_nth)

lemma set_list_size:
assumes "x \<in> set xs"
shows "f x \<le> list_size f xs"
by (metis assms list_size_estimation' order_eq_refl)

lemma nth_list_size:
assumes "i < length xs"
shows "f (xs!i) \<le> list_size f xs"
by (metis assms nth_mem set_list_size)

lemma list_all2_list_all[simp]:
"list_all2 (\<lambda> x y. f y) xs ys \<longleftrightarrow>
 length xs = length ys \<and> list_all f ys"
by (metis list_all2_conv_all_nth list_all_length)

lemma list_all2_list_all_2[simp]:
"list_all2 f xs xs \<longleftrightarrow> list_all (\<lambda> x. f x x) xs"
unfolding list_all2_def list_all_iff
by (metis splitD splitI2 zip_same)

lemma length_map2[simp]:
assumes "length ys = length xs"
shows "length (map2 f xs ys) = length xs"
using assms unfolding map2_def by auto

lemma listAll2_map2I[intro?]:
assumes "length xs = length ys" and "\<And> x y. R x (f x y)"
shows "list_all2 R xs (map2 f xs ys)"
apply(rule list_all2I) using assms unfolding set_zip map2_def by auto

term "(product,list_all2)"

lemma product_length:
assumes "as \<in> product As"
shows "length as = length As"
using assms apply(induct As arbitrary: as) by auto

lemma list_all2_product:
"list_all2 f xs ys \<longleftrightarrow> ys \<in> product (map (\<lambda> x. {y. f x y}) xs)"
proof-
  {assume "length xs = length ys"
   hence ?thesis
   apply(induct rule: list_induct2) by auto
  }
  thus ?thesis
  using product_length list_all2_lengthD
  by (metis length_map)
qed

abbreviation
  setf_to_predf where
 "setf_to_predf f \<equiv> (% x y. y \<in> f x)"

lemma setf_to_predf_Collect:
  "setf_to_predf Collect f = f" by auto

lemma in_product_list_all2[simp]:
"ys \<in> product (map f xs) \<longleftrightarrow> list_all2 (setf_to_predf f) xs ys"
unfolding list_all2_product by simp

lemma product_list_all2:
"product (map f xs) = Collect (list_all2 (setf_to_predf f) xs)"
by auto



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
     they are not characterized via Horn clauses *)
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
    and params :: "'psort \<Rightarrow> 'param \<Rightarrow> bool"
    and prels :: "(('param list \<Rightarrow> bool) * 'psort list) set"
begin

function trms :: "'sort \<Rightarrow> ('sort,'opsym) trm \<Rightarrow> bool"
where
"trms s (Var s' x) \<longleftrightarrow> s' = s"
|
"trms s (Op \<sigma> pxl Tl) \<longleftrightarrow>
 stOf \<sigma> = s \<and>
 length pxl = length (arOfP \<sigma>) \<and>
 list_all2 trms (arOf \<sigma>) Tl"
by(pat_completeness) auto
termination apply (relation "measure (size o snd)")
apply force
apply simp by (smt nth_list_size)

lemma trms_induct[induct pred: trms, consumes 1, case_names Var Op]:
assumes 0: "trms s T"
and Var: "\<And> s x. phi s (Var s x)"
and Op:
"\<And> \<sigma> pxl Tl.
  \<lbrakk>length pxl = length (arOfP \<sigma>);
   list_all2 trms (arOf \<sigma>) Tl; list_all2 phi (arOf \<sigma>) Tl\<rbrakk>
  \<Longrightarrow> phi (stOf \<sigma>) (Op \<sigma> pxl Tl)"
shows "phi s T"
proof-
  have "\<forall>s. trms s T \<longrightarrow> phi s T"
  apply(induct T rule:
        trm.inducts(1)[of "\<lambda> T. \<forall> s. trms s T \<longrightarrow> phi s T"
                          "\<lambda> Tl. \<forall> sl. list_all2 trms sl Tl \<longrightarrow> list_all2 phi sl Tl"])
  using Var Op by auto
  thus ?thesis using 0 by auto
qed

inductive inhab :: "'sort \<Rightarrow> bool"
where
inhabI: "\<lbrakk>stOf \<sigma> = s; \<And> s2. s2 \<in> set (arOf \<sigma>) \<Longrightarrow> inhab s2\<rbrakk> \<Longrightarrow> inhab s"

lemma inhabI2:
"\<lbrakk>stOf \<sigma> = s; list_all inhab (arOf \<sigma>)\<rbrakk> \<Longrightarrow> inhab s"
by (simp add: list_all_iff inhabI)

definition compat where
"compat intSt intOp \<equiv>
 \<forall> \<sigma> pl al.
   list_all2 params (arOfP \<sigma>) pl \<and>
   list_all2 intSt (arOf \<sigma>) al \<longrightarrow>
   intSt (stOf \<sigma>) (intOp \<sigma> pl al)"

lemma compat_elim[elim?]:
assumes "compat intSt intOp"
and "list_all2 params (arOfP \<sigma>) pl"
and "list_all2 intSt (arOf \<sigma>) al"
shows "intSt (stOf \<sigma>) (intOp \<sigma> pl al)"
using assms unfolding compat_def by auto


(* A model is a triple (intSt, intOp, intRl) where compat intSt intOp holds *)

(* interpretation of terms in a model, parameterized by an interpretation of
variables *)
fun intTrm ::
"('opsym \<Rightarrow> 'param list \<Rightarrow> 'a list \<Rightarrow> 'a)
  \<Rightarrow> ('psort \<Rightarrow> pvar \<Rightarrow> 'param) \<Rightarrow> ('sort \<Rightarrow> var \<Rightarrow> 'a)
  \<Rightarrow> ('sort,'opsym) trm \<Rightarrow> 'a"
where
"intTrm intOp intPvar intVar (Var s x) = intVar s x"
|
"intTrm intOp intPvar intVar (Op \<sigma> pxl ts) =
 intOp \<sigma>
   (map2 intPvar (arOfP \<sigma>) pxl)
   (map (intTrm intOp intPvar intVar) ts)"

lemma intTrm_intSt:
assumes PVAR: "\<And> ps px. params ps (intPvar ps px)" and
VAR: "\<And> s x. intSt s (intVar s x)"
and OP: "compat intSt intOp" and 0: "trms s T"
shows "intSt s (intTrm intOp intPvar intVar T)"
using 0 proof (induct)
  fix \<sigma> Tl and pxl :: "pvar list"
  let ?intTrm = "intTrm intOp intPvar intVar"
  let ?ar = "arOf \<sigma>"  let ?arP = "arOfP \<sigma>" let ?s = "stOf \<sigma>"
  assume l: "length pxl = length (arOfP \<sigma>)"
  and IH: "list_all2 (\<lambda>s T. intSt s (?intTrm T)) ?ar Tl"
  show "intSt ?s (?intTrm (Op \<sigma> pxl Tl))"
  unfolding intTrm.simps using OP proof
    show "list_all2 params ?arP (map2 intPvar ?arP pxl)"
    apply default using PVAR l by auto
  next
    show "list_all2 intSt ?ar (map ?intTrm Tl)"
    using IH unfolding list_all2_map2 .
  qed
qed(insert VAR, auto)

(* satisfaction of an equational atom by a model under a variable interpretation *)
definition satPcond where
"satPcond intPvar R psl pxl \<equiv> R (map2 intPvar psl pxl)
 ::bool"

definition satEq where
"satEq intOp intEq intPvar intVar T1 T2 \<equiv>
 intEq (intTrm intOp intPvar intVar T1) (intTrm intOp intPvar intVar T2)
 ::bool"

(* satisfaction of an relational atom by a model *)
definition satRl where
"satRl intOp intRl intPvar intVar \<pi> pxl Tl \<equiv>
 intRl \<pi>
   (map2 intPvar (rarOfP \<pi>) pxl)
   (map (intTrm intOp intPvar intVar) Tl)
 ::bool"

(* satisfaction of an atom by a model: *)
definition satAtm where
"satAtm intOp intEq intRl intPvar intVar atm \<equiv>
 case atm of
   Pcond R psl pxl \<Rightarrow> satPcond intPvar R psl pxl
 | Eq s T1 T2 \<Rightarrow> satEq intOp intEq intPvar intVar T1 T2
 | Rl \<pi> pxl Tl \<Rightarrow> satRl intOp intRl intPvar intVar \<pi> pxl Tl"

(* satisfaction of a Horn clause by a model: *)
definition satHcl where
"satHcl intSt intOp intEq intRl hcl \<equiv>
 case hcl of Horn atml atm \<Rightarrow>
 \<forall> intPvar intVar.
    (\<forall> ps px. params ps (intPvar ps px)) \<and> (\<forall> s x. intSt s (intVar s x)) \<longrightarrow>
    list_all (satAtm intOp intEq intRl intPvar intVar) atml \<longrightarrow>
    satAtm intOp intEq intRl intPvar intVar atm"
  (* vermutlich besser in der Form:
     ALL intPvar : compatPvar. ALL intVar : compatVar intST.
        list_all (satAtm intSt ...) atml --> satAtm intST ... atm *)

definition compatAtm where
  "compatAtm atm \<equiv>
 case atm of
   Pcond R psl pxl \<Rightarrow> (R, psl) \<in> prels \<and> length psl = length pxl
 | Eq s T1 T2 \<Rightarrow> trms s T1 \<and> trms s T2
 | Rl \<pi> pxl ts \<Rightarrow>
     length pxl = length (rarOfP \<pi>) \<and>
     list_all2 trms (rarOf \<pi>) ts"

definition compatHcl where
"compatHcl hcl \<equiv>
 case hcl of Horn atml atm \<Rightarrow>
   (\<forall> R psl pxl. atm \<noteq> Pcond R psl pxl) \<and>
   list_all compatAtm atml \<and> compatAtm atm"

end (* context Signature *)
(**************************)











datatype ('sort,'opsym,'param) gtrm =
Gop 'opsym "'param list" "('sort,'opsym,'param) gtrm list"

(* the factored type will consists of equiv. classes, i.e., of sets: *)
type_synonym ('sort,'opsym,'param) trmHCL = "(('sort,'opsym,'param) gtrm) set"


(* NB: HOL types have to be nonempty, so we might have to invent
   dummy psorts, rlsyms. (sorts, opsyms can be assumed) *)
locale HornTheory = Signature stOf arOfP arOf rarOf rarOfP params prels
  for stOf :: "'opsym \<Rightarrow> 'sort"
  and arOfP :: "'opsym \<Rightarrow> 'psort list"
  and arOf :: "'opsym \<Rightarrow> 'sort list"
  and rarOf :: "'rlsym \<Rightarrow> 'sort list"
  and rarOfP :: "'rlsym \<Rightarrow> 'psort list"
  and params :: "'psort \<Rightarrow> 'param \<Rightarrow> bool"
  and prels :: "(('param list \<Rightarrow> bool) * 'psort list) set" +
  fixes HCL :: "('sort,'opsym,'rlsym,'psort,'param) hcl set"
  assumes compatHCL: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> compatHcl hcl"
      and inhab_assm: "\<And> s. inhab s"
      and ex_params: "\<And> ps. \<exists> p. params ps p"
begin

lemma ex_list_all2_params:
"\<exists> pl. list_all2 params psl pl"
by (metis ex_list_all2 ex_params)


subsection {* Ground terms *}

function gtrms :: "'sort \<Rightarrow> ('sort,'opsym,'param) gtrm \<Rightarrow> bool"
where
"gtrms s (Gop \<sigma> pl Gl) \<longleftrightarrow>
 stOf \<sigma> = s \<and>
 list_all2 params (arOfP \<sigma>) pl \<and>
 list_all2 gtrms (arOf \<sigma>) Gl"
by(pat_completeness) auto
termination apply (relation "measure (size o snd)")
apply force
apply simp by (smt nth_list_size)

lemma gtrms_induct[induct pred: gtrms, consumes 1, case_names Gop]:
assumes 0: "gtrms s G"
and Gop:
"\<And> \<sigma> pl Gl.
  \<lbrakk>list_all2 params (arOfP \<sigma>) pl;
   list_all2 gtrms (arOf \<sigma>) Gl;
   list_all2 phi (arOf \<sigma>) Gl\<rbrakk>
  \<Longrightarrow> phi (stOf \<sigma>) (Gop \<sigma> pl Gl)"
shows "phi s G"
proof-
  have "\<forall>s. gtrms s G \<longrightarrow> phi s G"
  apply(induct G rule:
        gtrm.inducts(1)[of "\<lambda> Gl. \<forall> sl. list_all2 gtrms sl Gl \<longrightarrow> list_all2 phi sl Gl"
                           "\<lambda> G. \<forall> s. gtrms s G \<longrightarrow> phi s G"])
  using Gop by auto
  thus ?thesis using 0 by auto
qed

lemma gtrms_disj:
assumes "gtrms s G" and "s \<noteq> s'"
shows "\<not> gtrms s' G"
using assms by (induct arbitrary: s') auto

lemma inhab_imp_ex_gtrms:
assumes "inhab s" shows "\<exists> G. gtrms s G"
using assms proof induct
  fix \<sigma> s let ?ar = "arOf \<sigma>" let ?arP = "arOfP \<sigma>"
  assume s: "stOf \<sigma> = s" and
  IH: "\<And>s2. s2 \<in> set ?ar \<Longrightarrow> \<exists>G. gtrms s2 G"
  obtain Gl where Gl: "list_all2 gtrms ?ar Gl"
  using ex_list_all2[of ?ar gtrms, OF IH] by blast
  obtain pl where pl: "list_all2 params (arOfP \<sigma>) pl"
  using ex_list_all2_params by blast
  show "\<exists>G. gtrms s G"
  apply(rule exI[of _ "Gop \<sigma> pl Gl"]) using pl Gl s by simp
qed

lemma ex_gtrms: "\<exists> G. gtrms s G"
using inhab_assm inhab_imp_ex_gtrms by auto

lemma compat_gtrms:
"compat gtrms Gop"
unfolding compat_def by auto


subsection {* The HCL-induced relations *}

lemma set_incl_pred:
"A \<le> B \<longleftrightarrow> (\<forall> a. A a \<longrightarrow> B a)"
by (metis predicate1D predicate1I)

lemma set_incl_pred2:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2. A a1 a2 \<longrightarrow> B a1 a2)"
by (metis predicate2I rev_predicate2D)

lemma set_incl_pred3:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2 a3. A a1 a2 a3 \<longrightarrow> B a1 a2 a3)" (is "_ \<longleftrightarrow> ?R")
proof-
  have "A \<le> B \<longleftrightarrow> (\<forall> a1. A a1 \<le> B a1)" by (metis le_funD le_funI)
  also have "... \<longleftrightarrow> ?R" apply(rule iff_allI)
  unfolding set_incl_pred2 ..
  finally show ?thesis .
qed

lemma set_incl_pred4:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2 a3 a4. A a1 a2 a3 a4 \<longrightarrow> B a1 a2 a3 a4)" (is "_ \<longleftrightarrow> ?R")
proof-
  have "A \<le> B \<longleftrightarrow> (\<forall> a1. A a1 \<le> B a1)" by (metis le_funD le_funI)
  also have "... \<longleftrightarrow> ?R" apply(rule iff_allI)
  unfolding set_incl_pred3 ..
  finally show ?thesis .
qed

lemma list_all_mono:
assumes "phi \<le> chi"
shows "list_all phi \<le> list_all chi"
using assms unfolding set_incl_pred list_all_iff by auto

lemma list_all2_mono:
assumes "phi \<le> chi"
shows "list_all2 phi \<le> list_all2 chi"
using assms by (metis (full_types) list_all2_mono set_incl_pred2)

lemma satEq_mono:
assumes "Geq \<le> Geq2"
shows "satEq Gop Geq intPvar intVar \<le>
       satEq Gop Geq2 intPvar intVar"
using assms unfolding set_incl_pred2 satEq_def by auto

lemma satRl_mono:
assumes "Grel \<le> Grel2"
shows "satRl Gop Grel intPvar intVar \<le>
       satRl Gop Grel2 intPvar intVar"
using assms unfolding set_incl_pred3 satRl_def by auto

lemma satAtm_mono:
assumes e: "Geq \<le> Geq2" and r: "Grel \<le> Grel2"
shows "satAtm Gop Geq Grel intPvar intVar \<le>
       satAtm Gop Geq2 Grel2 intPvar intVar"
using satEq_mono[OF e] satRl_mono[OF r]
unfolding set_incl_pred set_incl_pred2 set_incl_pred3 satAtm_def
apply clarify by (case_tac a, auto)


subsection{* The Horn-determined relations on ground terms *}

inductive
Geq :: "('sort,'opsym,'param) gtrm \<Rightarrow> ('sort,'opsym,'param) gtrm \<Rightarrow> bool"
and
Grel :: "'rlsym \<Rightarrow> 'param list \<Rightarrow> ('sort,'opsym,'param) gtrm list \<Rightarrow> bool"
where
Refl[simp,intro]:
"Geq G G"
|
Sym:
"Geq G1 G2 \<Longrightarrow> Geq G2 G1"
|
Trans:
"\<lbrakk>Geq G1 G2; Geq G2 G3\<rbrakk> \<Longrightarrow> Geq G1 G3"
|
GeqGop:
"\<lbrakk>list_all2 params (arOfP \<sigma>) pl;
  list_all2 gtrms (arOf \<sigma>) Gl; list_all2 gtrms (arOf \<sigma>) Gl';
  list_all2 Geq Gl Gl'\<rbrakk> \<Longrightarrow>
  Geq (Gop \<sigma> pl Gl) (Gop \<sigma> pl Gl')"|
GeqGrel:
"\<lbrakk>list_all2 Geq Gl Gl'; Grel \<pi> pl Gl\<rbrakk> \<Longrightarrow>
  Grel \<pi> pl Gl'"
|Eq:
"\<lbrakk>Horn atml (Eq s T1 T2) \<in> HCL;
  \<And> ps px. params ps (intPvar ps px); \<And>s x. gtrms s (intVar s x);
  list_all (satAtm Gop Geq Grel intPvar intVar) atml\<rbrakk> \<Longrightarrow>
  Geq (intTrm Gop intPvar intVar T1) (intTrm Gop intPvar intVar T2)"
|Rel:
"\<lbrakk>Horn atml (Rl \<pi> pxl Tl) \<in> HCL;
  \<And> ps px. params ps (intPvar ps px); \<And>s x. gtrms s (intVar s x);
  list_all (satAtm Gop Geq Grel intPvar intVar) atml\<rbrakk> \<Longrightarrow>
  Grel \<pi>
   (map2 intPvar (rarOfP \<pi>) pxl)
   (map (intTrm Gop intPvar intVar) Tl)"
monos list_all_mono list_all2_mono satAtm_mono

lemma GeqGrel2:
assumes l: "list_all2 Geq Gl Gl'"
shows "Grel \<pi> pl Gl \<longleftrightarrow> Grel \<pi> pl Gl'"
proof-
  have l': "list_all2 Geq Gl' Gl"
  using assms unfolding list_all2_def set_zip apply simp
  by (metis Sym)
  show ?thesis using GeqGrel l l' by auto
qed

lemma satEq_Gop:
assumes "Horn atml (Eq s T1 T2) \<in> HCL" and
Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)" and
atml: "list_all (satAtm Gop Geq Grel intPvar intVar) atml"
shows "satEq Gop Geq intPvar intVar T1 T2"
unfolding satEq_def using Eq[OF assms] .

lemma satRel_Gop:
assumes "Horn atml (Rl \<pi> pxl Tl) \<in> HCL" and
Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)" and
atml: "list_all (satAtm Gop Geq Grel intPvar intVar) atml"
shows "satRl Gop Grel intPvar intVar \<pi> pxl Tl"
unfolding satRl_def using Rel[OF assms] .

abbreviation "GGeq \<equiv> {(G1,G2) . Geq G1 G2}"

lemma equiv_GGeq:
"equiv UNIV GGeq"
using Refl Sym Trans unfolding equiv_def refl_on_def sym_def trans_def by blast

lemma Geq_Grel_well:
"(Geq G1 G2 \<longrightarrow> ((\<exists> s. gtrms s G1 \<and> gtrms s G2) \<or> G1 = G2))
 \<and>
 (Grel \<pi> pl Gl \<longrightarrow> list_all2 params (rarOfP \<pi>) pl \<and> list_all2 gtrms (rarOf \<pi>) Gl)"
apply(induct rule: Geq_Grel.induct)
  apply force
  apply force
  apply (metis gtrms_disj)
  apply force
proof-
  fix Gl Gl' \<pi> pl
  let ?rar = "rarOf \<pi>" let ?rarP = "rarOfP \<pi>"
  assume IH:
  "list_all2 (\<lambda>G1 G2. Geq G1 G2 \<and> ((\<exists>s. gtrms s G1 \<and> gtrms s G2) \<or> G1 = G2)) Gl Gl'"
  and Gl: "Grel \<pi> pl Gl"
  and 0: "list_all2 params ?rarP pl \<and> list_all2 gtrms ?rar Gl"
  {fix i assume i: "i < length ?rar"
   have "gtrms (?rar!i) (Gl!i)" by (metis 0 i list_all2_nthD)
   moreover have "(\<exists>s. gtrms s (Gl!i) \<and> gtrms s (Gl'!i)) \<or> Gl!i = Gl'!i"
   by (smt 0 IH i list_all2_conv_all_nth)
   ultimately have "gtrms (?rar!i) (Gl'!i)" by (metis gtrms_disj)
  }
  thus "list_all2 params ?rarP pl \<and> list_all2 gtrms ?rar Gl'"
  using 0[THEN conjunct1]
  by (smt 0 IH list_all2_all_nthI list_all2_lengthD)
next
  case (Eq atml s T1 T2 intPvar intVar)
  have "gtrms s (intTrm Gop intPvar intVar T1)"
  apply(rule intTrm_intSt)
    apply (rule Eq(2), rule Eq(3), rule compat_gtrms)
    using compatHCL[OF Eq(1)] unfolding compatHcl_def compatAtm_def by auto
  moreover have "gtrms s (intTrm Gop intPvar intVar T2)"
  apply(rule intTrm_intSt)
    apply (rule Eq(2), rule Eq(3), rule compat_gtrms)
    using compatHCL[OF Eq(1)] unfolding compatHcl_def compatAtm_def by auto
  ultimately show ?case by blast
next
  case (Rel atml \<pi> pxl Tl intPvar intVar)
  show ?case
  apply default
    apply default
      using compatHCL[OF Rel(1)] unfolding compatHcl_def compatAtm_def apply fastforce
      apply (rule Rel(2))
    unfolding list_all2_map2
    using compatHCL[OF Rel(1)] unfolding compatHcl_def compatAtm_def apply simp
    using intTrm_intSt[of intPvar gtrms intVar Gop,
                       OF Rel(2) Rel(3) compat_gtrms]
  by (smt list_all2_cong list_all2_nthD2)
qed

lemma Geq_gtrms:
assumes "Geq G1 G2"
shows "(\<exists> s. gtrms s G1 \<and> gtrms s G2) \<or> G1 = G2"
using assms Geq_Grel_well by blast

lemma Grel_params:
assumes "Grel \<pi> pl Gl"
shows "list_all2 params (rarOfP \<pi>) pl"
using assms Geq_Grel_well by blast

lemma Grel_gtrms:
assumes "Grel \<pi> pl Gl"
shows "list_all2 gtrms (rarOf \<pi>) Gl"
using assms Geq_Grel_well by blast


subsection {* Transition from ground terms to Horn terms (Horn classes of ground terms) *}

definition "clsOf \<equiv> proj GGeq"
definition "htrms s H \<longleftrightarrow> H \<in> UNIV // GGeq \<and> gtrms s (EpsSet H)"
definition "Hop \<sigma> pl Hl = clsOf (Gop \<sigma> pl (map EpsSet Hl))"
definition "Hrel \<pi> pl Hl \<longleftrightarrow> Grel \<pi> pl (map EpsSet Hl)"

(* Pointwise facts: *)
lemma Geq_Eps_clsOf[simp]:
"Geq (EpsSet (clsOf G)) G"
using assms unfolding clsOf_def
using Eps_proj[OF equiv_GGeq] by simp

lemma Geq_Eps_clsOf2[simp]:
"Geq G (EpsSet (clsOf G))"
by (metis Geq_Eps_clsOf Sym)

lemma clsOf:
assumes "gtrms s G"
shows "htrms s (clsOf G)"
unfolding htrms_def apply default
  unfolding clsOf_def proj_in_iff[OF equiv_GGeq] apply fastforce
  using Geq_gtrms[OF Geq_Eps_clsOf, of G] assms
  by (metis (full_types) clsOf_def gtrms_disj)

lemma ex_htrms: "EX H. htrms s H"
  apply rule apply (rule clsOf)
  by (rule someI_ex[OF ex_gtrms])

lemma htrms_clsOf[simp]:
"htrms s (clsOf G) \<longleftrightarrow> gtrms s G"
apply default
unfolding htrms_def using Geq_gtrms[OF Geq_Eps_clsOf, of G]
  apply (metis gtrms_disj)
  by (metis (full_types) clsOf htrms_def)

lemma Eps[simp]:
assumes "htrms s H"
shows "gtrms s (EpsSet H)"
using assms unfolding htrms_def by auto

lemma htrms_in[simp]:
assumes "htrms s H"
shows "H \<in> UNIV // GGeq"
using assms unfolding htrms_def by auto

lemma clsOf_Eps[simp]:
assumes "htrms s H"
shows "clsOf (EpsSet H) = H"
unfolding clsOf_def apply(rule proj_Eps[OF equiv_GGeq]) using htrms_in[OF assms] .

lemma clsOf_surj:
assumes "htrms s H"
shows "\<exists> G. gtrms s G \<and> clsOf G = H"
apply(rule exI[of _ "EpsSet H"]) using assms by auto

lemma clsOf_Geq[simp]:
"clsOf G1 = clsOf G2 \<longleftrightarrow> Geq G1 G2"
unfolding clsOf_def using proj_iff[OF equiv_GGeq] by auto

lemma Geq_Eps[simp]:
assumes "htrms s H1" and "htrms s H2"
shows "Geq (EpsSet H1) (EpsSet H2) \<longleftrightarrow> H1 = H2"
by (metis assms clsOf_Eps clsOf_Geq)

lemma Geq_inj[simp]:
assumes "htrms s H1" and "htrms s H2"
shows "EpsSet H1 = EpsSet H2 \<longleftrightarrow> H1 = H2"
proof-
  have "EpsSet H1 = EpsSet H2 \<Longrightarrow> Geq (EpsSet H1) (EpsSet H2)"
  by (metis Geq_Eps assms)
  hence "EpsSet H1 = EpsSet H2 \<Longrightarrow> H1 = H2" using Geq_Eps[OF assms] by blast
  thus ?thesis by blast
qed

lemma Eps_Geq_surj:
assumes "gtrms s G"
shows "\<exists> H. htrms s H \<and> Geq (EpsSet H) G"
apply(rule exI[of _ "clsOf G"]) using assms by auto

lemma Eps_Geq_surj2:
assumes "gtrms s G"
shows "\<exists> H. htrms s H \<and> Geq G (EpsSet H)"
using Eps_Geq_surj[OF assms] by (metis Sym)

(* List facts: *)
lemmas map_map = "map.compositionality"
declare zip_same[simp]

lemma Geq_Eps_clsOfL[simp]:
"list_all2 Geq (map EpsSet (map clsOf Gl)) Gl"
unfolding map_map list_all2_map1 apply(rule list_all2I) by auto

lemma Geq_Eps_clsOfL_comp[simp]:
"list_all2 Geq (map (EpsSet o clsOf) Gl) Gl"
by (metis Geq_Eps_clsOfL List.map_map)

lemma Geq_Eps_clsOf2L[simp]:
"list_all2 Geq Gl (map EpsSet (map clsOf Gl))"
unfolding map_map list_all2_map2 apply(rule list_all2I) by auto

lemma Geq_Eps_clsOf2L_comp[simp]:
"list_all2 Geq Gl (map (EpsSet o clsOf) Gl)"
by (metis Geq_Eps_clsOf2L List.map_map)

lemma htrms_clsOfL[simp]:
"list_all2 htrms sl (map clsOf Gl) \<longleftrightarrow> list_all2 gtrms sl Gl"
unfolding list_all2_def set_zip apply simp apply safe
apply (metis htrms_clsOf nth_map) by auto

lemma EpsL[simp]:
assumes "list_all2 htrms sl Hl"
shows "list_all2 gtrms sl (map EpsSet Hl)"
using assms unfolding list_all2_def set_zip apply simp apply safe
by (metis Eps nth_map)

lemma htrms_inL[simp]:
assumes "list_all2 htrms sl Hl"
shows "list_all (\<lambda> H. H \<in> UNIV // GGeq) Hl"
unfolding list_all_iff set_conv_nth proof safe
  fix H i assume "i < length Hl"
  hence "htrms (sl!i) (Hl!i)" unfolding list_all2_def set_zip
  by (metis assms list_all2_nthD2)
  thus "Hl ! i \<in> UNIV // GGeq" by simp
qed

lemma clsOf_EpsL[simp]:
assumes "list_all2 htrms sl Hl"
shows "map clsOf (map EpsSet Hl) = Hl"
using assms unfolding map_map list_all2_def set_zip
apply(intro nth_equalityI, simp)
by (smt map_map assms clsOf_Eps length_map list_all2_conv_all_nth nth_map)

lemma clsOf_EpsL_comp[simp]:
assumes "list_all2 htrms sl Hl"
shows "map (clsOf o EpsSet) Hl = Hl"
by (smt List.map_map assms clsOf_EpsL)


lemma clsOf_surjL:
assumes "list_all2 htrms sl Hl"
shows "\<exists> Gl. list_all2 gtrms sl Gl \<and> map clsOf Gl = Hl"
apply(rule exI[of _ "map EpsSet Hl"]) using assms by auto

lemma clsOf_GeqL[simp]:
"map clsOf Gl1 = map clsOf Gl2 \<longleftrightarrow> list_all2 Geq Gl1 Gl2"
unfolding list_eq_iff_nth_eq list_all2_def set_zip apply simp
apply(rule conj_cong)
  apply fastforce
  by (metis clsOf_Geq nth_map)

lemma Geq_EpsL[simp]:
assumes "list_all2 htrms sl Hl1" and "list_all2 htrms sl Hl2"
shows "list_all2 Geq (map EpsSet Hl1) (map EpsSet Hl2) \<longleftrightarrow> Hl1 = Hl2"
by (metis assms clsOf_EpsL clsOf_GeqL)

lemma Geq_injL[simp]:
assumes "list_all2 htrms sl Hl1" and "list_all2 htrms sl Hl2"
shows "map EpsSet Hl1 = map EpsSet Hl2 \<longleftrightarrow> Hl1 = Hl2"
proof-
  have "map EpsSet Hl1 = map EpsSet Hl2 \<Longrightarrow> list_all2 Geq (map EpsSet Hl1) (map EpsSet Hl2)"
  by (metis Geq_EpsL assms)
  hence "map EpsSet Hl1 = map EpsSet Hl2 \<Longrightarrow> Hl1 = Hl2" using Geq_EpsL[OF assms] by blast
  thus ?thesis by blast
qed

lemma Eps_Geq_surjL:
assumes "list_all2 gtrms sl Gl"
shows "\<exists> Hl. list_all2 htrms sl Hl \<and> list_all2 Geq (map EpsSet Hl) Gl"
apply(rule exI[of _ "map clsOf Gl"]) using assms by auto

lemma Eps_Geq_surj2L:
assumes "list_all2 gtrms sl Gl"
shows "\<exists> Hl. list_all2 htrms sl Hl \<and> list_all2 Geq Gl (map EpsSet Hl)"
apply(rule exI[of _ "map clsOf Gl"]) using assms by auto

(* Operations:  *)
lemma clsOf_Gop:
assumes pl: "list_all2 params (arOfP \<sigma>) pl" and Gl: "list_all2 gtrms (arOf \<sigma>) Gl"
shows "clsOf (Gop \<sigma> pl Gl) = Hop \<sigma> pl (map clsOf Gl)"
unfolding Hop_def unfolding clsOf_Geq proof (rule GeqGop)
  show "list_all2 gtrms (arOf \<sigma>) (map EpsSet (map clsOf Gl))"
  unfolding map_map list_all2_map2
  proof (rule list_all2_all_nthI)
    fix i assume i: "i < length (arOf \<sigma>)" let ?ar = "arOf \<sigma>"
    have "gtrms (?ar ! i) (Gl ! i)" by (metis Gl i list_all2_nthD)
    moreover have "Geq (Gl ! i) (EpsSet (clsOf (Gl ! i)))" by (metis Geq_Eps_clsOf2)
    ultimately show "gtrms (?ar ! i) (EpsSet (clsOf (Gl ! i)))" by (metis Eps clsOf)
  qed (metis Gl list_all2_conv_all_nth)
qed (insert assms, auto)

lemma Geq_Eps_Hop:
"Geq (EpsSet (Hop \<sigma> pl Hl)) (Gop \<sigma> pl (map EpsSet Hl))"
unfolding Hop_def by simp

lemma Geq_Eps_Hop2:
"Geq (Gop \<sigma> pl (map EpsSet Hl)) (EpsSet (Hop \<sigma> pl Hl))"
unfolding Hop_def by simp

(* Relations: *)
lemma Hrel_clsOf[simp]:
"Hrel \<pi> pl (map clsOf Gl) \<longleftrightarrow> Grel \<pi> pl Gl"
unfolding Hrel_def apply(rule GeqGrel2) by simp

lemma Grel_Eps[simp]:
"Grel \<pi> pl (map EpsSet Hl) \<longleftrightarrow> Hrel \<pi> pl Hl"
unfolding Hrel_def by simp

lemma inhab_imp_ex_htrms:
assumes "inhab s" shows "\<exists> H. htrms s H"
using inhab_imp_ex_gtrms[OF assms]
by (metis Eps_Geq_surj2)


subsection{* The Horn initial model *}

(* Equational atoms: *)
lemma intTrm_Gop_Geq:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)"
and Var1: "\<And>s x. gtrms s (intVar1 s x)"
and Var: "\<And>s x. Geq (intVar1 s x) (intVar2 s x)"
and T: "trms s T"
shows "Geq (intTrm Gop intPvar intVar1 T) (intTrm Gop intPvar intVar2 T)"
using T proof (induct rule: trms_induct)
  case (Op \<sigma> pxl Tl)
  let ?arP = "arOfP \<sigma>"  let ?ar = "arOf \<sigma>"
  let ?iT1 = "intTrm Gop intPvar intVar1"
  let ?iT2 = "intTrm Gop intPvar intVar2"
  have Var2: "\<And>s x. gtrms s (intVar2 s x)"
  by (metis Var Var1 clsOf_Geq htrms_clsOf)
  show ?case unfolding intTrm.simps apply(rule GeqGop)
    apply (metis Op(1) Pvar listAll2_map2I)
    apply (metis Op(1) Op(2) Pvar Signature.intTrm.simps(2) Signature.trms.simps(2)
                 Var1 compat_gtrms gtrms.simps intTrm_intSt)
    apply (metis Op(1) Op(2) Pvar Signature.intTrm.simps(2) Signature.trms.simps(2)
                 Var2 compat_gtrms gtrms.simps intTrm_intSt)
    using Op(3) unfolding list_all2_map1 list_all2_map2
    list_all2_list_all list_all2_list_all_2 by simp
qed (metis Var intTrm.simps)

lemma map_nth_factor: "j < length xs ==> map f (map g xs) ! j = f (map g xs ! j)"
 by (metis length_map nth_map)


lemma intTrm_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and T: "trms s T"
shows
"intTrm Hop intPvar intVar T =
 clsOf (intTrm Gop intPvar (\<lambda> xs x. EpsSet (intVar xs x)) T)"
using T proof (induct rule: trms_induct)
  case (Op \<sigma> pxl Tl)
  let ?arP = "arOfP \<sigma>"  let ?ar = "arOf \<sigma>"
  let ?iV = "\<lambda> xs x. EpsSet (intVar xs x)"
  let ?hiT = "intTrm Hop intPvar intVar" let ?giT = "intTrm Gop intPvar ?iV"
  have l: "length pxl = length ?arP" and Tl: "list_all2 trms ?ar Tl"
  and IH: "list_all (\<lambda>T. ?hiT T = clsOf (?giT T)) Tl"
  using Op unfolding list_all2_list_all by auto
  have 0: "map (intTrm Hop intPvar intVar) Tl = map clsOf (map ?giT Tl)"
  using IH unfolding list_all_iff by simp
  have "?hiT (Op \<sigma> pxl Tl) = clsOf (Gop \<sigma> (map2 intPvar ?arP pxl) (map ?giT Tl))"
  unfolding intTrm.simps 0 apply(rule clsOf_Gop[symmetric])
    apply (metis Pvar l listAll2_map2I)
    unfolding list_all2_map2 proof (rule list_all2_all_nthI)
      fix i assume i: "i < length ?ar"
      have i': "i < length Tl" by (metis (full_types) Tl i list_all2_lengthD) 
      have hiT_mapunfold: "?hiT (Tl!i) = (map ?hiT Tl) ! i" by (metis i' nth_map)
      have giT_mapunfold: "?giT (Tl!i) = (map ?giT Tl) ! i" by (metis i' nth_map)
      have 1: "?hiT (Tl!i) = clsOf (?giT (Tl!i))" by (metis (mono_tags) IH i' list_all_length)
      hence "Geq (EpsSet (?hiT (Tl!i))) (?giT (Tl!i))" by (metis Geq_Eps_clsOf) 
      moreover 
      {have "gtrms (?ar!i) (?giT (Tl!i))"
       apply(rule intTrm_intSt[OF Pvar])
       by(metis Eps Var compat_gtrms Tl i list_all2_conv_all_nth)+
       hence "gtrms (?ar!i) (EpsSet (?hiT (Tl!i)))" 
       using Eps 1 htrms_clsOf by auto
      }
      ultimately show "gtrms (?ar!i) (?giT (Tl!i))"
      by (metis clsOf_Geq htrms_clsOf)
    qed (metis Tl list_all2_conv_all_nth)
  also have "... = clsOf (?giT (Op \<sigma> pxl Tl))" by simp
  finally show ?case .
qed(metis Var clsOf_Eps intTrm.simps)

lemma intTrm_Hop_clsOf:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)" and T: "trms s T"
shows
"intTrm Hop intPvar (\<lambda> xs x. clsOf (intVar xs x)) T =
 clsOf (intTrm Gop intPvar intVar T)"
proof-
  def iV \<equiv> "\<lambda> xs x. clsOf (intVar xs x)"
  have VVar: "\<And>s x. htrms s (iV s x)" unfolding iV_def using Var by (metis clsOf)
  show ?thesis
  unfolding intTrm_Hop[of intPvar, OF Pvar VVar T, unfolded iV_def] clsOf_Geq
  apply(rule intTrm_Gop_Geq)
  using Pvar Geq_Eps_clsOf Eps VVar iV_def T by auto
qed

(* Relational atoms: *)
lemma Grel_intTrm_Gop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)"
and Var1: "\<And>s x. gtrms s (intVar1 s x)"
and Var: "\<And>s x. Geq (intVar1 s x) (intVar2 s x)"
and Tl: "list_all2 trms (rarOf \<pi>) Tl"
shows "Grel \<pi> pl (map (intTrm Gop intPvar intVar1) Tl) \<longleftrightarrow>
       Grel \<pi> pl (map (intTrm Gop intPvar intVar2) Tl)"
apply(rule GeqGrel2) proof(rule list_all2_all_nthI, simp_all)
  fix i assume i: "i < length Tl"
  let ?giT1 = "intTrm Gop intPvar intVar1"
  let ?giT2 = "intTrm Gop intPvar intVar2"
  show "Geq (?giT1 (Tl!i)) (?giT2 (Tl!i))"
  apply(rule intTrm_Gop_Geq[OF Pvar Var1 Var, of "rarOf \<pi>!i"])
  by (metis Tl i list_all2_nthD2)
qed

lemma Hrel_intTrm_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and Tl: "list_all2 trms (rarOf \<pi>) Tl"
shows
"Hrel \<pi> pl (map (intTrm Hop intPvar intVar) Tl) \<longleftrightarrow>
 Grel \<pi> pl (map (intTrm Gop intPvar (\<lambda> xs x. EpsSet (intVar xs x))) Tl)"
unfolding Hrel_def map_map
apply(rule GeqGrel2) proof(rule list_all2_all_nthI, simp_all)
  fix i assume i: "i < length Tl"
  let ?hiT = "intTrm Hop intPvar intVar"
  let ?giT = "intTrm Gop intPvar (\<lambda>xs x. EpsSet (intVar xs x))"
  have "?hiT (Tl!i) = clsOf (?giT (Tl!i))"
  apply(rule intTrm_Hop[OF Pvar Var, of "rarOf \<pi>!i"])
  by (metis Tl i list_all2_nthD2)
  thus "Geq (EpsSet (?hiT (Tl!i))) (?giT (Tl!i))" by (metis Geq_Eps_clsOf2 Sym)
qed
                                          
lemma Hrel_intTrm_Hop_clsOf:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)" and Tl: "list_all2 trms (rarOf \<pi>) Tl"
shows
"Hrel \<pi> pl (map (intTrm Hop intPvar (\<lambda> xs x. clsOf (intVar xs x))) Tl) \<longleftrightarrow>
 Grel \<pi> pl (map (intTrm Gop intPvar intVar) Tl)"  (is "?L \<longleftrightarrow> ?R")
proof-
  def iV \<equiv> "\<lambda> xs x. clsOf (intVar xs x)"
  have VVar: "\<And>s x. htrms s (iV s x)" unfolding iV_def using Var by (metis clsOf)
  have 0: "\<And> xs x. Geq (EpsSet (iV xs x)) (intVar xs x)"
  by (metis Geq_Eps_clsOf2 Sym iV_def)
  have "?L \<longleftrightarrow> Grel \<pi> pl (map (intTrm Gop intPvar (\<lambda> xs x. EpsSet (iV xs x))) Tl)"
  unfolding iV_def[symmetric] by(rule Hrel_intTrm_Hop[OF Pvar VVar Tl])
  also have "... \<longleftrightarrow> ?R"
  apply(rule Grel_intTrm_Gop[OF Pvar _ 0 Tl]) by (metis Eps VVar)
  finally show ?thesis .
qed

lemma satEq_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)"
and T1: "trms s T1" and T2: "trms s T2"
shows
"satEq Hop (op=) intPvar intVar T1 T2 \<longleftrightarrow>
 satEq Gop Geq intPvar (\<lambda> xs x. EpsSet (intVar xs x)) T1 T2"
unfolding satEq_def intTrm_Hop[OF Pvar Var T1] intTrm_Hop[OF Pvar Var T2] by simp

lemma satRl_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and Tl: "list_all2 trms (rarOf \<pi>) Tl"
shows
"satRl Hop Hrel intPvar intVar \<pi> pxl Tl \<longleftrightarrow>
 satRl Gop Grel intPvar (\<lambda> xs x. EpsSet (intVar xs x)) \<pi> pxl Tl"
unfolding satRl_def Hrel_intTrm_Hop[OF assms]
apply(rule Grel_intTrm_Gop)
using Pvar Eps Var Tl by auto

lemma satAtm_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and
c: "compatAtm atm"
shows
"satAtm Hop (op=) Hrel intPvar intVar atm \<longleftrightarrow>
 satAtm Gop Geq Grel intPvar (\<lambda> xs x. EpsSet (intVar xs x)) atm"
using satEq_Hop[of intPvar intVar, OF Pvar Var]
      satRl_Hop[of intPvar intVar, OF Pvar Var]
using c unfolding compatAtm_def satAtm_def satPcond_def
apply(cases atm) by auto

theorem sat_HCL:
assumes "hcl \<in> HCL"
shows "satHcl htrms Hop (op=) Hrel hcl"
using assms proof(cases hcl, unfold satHcl_def, clarsimp)
  fix atml atm intPvar intVar
  assume H: "Horn atml atm \<in> HCL"
  and Pvar: "\<forall>ps px. params ps (intPvar ps px)"
  and Var: "\<forall>s x. htrms s (intVar s x)"
  and atml: "list_all (satAtm Hop (op =) Hrel intPvar intVar) atml"
  let ?iV = "\<lambda> xs x. EpsSet (intVar xs x)"
  have 0: "list_all (satAtm Gop Geq Grel intPvar ?iV) atml"
  unfolding list_all_iff proof safe
    fix atm' assume atm': "atm' \<in> set atml"
    have c: "compatAtm atm'" using compatHCL[OF assms] H unfolding compatHcl_def
    by (smt Ball_set_list_all atm' compatHCL compatHcl_def hcl.simps(2))
    have "satAtm Hop (op =) Hrel intPvar intVar atm'"
    by (metis Ball_set_list_all atm' atml)
    thus "satAtm Gop Geq Grel intPvar ?iV atm'"
    using Pvar Var satAtm_Hop[OF _ _ c] by auto
  qed
  show "satAtm Hop (op =) Hrel intPvar intVar atm"
  proof(cases atm)
    case Pcond
    hence False using compatHCL[OF H] unfolding compatHcl_def by auto
    thus ?thesis by simp
  next
    case (Eq s T1 T2)
    have T: "trms s T1" "trms s T2"
    using compatHCL[OF assms] H unfolding compatHcl_def Eq compatAtm_def
    by (smt atm.simps(11) compatAtm_def compatHCL compatHcl_def hcl.simps)+
    have "satEq Gop Geq intPvar ?iV T1 T2"
    apply(rule satEq_Gop) using H Pvar Var 0 unfolding Eq by auto
    hence "satEq Hop (op =) intPvar intVar T1 T2" by (metis Pvar T Var satEq_Hop)
    thus ?thesis unfolding H Eq satAtm_def by simp
  next
    case (Rl \<pi> pxl Tl)
    have pxl: "length pxl = length (rarOfP \<pi>)"
    and Tl: "list_all2 trms (rarOf \<pi>) Tl"
    using compatHCL[OF assms] H unfolding compatHcl_def Rl compatAtm_def
    by (smt atm.simps(12) compatAtm_def compatHCL compatHcl_def hcl.simps)+
    have "satRl Gop Grel intPvar ?iV \<pi> pxl Tl"
    apply(rule satRel_Gop) using H Pvar Var 0 unfolding Rl by auto
    hence "satRl Hop Hrel intPvar intVar \<pi> pxl Tl" by (metis Pvar Tl Var satRl_Hop)
    thus ?thesis unfolding H Rl satAtm_def by simp
  qed
qed

theorem induct_HCL[induct pred: htrms, consumes 1, case_names Hop]:
assumes 0: "htrms s H"
and Hop:
"\<And> \<sigma> pl Hl.
  \<lbrakk>list_all2 params (arOfP \<sigma>) pl;
   list_all2 htrms (arOf \<sigma>) Hl;
   list_all2 phi (arOf \<sigma>) Hl\<rbrakk>
  \<Longrightarrow> phi (stOf \<sigma>) (Hop \<sigma> pl Hl)"
shows "phi s H"
proof-
  {fix G
   assume "gtrms s G"
   hence "phi s (clsOf G)"
   proof (induct rule: gtrms_induct)
     case (Gop \<sigma> pl Gl)
     show ?case
     unfolding clsOf_Gop[OF Gop(1) Gop(2)] proof(rule Hop[OF Gop(1)])
       let ?ar = "arOf \<sigma>"
       show "list_all2 phi ?ar (map clsOf Gl)"
       proof (rule list_all2_all_nthI)
         fix i assume i: "i < length ?ar"
         hence "phi (?ar!i) (clsOf (Gl!i))" using Gop(3) by (metis list_all2_conv_all_nth)
         thus "phi (?ar!i) (map clsOf Gl ! i)"
         by (metis Gop(2) i list_all2_lengthD nth_map)
       qed (metis Gop(2) length_map list_all2_lengthD)
     qed(insert Gop(2), simp)
   qed
  }
  thus ?thesis using 0 by (metis Eps clsOf_Eps)
qed

theorem cases_HCL[consumes 1, case_names Hop]:
assumes 0: "htrms s H"
and Hop:
"\<And> \<sigma> pl Hl.
  \<lbrakk>  stOf \<sigma> = s ;
     list_all2 params (arOfP \<sigma>) pl ;
     list_all2 htrms (arOf \<sigma>) Hl ;
     H = Hop \<sigma> pl Hl  \<rbrakk>
  \<Longrightarrow> phi"
shows "phi"
using 0 Hop by induct auto


subsection{* Iteration *}

(* pre-iterator for ground terms: *)
fun giter where
"giter intOp (Gop \<sigma> pl Gl) = intOp \<sigma> pl (map (giter intOp) Gl)"

lemma gtrms_giter:
assumes c: "compat intSt intOp" and 0: "gtrms s G"
shows "intSt s (giter intOp G)"
using 0 apply(induct rule: gtrms_induct)
using c unfolding compat_def apply simp
by (metis list_all2_map2)

lemma intTrm_giter:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)"
and T: "trms s T"
shows
"intTrm intOp intPvar (\<lambda>s x. giter intOp (intVar s x)) T =
 giter intOp (intTrm Gop intPvar intVar T)"
using T apply (induct rule: trms_induct)
apply simp_all
by (smt Ball_set_list_all map_eq_conv o_eq_dest_lhs)

lemma map_intTrm_giter:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)"
and Tl: "list_all2 trms sl Tl"
shows
"map (intTrm intOp intPvar (\<lambda>s x. giter intOp (intVar s x))) Tl =
 map (giter intOp o intTrm Gop intPvar intVar) Tl"
proof-
  have l: "length sl = length Tl" using Tl unfolding list_all2_def by simp
  show ?thesis
  apply(rule nth_equalityI)
  using intTrm_giter[of intPvar intVar _ _ intOp, OF Pvar Var]
      list_all2_nthD[OF Tl] l by auto
qed

lemma satAtm_giter:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. gtrms s (intVar s x)" and
c: "compatAtm atm"
and 0:
"satAtm Gop
       (\<lambda>T1 T2. Geq T1 T2 \<and> giter intOp T1 = giter intOp T2)
       (\<lambda>\<pi> pl Tl. Grel \<pi> pl Tl \<and> intRl \<pi> pl (map (giter intOp) Tl))
       intPvar intVar atm"
shows "satAtm intOp (op =) intRl intPvar (\<lambda> s x. giter intOp (intVar s x)) atm"
proof(cases atm)
  case Pcond
  thus ?thesis using 0 unfolding satAtm_def by auto
next
  case (Eq s T1 T2)
  have T1: "trms s T1" and T2: "trms s T2"
  using c unfolding Eq compatHcl_def compatAtm_def by auto
  show ?thesis unfolding Eq satAtm_def satEq_def apply simp
  unfolding intTrm_giter[OF Pvar Var T1] intTrm_giter[OF Pvar Var T2]
  using 0 unfolding satAtm_def Eq satEq_def by simp
next
  case (Rl \<pi> pxl Tl)
  have pxl: "length pxl = length (rarOfP \<pi>)"
  and Tl: "list_all2 trms (rarOf \<pi>) Tl"
  using c unfolding Rl compatHcl_def compatAtm_def by auto
  show ?thesis unfolding Rl satAtm_def satRl_def apply simp
  unfolding map_intTrm_giter[OF Pvar Var Tl]
  using 0 unfolding satAtm_def Rl satRl_def by simp
qed

lemma Geq_Grel_giter:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows
"(Geq G1 G2 \<longrightarrow> (giter intOp G1 = giter intOp G2))
 \<and>
 (Grel \<pi> pl Gl \<longrightarrow> intRl \<pi> pl (map (giter intOp) Gl))"
proof(induct rule: Geq_Grel.induct)
  case (GeqGop \<sigma> pl Gl1 Gl2)
  hence "length Gl1 = length Gl2" by (metis list_all2_lengthD)
  hence ?case
  unfolding giter.simps using list_all2_nthD[OF GeqGop(4)]
  by (metis (no_types) length_map list_eq_iff_nth_eq nth_map)
next
  case (Eq atml s T1 T2 intPvar intVar)
  let ?iT = "intTrm Gop intPvar intVar"
  let ?iV = "\<lambda> s x. giter intOp (intVar s x)"
  have T1: "trms s T1" and T2: "trms s T2" using compatHCL[OF Eq(1)]
  unfolding compatHcl_def compatAtm_def by auto
  have ssat: "list_all (satAtm intOp (op=) intRl intPvar ?iV) atml"
  unfolding list_all_length proof safe
    fix i assume i: "i < length atml"
    have c: "compatAtm (atml!i)"
    using i compatHCL[OF Eq(1)] unfolding compatHcl_def list_all_length by auto
    have 0:
    "satAtm Gop
       (\<lambda>T1 T2. Geq T1 T2 \<and> giter intOp T1 = giter intOp T2)
       (\<lambda>\<pi> pl Tl. Grel \<pi> pl Tl \<and> intRl \<pi> pl (map (giter intOp) Tl))
       intPvar intVar (atml!i)"
    using i Eq(4) unfolding list_all_length by simp
    show "satAtm intOp (op =) intRl intPvar ?iV (atml!i)"
    using satAtm_giter[OF Eq(2) Eq(3) c 0] .
  qed
  have "\<And> s x. intSt s (?iV s x)" using gtrms_giter[OF c Eq(3)] .
  hence "satAtm intOp (op=) intRl intPvar ?iV (Eq s T1 T2)"
  using ssat sat[OF Eq(1)] Eq(2) unfolding satHcl_def by simp
  hence "satEq intOp (op=) intPvar (\<lambda> s x. giter intOp (intVar s x)) T1 T2"
  unfolding satAtm_def by simp
  thus ?case unfolding satEq_def
  unfolding intTrm_giter[OF Eq(2) Eq(3) T1] intTrm_giter[OF Eq(2) Eq(3) T2] .
next
  case (Rel atml \<pi> pxl Tl intPvar intVar)
  let ?iT = "intTrm Gop intPvar intVar"
  let ?iV = "\<lambda> s x. giter intOp (intVar s x)"
  have pxl: "length pxl = length (rarOfP \<pi>)"
  and Tl: "list_all2 trms (rarOf \<pi>) Tl"
  using compatHCL[OF Rel(1)] unfolding compatHcl_def compatAtm_def by auto
  have ssat: "list_all (satAtm intOp (op=) intRl intPvar ?iV) atml"
  unfolding list_all_length proof safe
    fix i assume i: "i < length atml"
    have c: "compatAtm (atml!i)"
    using i compatHCL[OF Rel(1)] unfolding compatHcl_def list_all_length by auto
    have 0:
    "satAtm Gop
       (\<lambda>T1 T2. Geq T1 T2 \<and> giter intOp T1 = giter intOp T2)
       (\<lambda>\<pi> pl Tl. Grel \<pi> pl Tl \<and> intRl \<pi> pl (map (giter intOp) Tl))
       intPvar intVar (atml!i)"
    using i Rel(4) unfolding list_all_length by simp
    show "satAtm intOp (op =) intRl intPvar ?iV (atml!i)"
    using satAtm_giter[OF Rel(2) Rel(3) c 0] .
  qed
  have "\<And> s x. intSt s (?iV s x)" using gtrms_giter[OF c Rel(3)] .
  hence "satAtm intOp (op=) intRl intPvar ?iV (Rl \<pi> pxl Tl)"
  using ssat sat[OF Rel(1)] Rel(2) unfolding satHcl_def by simp
  hence "satRl intOp intRl intPvar (\<lambda> s x. giter intOp (intVar s x)) \<pi> pxl Tl"
  unfolding satAtm_def by simp
  thus ?case unfolding satRl_def
  unfolding map_intTrm_giter[OF Rel(2) Rel(3) Tl] by simp
next
  case (GeqGop \<sigma> pl Gl1 Gl2)
  have "map (giter intOp) Gl1 = map (giter intOp) Gl2"
  apply(rule nth_equalityI)
    using GeqGop(2,3) unfolding list_all2_def apply fastforce
    using GeqGop(4) unfolding list_all2_conv_all_nth by simp
  thus ?case by simp
next
  case (GeqGrel Gl1 Gl2 \<pi> pl)
  have "map (giter intOp) Gl1 = map (giter intOp) Gl2"
  apply(rule nth_equalityI)
    using GeqGrel unfolding list_all2_def apply fastforce
    using GeqGrel unfolding list_all2_conv_all_nth by simp
  thus ?case using GeqGrel by simp
qed auto

lemma Geq_giter:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
and 0: "Geq G1 G2"
shows "giter intOp G1 = giter intOp G2"
using Geq_Grel_giter[OF c sat] 0 by auto

lemma Grel_giter:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
and 0: "Grel \<pi> pl Gl"
shows "intRl \<pi> pl (map (giter intOp) Gl)"
using Geq_Grel_giter[OF c sat] 0 by auto

lemma giter_respects_GGeq:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "(giter intOp) respects GGeq"
using Geq_giter[OF c sat] unfolding congruent_def by auto

(*   *)
definition "iter intOp = univ (giter intOp)"

lemma iter_clsOf:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "iter intOp (clsOf G) = giter intOp G"
unfolding iter_def clsOf_def apply(rule univ_commute[OF equiv_GGeq])
using giter_respects_GGeq[OF assms] by simp_all

lemma giter_Eps:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "giter intOp (EpsSet H) = iter intOp H"
using iter_clsOf[OF c sat] by (metis iter_def univ_def)

lemma map_iter_clsOf:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "map ((iter intOp) o clsOf) Gl = map (giter intOp) Gl"
using iter_clsOf[OF assms]
by (metis map_ext o_eq_dest_lhs splitE)

lemma map_giter_Eps:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "map ((giter intOp) o EpsSet) Hl = map (iter intOp) Hl"
using giter_Eps[OF assms]
by (metis map_ext o_eq_dest_lhs splitE)

lemma iter_intSt:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
and H: "htrms s H"
shows "intSt s (iter intOp H)"
using gtrms_giter[OF c] sat H by (metis Eps iter_def univ_def)

lemma compat_Hop:
"compat htrms Hop"
unfolding compat_def
by (metis EpsL Hop_def clsOf gtrms.simps)

theorem iter_Hop:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
shows "iter intOp (Hop \<sigma> pl Hl) = intOp \<sigma> pl (map (iter intOp) Hl)"
using map_giter_Eps[OF c sat]
by (metis (no_types) Hop_def List.map_map c giter.simps iter_clsOf sat)

theorem iter_Hrel:
assumes c: "compat intSt intOp"
and sat: "\<And> hcl. hcl \<in> HCL \<Longrightarrow> satHcl intSt intOp (op=) intRl hcl"
and Hrel: "Hrel \<pi> pl Hl"
shows "intRl \<pi> pl (map (iter intOp) Hl)"
proof-
  let ?Gl = "map EpsSet Hl"
  have 0: "Grel \<pi> pl ?Gl" unfolding Grel_Eps using Hrel .
  show ?thesis using Grel_giter[OF c sat 0] map_giter_Eps[OF c sat, of Hl] by auto
qed

thm sat_HCL
thm induct_HCL
thm iter_intSt
thm iter_Hop
thm iter_Hrel
thm cases_HCL


end (* context HornTheory *)



end
