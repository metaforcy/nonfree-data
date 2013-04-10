theory NonFree
imports "SetoidIsotrans" "~~/src/HOL/Library/FuncSet" Equiv_Relation2
begin


section{* Combinators *}



ML {*
  Syntax.read_term @{context} "x";
  Specification.read_spec [(Binding.name "bla", NONE, NoSyn)]
    [(Attrib.empty_binding, "x = x")] @{context};

  Specification.read_spec [(Binding.name "x", SOME "'a list", NoSyn)]
    [(Attrib.empty_binding, "x = x")] @{context};

*}

ML {*
  val myloc = Binding.name "blalocale"
  val full_myloc = Sign.full_name @{theory} myloc
*}

setup {*
  (* eher Expression.add_locale nutzen *)
  Locale.register_locale myloc ([], []) (NONE, []) (NONE, NONE) [] [] [] []
*}

ML {*
  val lthy = Named_Target.init I full_myloc @{theory};
  val defbnd = Binding.name "myconst";
  val (_, lthy2) = lthy
    |> Local_Theory.define ((defbnd, NoSyn), ((Thm.def_binding defbnd, []),
         @{term "0"}));
  val thy2 = ProofContext.theory_of lthy2;
  (* ... *)
  val ctxt2 = ProofContext.init_global thy2;
  val ctxt3 = ctxt2
    |> Context.proof_map (Locale.activate_facts NONE (full_myloc, Morphism.identity));
  val th = ProofContext.get_thm ctxt3 (Thm.def_binding defbnd |> Binding.name_of);
  prop_of th;
  val _ = Output.writeln (Display.string_of_thm ctxt3 th)

*}




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
apply fastsimp
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

lemma in_product_list_all2[simp]:
"ys \<in> product (map f xs) \<longleftrightarrow> list_all2 f xs ys"
unfolding list_all2_product Collect_def ..

lemma product_list_all2:
"product (map f xs) = list_all2 f xs"
apply(rule ext) unfolding in_product_list_all2[THEN sym] mem_def ..



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
      using compatHCL[OF Rel(1)] unfolding compatHcl_def compatAtm_def apply fastsimp
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
definition "htrms s H \<longleftrightarrow> H \<in> UNIV // GGeq \<and> gtrms s (Eps H)"
definition "Hop \<sigma> pl Hl = clsOf (Gop \<sigma> pl (map Eps Hl))"
definition "Hrel \<pi> pl Hl \<longleftrightarrow> Grel \<pi> pl (map Eps Hl)"

(* Pointwise facts: *)
lemma Geq_Eps_clsOf[simp]:
"Geq (Eps (clsOf G)) G"
using assms unfolding clsOf_def
using Eps_proj[OF equiv_GGeq] by simp

lemma Geq_Eps_clsOf2[simp]:
"Geq G (Eps (clsOf G))"
by (metis Geq_Eps_clsOf Sym)

lemma clsOf:
assumes "gtrms s G"
shows "htrms s (clsOf G)"
unfolding htrms_def apply default
  unfolding clsOf_def proj_in_iff[OF equiv_GGeq] apply fastsimp
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
  by (smt clsOf htrms_def)

lemma Eps[simp]:
assumes "htrms s H"
shows "gtrms s (Eps H)"
using assms unfolding htrms_def by auto

lemma htrms_in[simp]:
assumes "htrms s H"
shows "H \<in> UNIV // GGeq"
using assms unfolding htrms_def by auto

lemma clsOf_Eps[simp]:
assumes "htrms s H"
shows "clsOf (Eps H) = H"
unfolding clsOf_def apply(rule proj_Eps[OF equiv_GGeq]) using htrms_in[OF assms] .

lemma clsOf_surj:
assumes "htrms s H"
shows "\<exists> G. gtrms s G \<and> clsOf G = H"
apply(rule exI[of _ "Eps H"]) using assms by auto

lemma clsOf_Geq[simp]:
"clsOf G1 = clsOf G2 \<longleftrightarrow> Geq G1 G2"
unfolding clsOf_def using proj_iff[OF equiv_GGeq] by auto

lemma Geq_Eps[simp]:
assumes "htrms s H1" and "htrms s H2"
shows "Geq (Eps H1) (Eps H2) \<longleftrightarrow> H1 = H2"
by (metis assms clsOf_Eps clsOf_Geq)

lemma Geq_inj[simp]:
assumes "htrms s H1" and "htrms s H2"
shows "Eps H1 = Eps H2 \<longleftrightarrow> H1 = H2"
proof-
  have "Eps H1 = Eps H2 \<Longrightarrow> Geq (Eps H1) (Eps H2)"
  by (metis Geq_Eps assms)
  hence "Eps H1 = Eps H2 \<Longrightarrow> H1 = H2" using Geq_Eps[OF assms] by blast
  thus ?thesis by blast
qed

lemma Eps_Geq_surj:
assumes "gtrms s G"
shows "\<exists> H. htrms s H \<and> Geq (Eps H) G"
apply(rule exI[of _ "clsOf G"]) using assms by auto

lemma Eps_Geq_surj2:
assumes "gtrms s G"
shows "\<exists> H. htrms s H \<and> Geq G (Eps H)"
using Eps_Geq_surj[OF assms] by (metis Sym)

(* List facts: *)
lemmas map_map = "map.compositionality"
declare zip_same[simp]

lemma Geq_Eps_clsOfL[simp]:
"list_all2 Geq (map Eps (map clsOf Gl)) Gl"
unfolding map_map list_all2_map1 apply(rule list_all2I) by auto

lemma Geq_Eps_clsOfL_comp[simp]:
"list_all2 Geq (map (Eps o clsOf) Gl) Gl"
by (metis Geq_Eps_clsOfL List.map_map)

lemma Geq_Eps_clsOf2L[simp]:
"list_all2 Geq Gl (map Eps (map clsOf Gl))"
unfolding map_map list_all2_map2 apply(rule list_all2I) by auto

lemma Geq_Eps_clsOf2L_comp[simp]:
"list_all2 Geq Gl (map (Eps o clsOf) Gl)"
by (metis Geq_Eps_clsOf2L List.map_map)

lemma htrms_clsOfL[simp]:
"list_all2 htrms sl (map clsOf Gl) \<longleftrightarrow> list_all2 gtrms sl Gl"
unfolding list_all2_def set_zip apply simp apply safe
apply (metis htrms_clsOf nth_map) by auto

lemma EpsL[simp]:
assumes "list_all2 htrms sl Hl"
shows "list_all2 gtrms sl (map Eps Hl)"
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
shows "map clsOf (map Eps Hl) = Hl"
using assms unfolding map_map list_all2_def set_zip
apply(intro nth_equalityI, simp)
by (smt map_map assms clsOf_Eps length_map list_all2_conv_all_nth nth_map)

lemma clsOf_EpsL_comp[simp]:
assumes "list_all2 htrms sl Hl"
shows "map (clsOf o Eps) Hl = Hl"
by (metis assms clsOf_EpsL map_map)

lemma clsOf_surjL:
assumes "list_all2 htrms sl Hl"
shows "\<exists> Gl. list_all2 gtrms sl Gl \<and> map clsOf Gl = Hl"
apply(rule exI[of _ "map Eps Hl"]) using assms by auto

lemma clsOf_GeqL[simp]:
"map clsOf Gl1 = map clsOf Gl2 \<longleftrightarrow> list_all2 Geq Gl1 Gl2"
unfolding list_eq_iff_nth_eq list_all2_def set_zip apply simp
apply(rule conj_cong)
  apply fastsimp
  by (metis clsOf_Geq nth_map)

lemma Geq_EpsL[simp]:
assumes "list_all2 htrms sl Hl1" and "list_all2 htrms sl Hl2"
shows "list_all2 Geq (map Eps Hl1) (map Eps Hl2) \<longleftrightarrow> Hl1 = Hl2"
by (metis assms clsOf_EpsL clsOf_GeqL)

lemma Geq_injL[simp]:
assumes "list_all2 htrms sl Hl1" and "list_all2 htrms sl Hl2"
shows "map Eps Hl1 = map Eps Hl2 \<longleftrightarrow> Hl1 = Hl2"
proof-
  have "map Eps Hl1 = map Eps Hl2 \<Longrightarrow> list_all2 Geq (map Eps Hl1) (map Eps Hl2)"
  by (metis Geq_EpsL assms)
  hence "map Eps Hl1 = map Eps Hl2 \<Longrightarrow> Hl1 = Hl2" using Geq_EpsL[OF assms] by blast
  thus ?thesis by blast
qed

lemma Eps_Geq_surjL:
assumes "list_all2 gtrms sl Gl"
shows "\<exists> Hl. list_all2 htrms sl Hl \<and> list_all2 Geq (map Eps Hl) Gl"
apply(rule exI[of _ "map clsOf Gl"]) using assms by auto

lemma Eps_Geq_surj2L:
assumes "list_all2 gtrms sl Gl"
shows "\<exists> Hl. list_all2 htrms sl Hl \<and> list_all2 Geq Gl (map Eps Hl)"
apply(rule exI[of _ "map clsOf Gl"]) using assms by auto

(* Operations:  *)
lemma clsOf_Gop:
assumes pl: "list_all2 params (arOfP \<sigma>) pl" and Gl: "list_all2 gtrms (arOf \<sigma>) Gl"
shows "clsOf (Gop \<sigma> pl Gl) = Hop \<sigma> pl (map clsOf Gl)"
unfolding Hop_def unfolding clsOf_Geq proof (rule GeqGop)
  show "list_all2 gtrms (arOf \<sigma>) (map Eps (map clsOf Gl))"
  unfolding map_map list_all2_map2 proof(rule list_all2_all_nthI, unfold comp_def)
    fix i assume i: "i < length (arOf \<sigma>)" let ?ar = "arOf \<sigma>"
    have "gtrms (?ar ! i) (Gl ! i)" by (metis Gl i list_all2_nthD)
    moreover have "Geq (Gl ! i) (Eps (clsOf (Gl ! i)))" by (metis Geq_Eps_clsOf2)
    ultimately show "gtrms (?ar ! i) (Eps (clsOf (Gl ! i)))" by (metis Eps clsOf)
  qed (metis Gl list_all2_conv_all_nth)
qed (insert assms, auto)

lemma Geq_Eps_Hop:
"Geq (Eps (Hop \<sigma> pl Hl)) (Gop \<sigma> pl (map Eps Hl))"
unfolding Hop_def by simp

lemma Geq_Eps_Hop2:
"Geq (Gop \<sigma> pl (map Eps Hl)) (Eps (Hop \<sigma> pl Hl))"
unfolding Hop_def by simp

(* Relations: *)
lemma Hrel_clsOf[simp]:
"Hrel \<pi> pl (map clsOf Gl) \<longleftrightarrow> Grel \<pi> pl Gl"
unfolding Hrel_def apply(rule GeqGrel2) by simp

lemma Grel_Eps[simp]:
"Grel \<pi> pl (map Eps Hl) \<longleftrightarrow> Hrel \<pi> pl Hl"
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

lemma intTrm_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and T: "trms s T"
shows
"intTrm Hop intPvar intVar T =
 clsOf (intTrm Gop intPvar (\<lambda> xs x. Eps (intVar xs x)) T)"
using T proof (induct rule: trms_induct)
  case (Op \<sigma> pxl Tl)
  let ?arP = "arOfP \<sigma>"  let ?ar = "arOf \<sigma>"
  let ?iV = "\<lambda> xs x. Eps (intVar xs x)"
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
      have "Geq (Eps (?hiT (Tl!i))) (?giT (Tl!i))"
      by (smt 0 Geq_Eps_clsOf2 Tl clsOf_Geq i length_map list_all2_lengthD nth_map)
      moreover have "gtrms (?ar!i) (Eps (?hiT (Tl!i)))"
      by (smt Eps Pvar Tl Var calculation clsOf_Geq compat_gtrms
              htrms_clsOf i intTrm_intSt list_all2_nthD)
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
  have 0: "\<And> xs x. Geq (intVar xs x) (Eps (iV xs x))"
  by (metis Geq_Eps_clsOf2 Sym iV_def)
  have 1: "Geq (intTrm Gop intPvar intVar T)
               (intTrm Gop intPvar (\<lambda> xs x. Eps (iV xs x)) T) "
  using intTrm_Gop_Geq[OF Pvar Var 0 T] .
  show ?thesis
  using intTrm_Hop[OF Pvar VVar T] unfolding iV_def apply simp
  by (smt Geq_Eps_clsOf2 Pvar Sym T Var intTrm_Gop_Geq)
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
 Grel \<pi> pl (map (intTrm Gop intPvar (\<lambda> xs x. Eps (intVar xs x))) Tl)"
unfolding Hrel_def map_map
apply(rule GeqGrel2) proof(rule list_all2_all_nthI, simp_all)
  fix i assume i: "i < length Tl"
  let ?hiT = "intTrm Hop intPvar intVar"
  let ?giT = "intTrm Gop intPvar (\<lambda>xs x. Eps (intVar xs x))"
  have "?hiT (Tl!i) = clsOf (?giT (Tl!i))"
  apply(rule intTrm_Hop[OF Pvar Var, of "rarOf \<pi>!i"])
  by (metis Tl i list_all2_nthD2)
  thus "Geq (Eps (?hiT (Tl!i))) (?giT (Tl!i))" by (metis Geq_Eps_clsOf2 Sym)
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
  have 0: "\<And> xs x. Geq (Eps (iV xs x)) (intVar xs x)"
  by (metis Geq_Eps_clsOf2 Sym iV_def)
  have "?L \<longleftrightarrow> Grel \<pi> pl (map (intTrm Gop intPvar (\<lambda> xs x. Eps (iV xs x))) Tl)"
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
 satEq Gop Geq intPvar (\<lambda> xs x. Eps (intVar xs x)) T1 T2"
unfolding satEq_def intTrm_Hop[OF Pvar Var T1] intTrm_Hop[OF Pvar Var T2] by simp

lemma satRl_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and Tl: "list_all2 trms (rarOf \<pi>) Tl"
shows
"satRl Hop Hrel intPvar intVar \<pi> pxl Tl \<longleftrightarrow>
 satRl Gop Grel intPvar (\<lambda> xs x. Eps (intVar xs x)) \<pi> pxl Tl"
unfolding satRl_def using Hrel_intTrm_Hop[OF assms]
by (smt Eps Grel_intTrm_Gop Grel_params Hrel_def Hrel_intTrm_Hop Pvar Tl Var clsOf_Geq)

lemma satAtm_Hop:
assumes Pvar: "\<And> ps px. params ps (intPvar ps px)" and
Var: "\<And>s x. htrms s (intVar s x)" and
c: "compatAtm atm"
shows
"satAtm Hop (op=) Hrel intPvar intVar atm \<longleftrightarrow>
 satAtm Gop Geq Grel intPvar (\<lambda> xs x. Eps (intVar xs x)) atm"
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
  let ?iV = "\<lambda> xs x. Eps (intVar xs x)"
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
  \<lbrakk>list_all2 params (arOfP \<sigma>) pl;
   list_all2 htrms (arOf \<sigma>) Hl;
   H = Hop \<sigma> pl Hl\<rbrakk>
  \<Longrightarrow> phi H"
shows "phi H"
using 0 Hop by induct auto

theorem nchotomy_HCL:
"htrms s H \<Longrightarrow>
 \<exists> \<sigma> pl Hl.
   list_all2 params (arOfP \<sigma>) pl \<and>
   list_all2 htrms (arOf \<sigma>) Hl \<and>
   H = Hop \<sigma> pl Hl"
using cases_HCL by blast


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
    using GeqGop(2,3) unfolding list_all2_def apply fastsimp
    using GeqGop(4) unfolding list_all2_conv_all_nth by simp
  thus ?case by simp
next
  case (GeqGrel Gl1 Gl2 \<pi> pl)
  have "map (giter intOp) Gl1 = map (giter intOp) Gl2"
  apply(rule nth_equalityI)
    using GeqGrel unfolding list_all2_def apply fastsimp
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
shows "giter intOp (Eps H) = iter intOp H"
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
shows "map ((giter intOp) o Eps) Hl = map (iter intOp) Hl"
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
  let ?Gl = "map Eps  Hl"
  have 0: "Grel \<pi> pl ?Gl" unfolding Grel_Eps using Hrel .
  show ?thesis using Grel_giter[OF c sat 0] map_giter_Eps[OF c sat, of Hl] by auto
qed

thm sat_HCL
thm induct_HCL
thm iter_intSt
thm iter_Hop
thm iter_Hrel
thm cases_HCL
thm nchotomy_HCL


end (* context HornTheory *)









fun holdsAll where
  "holdsAll phi [] = True"
| "holdsAll phi (Cons x xs) = (phi x & holdsAll phi xs)"

lemma [MR]: "
  holdsAll phi [] rewto True  " by (simp add: rewto_const_def)
lemma [MR]: "
  holdsAll phi (Cons x xs) rewto (phi x & holdsAll phi xs)  " by (simp add: rewto_const_def)


lemma holdsAll_char: "holdsAll phi xs = (ALL x : set xs. phi x)"
  apply (induct xs)
  by simp+

fun holdsAll2 where
  "holdsAll2 R [] ys = (ys = [])"
| "holdsAll2 R (Cons x xs) ys = (EX y ys'. ys = Cons y ys'  &  R x y  &  holdsAll2 R xs ys')"

lemma [MR]: "
  holdsAll2 R Nil pNil rewto True " by (simp add: rewto_const_def pNil_def)
lemma [MR]: "
  holdsAll2 R (Cons x xs) (pCons A As y ys) rewto (R x y & holdsAll2 R xs ys)  "
  by (simp add: rewto_const_def pCons_def)

lemma holdsAll2_char: "length xs = length ys ==> holdsAll2 R xs ys = (ALL (x,y) : set (zip xs ys). R x y)"
  apply (induct xs arbitrary: ys)
  apply simp+
  oops


lemma [simp]: "map2 f Nil Nil = Nil" by (simp add: map2_def)
lemma [simp]: "map2 f (Cons x xs) (Cons y ys) = Cons (f x y) (map2 f xs ys)" by (simp add: map2_def)

lemma [MR]: "
  map2 f Nil Nil rewto Nil " by (simp add: rewto_const_def)
lemma [MR]: "
  map2 f (Cons x xs) (Cons y ys) rewto Cons (f x y) (map2 f xs ys)" by (simp add: rewto_const_def)

lemma [MR]: "
  map f Nil rewto Nil " by (simp add: rewto_const_def)
lemma [MR]: "
  map f (Cons x xs) rewto Cons (f x) (map f xs)" by (simp add: rewto_const_def)

lemma [MR]: "
  [] @ ys  rewto  ys " by (simp add: rewto_const_def)
lemma [MR]: "
  (Cons x xs) @ ys  rewto  (Cons x (xs @ ys)) " by (simp add: rewto_const_def)


lemma [MR]: "
  length Nil rewto 0  "  by (simp add: rewto_const_def)
lemma [MR]: "
  length (Cons x xs) rewto Suc (length xs)  "  by (simp add: rewto_const_def)

lemma [MR]: "
  zip [] [] rewto []  " by (simp add: rewto_const_def)
lemma [MR]: "
  zip (Cons x xs) (Cons y ys) rewto Cons (x, y) (zip xs ys)  " by (simp add: rewto_const_def)


(* implicit, so runs always, no need for tracking of rewto judgement dependency *)
lemma [impl_frule]: "
  enum_datatype_constreq_rew n t1 t2
  ==> brule(  t1 rewto t2  )  " by (simp add: brule_const_def rewto_const_def enum_datatype_constreq_rew_def)

lemma [MR]: "
  True & P rewto P  " by (simp add: rewto_const_def)
lemma [MR]: "
  P & True rewto P  " by (simp add: rewto_const_def)
lemma [MR]: "
  P & False rewto False  " by (simp add: rewto_const_def)
lemma [MR]: "
  False & P rewto False  " by (simp add: rewto_const_def)


definition
  matches_const ("_ matches _") where
  [MRjud 1 1]: "t1 matches t2 == (t1 == t2)"
lemma [MR]: "t matches t" by (simp add: matches_const_def)


lemma [MR]: "  ((x :: nat) = x) rewto True  " by (simp add: rewto_const_def)
lemma [MR]: "  (Suc x = 0) rewto False " by (simp add: rewto_const_def)
lemma [MR]: "  (0 = Suc x) rewto False  " by (simp add: rewto_const_def)
lemma [MR]: "  (Suc x = Suc y) rewto (x = y)   " by (simp add: rewto_const_def)

lemma [MR]: "  fst (a, b) rewto a   " by (simp add: rewto_const_def)
lemma [MR]: "  snd (a, b) rewto b   " by (simp add: rewto_const_def)












(* adapted from classical.ML *)
ML {*
fun some_rule_tac ctxt facts = SUBGOAL (fn (goal, i) =>
  let
    val [rules1, rules2, rules4] = Context_Rules.find_rules false facts goal ctxt;
    val {xtra_netpair, ...} = Classical.claset_of ctxt |> Classical.rep_cs;
    val rules3 = Context_Rules.find_rules_netpair true facts goal xtra_netpair;
    val rules = rules1 @ rules2 @ rules3 @ rules4 @ [@{thm Pure.conjunctionI}];
    val ruleq = Drule.multi_resolves facts rules;
  in
    Method.trace ctxt rules;
    fn st => Seq.maps (fn rule => Tactic.rtac rule i st) ruleq
  end)
  THEN_ALL_NEW Goal.norm_hhf_tac;
*}
method_setup triv = {*
  Attrib.thms >> (fn _ => fn ctxt => METHOD (HEADGOAL o K (some_rule_tac ctxt [])))
*} ""






(* usage syntax via declarations on pseudo-terms
   without logical significance *)

datatype tyco = TycoEmb nat
datatype tyvar = TypvarEmb nat
datatype oper = OperEmb nat
datatype logop = LogopEmb nat
datatype rel = RelEmb nat
datatype pcond = PcondEmb nat

datatype kind = ExtType | IntType | KindArr kind kind
datatype type = Tyco tyco | TypeApp type type | TypeArr type type | TypeVar tyvar
datatype terms = App terms terms | Oper oper | PCond pcond | Rel rel
  | LogicOper logop | PseudoVar nat | Quant type "(nat => terms)"


abbreviation
  kind_arr :: "kind => kind => kind" (infixr "=K=>" 5)
where
  "kind_arr == KindArr"
abbreviation
  type_arr :: "type => type => type" (infixr "=T=>" 5)
where
  "type_arr == TypeArr"


definition
  bool :: tyco
where
  "bool == TycoEmb 0"

abbreviation
  type_app :: "type => type => type" (infixl "**" 20)
where
  "type_app == TypeApp"


(* Dmitriy saves the syntax.
   Non-parametric coerctions, such as App would be even better *)
declare [[coercion_enabled]]
declare [[coercion "TypeVar :: tyvar => type" ]]
declare [[coercion "Tyco :: tyco => type" ]]
declare [[coercion "Oper :: oper => terms"]]
declare [[coercion "PCond :: pcond => terms"]]
declare [[coercion "Rel :: rel => terms"]]
declare [[coercion "LogicOper :: logop => terms"]]
declare [[coercion "PseudoVar :: nat => terms"]]




abbreviation
  app :: "terms => terms => terms" (infixl "$" 500)
where
  "app == App"



definition
  implication_logop :: logop where
  "implication_logop == LogopEmb 0"
definition
  implication :: "terms => terms => terms" (infixr "--->" 20) where
  "implication P Q == implication_logop $ P $ Q"

definition
  equality_logop :: logop where
  "equality_logop == LogopEmb 0"
definition
  equality :: "terms => terms => terms" (infixl "===" 50) where
  "equality x y == equality_logop $ x $ y"


syntax
  "_Quant" :: "pttrn => type => terms => terms" ("(3QUANT _:_./ _)" [0, 0, 10] 10)
translations
  "QUANT x:T. P" == "CONST Quant T (% x. P)"

ML {*
  @{term "QUANT x:bool. x ---> x"}
*}

definition
  extract_tyco :: "type => tyco => bool" where
  [MRjud 1 1]: "extract_tyco T k == True"
lemma extract_tycoI[intro]: "extract_tyco T k" by (simp add: extract_tyco_def)

lemma [MR]: "  extract_tyco T k ==>
   extract_tyco (TypeApp T T2) k  " ..
lemma [MR]: "
   extract_tyco (Tyco k) k " ..




(* well-formedness judgements hardly used ATM *)
definition
  wf_decl_tyco :: "tyco => kind => bool" where
  [MRjud 2 0]: "wf_decl_tyco k K == True"
definition
  wf_decl_tyinterpr :: "type => 'a itself => bool" where
  [MRjud 2 0]: "wf_decl_tyinterpr T tau == True"

definition
  wf_decl_oper :: "oper => type => bool" where
  [MRjud 2 0]: "wf_decl_oper c T == True"
definition
  wf_decl_rel :: "rel => type => bool" where
  [MRjud 2 0]: "wf_decl_rel r T == True"
definition
  wf_decl_pcond :: "pcond => type => bool" where
  [MRjud 2 0]: "wf_decl_pcond r T == True"
definition
  wf_decl_pcond_interpr :: "pcond => 'a => bool" where
  [MRjud 2 0]: "wf_decl_pcond_interpr p x == True"
definition
  wf_decl_hcl :: "'a => terms => bool" where
  [MRjud 2 0]: "wf_decl_hcl n P == True"

lemma wf_decl_tycoI [intro]: "wf_decl_tyco k K" by (simp add: wf_decl_tyco_def)
lemma wf_decl_tyinterprI [MR, intro]: "wf_decl_tyinterpr T tau" by (simp add: wf_decl_tyinterpr_def)
  (* TODO: check that type constructors occur in T only applied exactly to the declared type variables in
      the given order *)
lemma wf_decl_operI [MR, intro]: "wf_decl_oper c T" by (simp add: wf_decl_oper_def)
lemma wf_decl_relI [MR, intro]: "wf_decl_rel r T" by (simp add: wf_decl_rel_def)
lemma wf_decl_pcondI [MR, intro]: "wf_decl_pcond r T" by (simp add: wf_decl_pcond_def)
lemma wf_decl_pcond_interprI [MR, intro]: "wf_decl_pcond_interpr p x" by (simp add: wf_decl_pcond_interpr_def)
lemma wf_decl_hclI [MR, intro]: "wf_decl_hcl n P" by (simp add: wf_decl_hcl_def)

definition
  valid_kind :: "kind => bool" where
  [MRjud 1 0]: "valid_kind x == True"
lemma valid_kindI [intro]: "valid_kind K" by (simp add: valid_kind_def)



lemma [MR]: "
  valid_kind ExtType  " ..

lemma [MR]: "
  valid_kind IntType  " ..

lemma [MR]: "    valid_kind K ==>
  valid_kind (ExtType =K=> K)  " ..



lemma [MR]: "  valid_kind K ==>
  wf_decl_tyco k K  " ..




definition
  decl_tyvars :: "unit => tyvar list => bool" where
  [MRjud 1 1]: "decl_tyvars x alphas == True"
definition
  decl_tyco :: "tyco => kind => bool" ("_ tycohaskind _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_tyco_jud"]: "decl_tyco k K == True"
definition
  decl_tyinterpr :: "type => 'a itself => bool" ("_ tyinterpr _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_tyinterpr_jud"]: "decl_tyinterpr T tau == True"

definition
  decl_oper :: "oper => type => bool" ("_ operhasty _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_oper_jud"]: "decl_oper c T == True"
definition
  decl_rel :: "rel => type => bool" ("_ relhasty _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_rel_jud"]: "decl_rel r T == True"
definition
  decl_pcond :: "pcond => type => bool" ("_ pcondhasty _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_pcond_jud"]: "decl_pcond r T == True"
definition
  decl_pcond_interpr :: "pcond => 'a => bool" ("_ pcondinterpr _" 20) where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_pcond_interpr_jud"]: "decl_pcond_interpr p x == True"
definition
  decl_hcl :: "'a => terms => bool" where
  [MRjud 1 1 wfjud: "NonFree.wf_decl_hcl_jud"]: "decl_hcl n P == True"

lemma decl_tyvarsI [intro]: "decl_tyvars () alphas" by (simp add: decl_tyvars_def)
lemma decl_tycoI [intro]: "decl_tyco k K" by (simp add: decl_tyco_def)
lemma decl_tyinterprI [intro]: "decl_tyinterpr T tau" by (simp add: decl_tyinterpr_def)
lemma decl_operI [intro]: "decl_oper c T" by (simp add: decl_oper_def)
lemma decl_relI [intro]: "decl_rel r T" by (simp add: decl_rel_def)
lemma decl_pcondI [intro]: "decl_pcond r T" by (simp add: decl_pcond_def)
lemma decl_pcond_interprI [intro]: "decl_pcond_interpr p x" by (simp add: decl_pcond_interpr_def)
lemma decl_hclI [intro]: "decl_hcl n P" by (simp add: decl_hcl_def)


lemma decl_pcond_interpr_easyI: "p == p ==> x == x ==> decl_pcond_interpr p x"
  by (simp add: decl_pcond_interpr_def)
lemma decl_hcl_easyI: "n == n ==> P == P ==> decl_hcl n P" by (simp add: decl_hcl_def)
lemma decl_tyinterpr_easyI: "T == T ==> tau == tau ==> decl_tyinterpr T tau"
  by (simp add: decl_tyinterpr_def)




definition
  has_kind :: "type => kind => bool" ("_ haskind _" 20) where
  [MRjud 1 1]: "has_kind T k == True"
lemma has_kindI [intro]: "has_kind T k" by (simp add: has_kind_def)

definition
  isatomkind :: "kind => bool" where
  [MRjud 1 0]: "isatomkind k == True"
lemma isatomkindI [intro]: "isatomkind k" by (simp add: isatomkind_def)

definition
  extpred :: "type => bool"  where
  [MRjud 1 0]: "extpred T == True"
lemma extpredI [intro]: "extpred T" by (simp add: extpred_def)

definition
  has_type :: "terms => type => bool" ("_ hastype _" 20) where
  [MRjud 1 1]: "has_type t T == True"
lemma has_typeI [intro]: "has_type t T" by (simp add: has_type_def)


definition
  calc_op_ar :: "type => userar => type list => type list => type => bool" where
  [MRjud 1 4]: "calc_op_ar T uar par ar s == True"
lemma calc_op_arI [intro]: "calc_op_ar T uar par ar s" by (simp add: calc_op_ar_def)

definition
  calc_rel_ar :: "type => userar => type list => type list => bool"  where
  [MRjud 1 3]: "calc_rel_ar T uar par ar == True"
lemma calc_rel_arI [intro]: "calc_rel_ar T uar par ar" by (simp add: calc_rel_ar_def)

definition
  calc_pcond_par :: "type => type list => bool"  where
  [MRjud 1 1]: "calc_pcond_par T par == True"
lemma calc_pcond_parI[intro]: "calc_pcond_par T par" by (simp add: calc_pcond_par_def)





definition
  process_tyvars :: "tyvar list => bool" where
  [MRjud 1 0]: "process_tyvars alphas == True"
lemma process_tyvarsI[intro]: "process_tyvars alphas" by (simp add: process_tyvars_def)

lemma [expl_frule]: "
  decl_tyvars () alphas
  ==> process_tyvars alphas  " ..

lemma [expl_frule]: "
  process_tyvars (Cons alpha alphas)
  ==>  alpha haskind ExtType  &&&  process_tyvars alphas  " apply triv by rule+


lemma [MR]: "    k tycohaskind K ==>
  k haskind K  " ..

lemma [MR]: "[|  T haskind (ExtType =K=> K)  ;  T2 haskind ExtType  |] ==>
  (T ** T2) haskind K  " ..

lemma [MR]: "  isatomkind ExtType  " ..
lemma [MR]: "  isatomkind IntType  " ..

(* direkt als haskind wuerde Charakterisierung von benoetigten Sorten, Parameter in enum_sorts_and_params stoeren *)
lemma [MR]: "[|  T haskind ExtType  ;  extpred T2  |] ==>
  extpred (T =T=> T2) " ..
lemma [MR]:  "
  extpred bool " ..

lemma [MR]: "   c  operhasty T ==>
  c hastype T  " ..

lemma [MR]: "[|   t1 hastype (T1 =T=> T2)   ;   t2 hastype T1   |] ==>
  (t1 $ t2) hastype T2  " ..



lemma [MR]: "    T haskind IntType ==>
  calc_op_ar T [] [] [] T  " ..

lemma [MR]: "[|  T1 haskind IntType  ;  calc_op_ar T2 uar parTs arTs sT  |] ==>
  calc_op_ar (T1 =T=> T2) (Cons Intern uar) parTs (Cons T1 arTs) sT  " ..

lemma [MR]: "[|  try (T1 haskind ExtType)  ;   calc_op_ar T2 uar parTs arTs sT  |] ==>
  calc_op_ar (T1 =T=> T2) (Cons Param uar) (Cons T1 parTs) arTs sT  " ..



lemma [MR]: "
  calc_rel_ar bool [] [] []  " ..

lemma [MR]: "[|  T1 haskind IntType  ;   calc_rel_ar T2 uar parTs arTs  |] ==>
  calc_rel_ar (T1 =T=> T2) (Cons Intern uar) parTs (Cons T1 arTs)  " ..

lemma [MR]: "[|  try (T1 haskind ExtType)  ;   calc_rel_ar T2 uar parTs arTs  |] ==>
  calc_rel_ar (T1 =T=> T2) (Cons Param uar) (Cons T1 parTs) arTs  " ..



lemma [MR]: "[|  try (T1 haskind ExtType)  ;   calc_pcond_par T2 parTs  |] ==>
  calc_pcond_par (T1 =T=> T2) (Cons T1 parTs)  " ..

lemma [MR]: "
  calc_pcond_par bool []  " ..




definition
  enum_sorts_and_params :: "type => bool" where
  [MRjud 1 0]: "enum_sorts_and_params T == True"

lemma enum_sorts_and_paramsI[intro]: "enum_sorts_and_params T"
  by (simp add: enum_sorts_and_params_def)

definition
  needs_sort :: "type => bool" where
  [MRjud 1 0]: "needs_sort T == True"

lemma needs_sortI[intro]: "needs_sort T"
  by (simp add: needs_sort_def)

definition
  needs_param :: "type => bool" where
  [MRjud 1 0]: "needs_param T == True"

lemma needs_paramI[intro]: "needs_param T"
  by (simp add: needs_param_def)

definition
  coll_needs_sort :: "unit => proplist => prop" where
  [MRcolljud "NonFree.needs_sort_jud"]: "coll_needs_sort x L == Trueprop True"

definition
  coll_needs_param :: "unit => proplist => prop" where
  [MRcolljud "NonFree.needs_param_jud"]: "coll_needs_param x L == Trueprop True"

definition
  coll_decl_oper :: "unit => proplist => prop" where
  [MRcolljud "NonFree.decl_oper_jud"]: "coll_decl_oper x L == Trueprop True"

definition
  coll_decl_rel :: "unit => proplist => prop" where
  [MRcolljud "NonFree.decl_rel_jud"]: "coll_decl_rel x L == Trueprop True"

definition
  coll_decl_pcond_interpr :: "unit => proplist => prop" where
  [MRcolljud "NonFree.decl_pcond_interpr_jud"]: "coll_decl_pcond_interpr x L == Trueprop True"


definition sorts_enum_name :: "nat"
where "sorts_enum_name = 0"
definition psorts_enum_name :: "nat"
where "psorts_enum_name = 0"
definition opsyms_enum_name :: "nat"
where "opsyms_enum_name = 0"







definition
  def_sort_type_map :: "proplist => 'a list => bool" where
  [MRjud 2 0]: "def_sort_type_map L Cs == True"
lemma def_sort_type_map[intro]: "def_sort_type_map L Cs" by (simp add: def_sort_type_map_def)

definition
  def_psort_type_map :: "proplist => 'a list => bool" where
  [MRjud 2 0]: "def_psort_type_map L Cs == True"
lemma def_psort_type_map[intro]: "def_psort_type_map L Cs" by (simp add: def_psort_type_map_def)

definition
  sort_to_name_and_type :: "'a => tyco => type => bool" where
  [MRjud 1 2]: "sort_to_name_and_type C n T == True"
lemma sort_to_name_and_typeI[intro]: "sort_to_name_and_type C n T" by (simp add: sort_to_name_and_type_def)

definition
  type_to_sort :: "type => 'a => bool" where
  [MRjud 1 1]: "type_to_sort T C == True"
lemma type_to_sortI[intro]: "type_to_sort T C" by (simp add: type_to_sort_def)

definition
  sort_to_interpr :: "'a => 'b itself => bool" where
  [MRjud 1 1]: "sort_to_interpr s T == True"
lemma sort_to_interpr[intro]: "sort_to_interpr T C" by (simp add: sort_to_interpr_def)


definition
  psort_to_type :: "'a => type => bool" where
  [MRjud 1 1]: "psort_to_type C T == True"
lemma psort_to_typeI[intro]: "psort_to_type C T" by (simp add: psort_to_type_def)

definition
  type_to_psort :: "type => 'a => bool" where
  [MRjud 1 1]: "type_to_psort T C == True"
lemma type_to_psortI[intro]: "type_to_psort T C" by (simp add: type_to_psort_def)

definition
  type_to_interpr :: "type => 'a itself => bool" where
  [MRjud 1 1]: "type_to_interpr T tau == True"
lemma type_to_interprI[intro]: "type_to_interpr T C" by (simp add: type_to_interpr_def)

definition
  psort_to_tyinterpr :: "'a => 'b itself => bool" where
  [MRjud 1 1]: "psort_to_tyinterpr ps tau == True"
lemma psort_to_tyinterprI[intro]: "psort_to_tyinterpr ps tau" by (simp add: psort_to_tyinterpr_def)

definition
  oper_to_opsym :: "oper => 'a => bool" where
  [MRjud 1 1]: "oper_to_opsym c sigma == True"
lemma oper_to_opsymI[intro]: "oper_to_opsym c sigma" by (simp add: oper_to_opsym_def)

definition
  rel_to_relsym :: "rel => 'a => bool" where
  [MRjud 1 1]: "rel_to_relsym c sigma == True"
lemma rel_to_relsymI[intro]: "rel_to_relsym c sigma" by (simp add: rel_to_relsym_def)

definition
  uar_of_sym :: "'a => userar => bool" where
  [MRjud 1 1]: "uar_of_sym t uar == True"
lemma uar_of_symI[intro]: "uar_of_sym t uar" by (simp add: uar_of_sym_def)


definition
  proj_op_op :: "prop => oper => prop" where
  [MRjud 1 1]: "proj_op_op P oper == Trueprop True"
lemma proj_op_opI: "PROP proj_op_op P oper" by (simp add: proj_op_op_def)

definition
  proj_op_uar :: "prop => userar => prop" where
  [MRjud 1 1]: "proj_op_uar P uar == Trueprop True"
lemma proj_op_uarI: "PROP proj_op_uar P uar" by (simp add: proj_op_uar_def)

definition
  proj_op_par :: "prop => 'psort list => prop" where
  [MRjud 1 1]: "proj_op_par P par == Trueprop True"
lemma proj_op_parI: "PROP proj_op_par P par" by (simp add: proj_op_par_def)


definition
  proj_op_ar :: "prop => 'sort list => prop" where
  [MRjud 1 1]: "proj_op_ar P ar == Trueprop True"
lemma proj_op_arI: "PROP proj_op_ar P ar" by (simp add: proj_op_ar_def)

definition
  proj_op_s :: "prop => 'ssort => prop" where
  [MRjud 1 1]: "proj_op_s P s == Trueprop True"
lemma proj_op_sI: "PROP proj_op_s P s" by (simp add: proj_op_s_def)


definition
  proj_rel_rel :: "prop => rel => prop" where
  [MRjud 1 1]: "proj_rel_rel P rel == Trueprop True"
lemma proj_rel_relI: "PROP proj_rel_rel P rel" by (simp add: proj_rel_rel_def)

definition
  proj_rel_par :: "prop => 'psort list => prop" where
  [MRjud 1 1]: "proj_rel_par P par == Trueprop True"
lemma proj_rel_parI: "PROP proj_rel_par P par" by (simp add: proj_rel_par_def)

definition
  proj_rel_uar :: "prop => userar => prop" where
  [MRjud 1 1]: "proj_rel_uar P uar == Trueprop True"
lemma proj_rel_uarI: "PROP proj_rel_uar P uar" by (simp add: proj_rel_uar_def)

definition
  proj_rel_ar :: "prop => 'sort list => prop" where
  [MRjud 1 1]: "proj_rel_ar P ar == Trueprop True"
lemma proj_rel_arI: "PROP proj_rel_ar P ar" by (simp add: proj_rel_ar_def)


definition
  proj_pcond_const :: "prop => 'a => prop" where
  [MRjud 1 1]: "proj_pcond_const P c == Trueprop True"
lemma proj_pcond_constI: "PROP proj_pcond_const P const" by (simp add: proj_pcond_const_def)

definition
  proj_pcond_par :: "prop => 'psort list => prop" where
  [MRjud 1 1]: "proj_pcond_par P par == Trueprop True"
lemma proj_pcond_parI: "PROP proj_pcond_par P par" by (simp add: proj_pcond_par_def)


definition
  proj_reflected_hcl :: "prop => ('sort,'opsym,'rlsym,'psort,'paramuni) hcl => prop" where
  [MRjud 1 1]: "proj_reflected_hcl P hcl == Trueprop True"
lemma proj_reflected_hclI: "PROP proj_reflected_hcl P hclpar" by (simp add: proj_reflected_hcl_def)

definition
  proj_sort_to_name_and_type_s :: "prop => 'sort => prop" where
  [MRjud 1 1]: "proj_sort_to_name_and_type_s P s == Trueprop True"
lemma proj_sort_to_name_and_type_sI: "PROP proj_sort_to_name_and_type_s P s" by (simp add: proj_sort_to_name_and_type_s_def)

definition
  proj_psort_to_type_ps :: "prop => 'psort => prop" where
  [MRjud 1 1]: "proj_psort_to_type_ps P ps == Trueprop True"
lemma proj_psort_to_type_psI: "PROP proj_psort_to_type_ps P s" by (simp add: proj_psort_to_type_ps_def)




definition
  oper_with_ar :: "oper => type => userar => 'psort list => 'sort list => 'sort => bool" where
  [MRjud 1 5]: "oper_with_ar c T uar par ar s == True"
lemma oper_with_arI[intro]: "oper_with_ar c T uar par ar s" by (simp add: oper_with_ar_def)

definition
  rel_with_ar :: "rel => type => userar => 'psort list => 'sort list => bool" where
  [MRjud 1 4]: "rel_with_ar R T uar par ar == True"
lemma rel_with_arI[intro]: "rel_with_ar R T uar par ar" by (simp add: rel_with_ar_def)

definition
  pcond_with_ar :: "pcond => 'a => type => 'psort list => bool" where
  [MRjud 1 3]: "pcond_with_ar P c T par == True"
lemma pcond_with_arI[intro]: "pcond_with_ar P c T par" by (simp add: pcond_with_ar_def)


definition
  constr_prels :: "proplist => (('paramuni list => bool) * 'psort list) set => bool" where
  [MRjud 1 1]: "constr_prels L prels == True"
lemma constr_prelsI[intro]: "constr_prels L prels" by (simp add: constr_prels_def)

definition reflected_hcl :: "'a => ('sort,'opsym,'rlsym,'psort,'paramuni) hcl => bool" where
  [MRjud 1 1]: "reflected_hcl n hcl == True"
lemma reflected_hclI[intro]: "reflected_hcl n hcl" by (simp add: reflected_hcl_def)



definition
  coll_sort_to_name_and_type :: "unit => proplist => prop" where
  [MRcolljud "NonFree.sort_to_name_and_type_jud"]: "coll_sort_to_name_and_type x L == Trueprop True"
lemma coll_sort_to_name_and_typeI: "PROP coll_sort_to_name_and_type x L " by (simp add: coll_sort_to_name_and_type_def)
definition
  coll_psort_to_type :: "unit => proplist => prop" where
  [MRcolljud "NonFree.psort_to_type_jud"]: "coll_psort_to_type x L == Trueprop True"
lemma coll_psort_to_typeI: "PROP coll_psort_to_type x L " by (simp add: coll_psort_to_type_def)



definition
  coll_oper_with_ar :: "unit => proplist => prop" where
  [MRcolljud "NonFree.oper_with_ar_jud"]: "coll_oper_with_ar x L == Trueprop True"
lemma coll_oper_with_arI: "PROP coll_oper_with_ar x L " by (simp add: coll_oper_with_ar_def)

definition
  coll_rel_with_ar :: "unit => proplist => prop" where
  [MRcolljud "NonFree.rel_with_ar_jud"]: "coll_rel_with_ar x L == Trueprop True"
lemma coll_rel_with_arI: "PROP coll_rel_with_ar x L " by (simp add: coll_rel_with_ar_def)

definition
  coll_pcond_with_ar :: "unit => proplist => prop" where
  [MRcolljud "NonFree.pcond_with_ar_jud"]: "coll_pcond_with_ar x L == Trueprop True"
lemma coll_pcond_with_arI: "PROP coll_pcond_with_ar x L " by (simp add: coll_pcond_with_ar_def)

definition coll_reflected_hcl :: "unit => proplist => prop" where
  [MRcolljud "NonFree.reflected_hcl_jud"]: "coll_reflected_hcl x L == Trueprop True"
lemma coll_reflected_hclI: "PROP coll_reflected_hcl x L" by (simp add: coll_reflected_hcl_def)



definition sort_datatype :: "'a itself => bool" where
  [MRjud 1 0]: "sort_datatype tau == True"
lemma sort_datatypeI[intro]: "sort_datatype tau" by (simp add: sort_datatype_def)

definition psort_datatype :: "'a itself => bool" where
  [MRjud 1 0]: "psort_datatype tau == True"
lemma psort_datatypeI[intro]: "psort_datatype tau" by (simp add: psort_datatype_def)

definition opsym_datatype :: "'a itself => bool" where
  [MRjud 1 0]: "opsym_datatype tau == True"
lemma opsym_datatypeI[intro]: "opsym_datatype tau" by (simp add: opsym_datatype_def)

definition relsym_datatype :: "'a itself => bool" where
  [MRjud 1 0]: "relsym_datatype tau == True"
lemma relsym_datatypeI[intro]: "relsym_datatype tau" by (simp add: relsym_datatype_def)

definition stOf_is :: "('opsym \<Rightarrow> 'sort) => bool" where
  [MRjud 1 0]: "stOf_is x == True"
lemma stOf_isI[intro]: "stOf_is x" by (simp add: stOf_is_def)

definition arOfP_is :: "('opsym \<Rightarrow> 'psort list) => bool" where
  [MRjud 1 0]: "arOfP_is x == True"
lemma arOfP_isI[intro]: "arOfP_is x" by (simp add: arOfP_is_def)

definition arOf_is :: "('opsym \<Rightarrow> 'sort list) => bool"  where
  [MRjud 1 0]: "arOf_is x == True"
lemma arOf_isI[intro]: "arOf_is x" by (simp add: arOf_is_def)

definition rarOf_is :: "('rlsym \<Rightarrow> 'sort list) => bool"  where
  [MRjud 1 0]: "rarOf_is x == True"
lemma rarOf_isI[intro]: "rarOf_is x" by (simp add: rarOf_is_def)

definition rarOfP_is :: "('rlsym \<Rightarrow> 'psort list) => bool"  where
  [MRjud 1 0]: "rarOfP_is x == True"
lemma rarOfP_isI[intro]: "rarOfP_is x" by (simp add: rarOfP_is_def)

definition params_is :: "('psort \<Rightarrow> 'paramuni set) => bool" where
  [MRjud 1 0]: "params_is x == True"
lemma params_isI[intro]: "params_is x" by (simp add: params_is_def)

definition hcls_is :: "('sort,'opsym,'rlsym,'psort,'paramuni) hcl list => bool" where
  [MRjud 1 0]: "hcls_is l == True"
lemma hcls_isI[intro]: "hcls_is l" by (simp add: hcls_is_def)



definition
  nonzero :: "nat => bool" where
  [MRjud 1 0]: "nonzero n == (n ~= 0)"

lemma [MR]: "nonzero (Suc x)"
  by (simp add: nonzero_def)



lemma [expl_frule]: "
  decl_oper c T
  ==>  enum_sorts_and_params T  " ..

lemma [expl_frule]: "
  decl_rel R T
  ==>  enum_sorts_and_params T  " ..

lemma [expl_frule]: "
  decl_pcond P T
  ==>  enum_sorts_and_params T  " ..

lemma [expl_frule]: "[|
  enum_sorts_and_params (T1 =T=> T2)  ;  try (T1 haskind IntType)  |]
  ==>  enum_sorts_and_params T2  &&&  needs_sort T1  " by triv+

lemma [expl_frule]: "[|
  enum_sorts_and_params (T1 =T=> T2)  ;  try (T1 haskind ExtType)  |]
  ==>  enum_sorts_and_params T2  &&&  needs_param T1  " by triv+

lemma [expl_frule]: "[|
  enum_sorts_and_params T  ;  try ( T haskind IntType )  |]
  ==>  enum_sorts_and_params T  &&&  needs_sort T  " by triv+

lemma [expl_frule]: "[|
  PROP coll_needs_sort () L  ;  proplist_len L n  ;  nonzero n  ;
    scopify_name sorts_enum_name name'  ;
    enum_datatype name' n tau Cs  |]
  ==>  def_sort_type_map L Cs  &&&  sort_datatype tau " by triv+

lemma [expl_frule]: "[|
  def_sort_type_map (prop_cons (Trueprop (needs_sort T)) L) (Cons C Cs)  ;
    extract_tyco T k  |]
  ==>  def_sort_type_map L Cs  &&&  sort_to_name_and_type C k T  &&&  type_to_sort T C  "
  by triv+



lemma [expl_frule]: "[|
  PROP coll_needs_param () L ;
    proplist_len L n  ;  try (nonzero n)  ;
    scopify_name psorts_enum_name name'  ;
    enum_datatype name' n tau Cs  |]
  ==>  def_psort_type_map L Cs  &&&  psort_datatype tau  " by triv+

definition
  "dummy_param_T == Tyco (TycoEmb 0)"
lemma [MR]: "dummy_param_T haskind ExtType" ..

(* if no params needed,  use dummy psort, pseudotype, tyinterpr  *)
lemma [expl_frule]: "[|
  PROP coll_needs_param () L ; try( proplist_len L 0 )  ;
    scopify_name psorts_enum_name name'  ;
    enum_datatype name' (Suc 0) tau Cs  |]
  ==>  def_psort_type_map (prop_cons (Trueprop (needs_param dummy_param_T)) prop_nil) Cs  &&&
       decl_tyinterpr dummy_param_T TYPE(unit) &&&
       psort_datatype tau  " by triv+

lemma [expl_frule]: "
  def_psort_type_map (prop_cons (Trueprop (needs_param T)) L) (Cons C Cs)
  ==> def_psort_type_map L Cs  &&&  psort_to_type C T  &&&  type_to_psort T C  "
  by triv+


definition
  tyvar_interpr :: "tyvar => 'a itself => bool" where
  [MRjud 1 1]: "tyvar_interpr alpha tau == True"
lemma tyvar_interprI[intro]: "tyvar_interpr alpha tau" by (simp add: tyvar_interpr_def)

lemma [MR]: "
  decl_tyinterpr alpha TYPE('a)
  ==> tyvar_interpr alpha TYPE('a) " ..


lemma [expl_frule]: "[|
  decl_tyinterpr T TYPE('a)  ;   T haskind ExtType |]
  ==> type_to_interpr T TYPE('a)  " ..

lemma [MR]: "
  type_to_interpr bool TYPE(bool)  " ..

lemma [MR]: "[|  type_to_interpr T1 TYPE('tau1)  ;   type_to_interpr T2 TYPE('tau2)  |] ==>
  type_to_interpr (T1 =T=> T2) TYPE('tau1 => 'tau2)  " ..

ML {*
  MetaRec.decompose_judgement (@{context} |> Context.Proof)
    @{prop "metamap type_to_psort (parTs::NonFree.type list) (pars::'a list)"};
*}


lemma [expl_frule]: "[|
  decl_oper c T  &&&  psort_datatype TYPE('psort)  &&&  sort_datatype TYPE('sort)  ;
    calc_op_ar T uar parTs arTs sT  ;
    metamap (type_to_psort :: type => 'psort => bool) parTs pars  ;
    metamap (type_to_sort :: type => 'sort => bool) arTs ars  ;  type_to_sort sT s   |]
  ==>  oper_with_ar c T uar pars ars s " ..


lemma [expl_frule]: "[|
  decl_rel R T  &&&  sort_datatype TYPE('sort)  &&&  psort_datatype TYPE('psort)  ;
    calc_rel_ar T uar parTs arTs  ;
    metamap (type_to_psort :: type => 'psort => bool) parTs pars  ;
    metamap (type_to_sort :: type => 'sort => bool) arTs ars  |]
  ==>  rel_with_ar R T uar pars ars " ..






definition
  "reify_iso = isomark 0"
definition
  "paramiso = isomark 0"


(* To make dependency analysis easier we give specialized judgement
   for isomorphic transfer of parameter soft types.
   Does not need argument permutations, as parameter conditions have only
   parameter arguments *)
definition
  paramisotovia_const :: "'a setoid => 'b setoid => ('a => 'b) => bool" ("_ paramisoto _ via _" [1000,1000,1000] 10)
where
  [MRjud 1 2]: "(AA paramisoto AA' via f) == ((curry_iso None paramiso):  AA isoto AA' via f)"

lemma paramisoto_fun[MR]: "[|
      AA paramisoto AA' via f  ;
      BB paramisoto BB' via g  |] ==>
    (AA ~s~> BB) paramisoto (AA' ~s~> BB') via (f : AA -> AA'  ##>>  g : BB -> BB')  "
  unfolding paramisotovia_const_def by (rule isoto_funsetoid)


lemma paramisoto_bool[MR]: "
  (UNIV_s :: bool setoid) paramisoto UNIV_s via id"
unfolding paramisotovia_const_def by (rule isoto_UNIV_s)


lemma [MR]: "  BB paramisoto (BB' :: 'b2 setoid) via g  ==>
  (sset (product ([] :: 'a set list)) ~s~> (BB :: 'b setoid))  paramisoto BB'
    via ((prod_nil_iso g) :: ('a list => 'b) => 'b2)  "
  unfolding paramisotovia_const_def by (rule isoto_prod_nil)

lemma [MR]: "[|
    (sset A) paramisoto (sset A') via f  ;
    (sset (product As) ~s~> BB)  paramisoto  CC' via g  ;
    setoid BB  |] ==>
  (sset (product (Cons A As)) ~s~> BB)  paramisoto  (sset A' ~s~> CC')
    via (prod_cons_iso f (sset A) (sset A') g)  "
  unfolding paramisotovia_const_def using isoto_prod_cons
  by (simp add: isotovia_const_def)



definition
  define_opers_to_opsyms :: "oper list => 'a list => userar list => bool" where
  [MRjud 3 0]: "define_opers_to_opsyms ops Cs uars == True"
lemma define_opers_to_opsymsI[intro]: "define_opers_to_opsyms ops Cs uars" by (simp add: define_opers_to_opsyms_def)
definition
  define_rels_to_relsyms :: "rel list => 'a list => userar list => bool" where
  [MRjud 3 0]: "define_rels_to_relsyms ops Cs uars == True"
lemma define_rels_to_relsymsI[intro]: "define_rels_to_relsyms ops Cs uars" by (simp add: define_rels_to_relsyms_def)


lemma [MR]: "PROP proj_op_op (Trueprop (oper_with_ar c T uar par ar s)) c" by (rule proj_op_opI)
lemma [MR]: "PROP proj_op_uar (Trueprop (oper_with_ar c T uar par ar s)) uar" by (rule proj_op_uarI)
lemma [MR]: "PROP proj_op_par (Trueprop (oper_with_ar c T uar par ar s)) par" by (rule proj_op_parI)
lemma [MR]: "PROP proj_op_ar (Trueprop (oper_with_ar c T uar par ar s)) ar" by (rule proj_op_arI)
lemma [MR]: "PROP proj_op_s (Trueprop (oper_with_ar c T uar par ar s)) s" by (rule proj_op_sI)
lemma [MR]: "PROP proj_rel_rel (Trueprop (rel_with_ar R T uar par ar)) R" by (rule proj_rel_relI)
lemma [MR]: "PROP proj_rel_uar (Trueprop (rel_with_ar R T uar par ar)) uar" by (rule proj_rel_uarI)
lemma [MR]: "PROP proj_rel_par (Trueprop (rel_with_ar R T uar par ar)) par" by (rule proj_rel_parI)
lemma [MR]: "PROP proj_rel_ar (Trueprop (rel_with_ar R T uar par ar)) ar" by (rule proj_rel_arI)
lemma [MR]: "PROP proj_pcond_const (Trueprop (pcond_with_ar P c T par)) c" by (rule proj_pcond_constI)
lemma [MR]: "PROP proj_pcond_par (Trueprop (pcond_with_ar P c T par)) par" by (rule proj_pcond_parI)

definition
  "op_enum_name = (0::nat)"
definition
  "op_par_fun_name = (0::nat)"
definition
  "op_ar_fun_name = (0::nat)"
definition
  "op_s_fun_name = (0::nat)"

definition
  proplist_to_bools :: "proplist => bool list => bool" where
  [MRjud 1 1]: "proplist_to_bools L l == True"
lemma proplist_to_boolsI[intro]: "proplist_to_bools L l"
  by (simp add: proplist_to_bools_def)

lemma [MR]: " proplist_to_bools L Ps ==>
  proplist_to_bools (prop_cons (Trueprop P) L) (Cons P Ps) " ..
lemma [MR]: "
  proplist_to_bools prop_nil []" ..

lemma [expl_frule]: "[|
  PROP coll_oper_with_ar () L   &&&  psort_datatype TYPE('psort)  &&&  sort_datatype TYPE('sort);
    proplist_len L n  ;  nonzero n  ;
    proplist_to_bools L bools ;
    scopify_name op_enum_name op_enum_name'  ;
    scopify_name op_par_fun_name op_par_fun_name'  ;
    scopify_name op_ar_fun_name op_ar_fun_name'  ;
    scopify_name op_s_fun_name op_s_fun_name'  ;

    enum_datatype op_enum_name' n T Cs  ;

    proj_proplist proj_op_op L ops  ;
    proj_proplist proj_op_uar L (uars :: userar list)  ;
    proj_proplist proj_op_par L (pars :: 'psort list list)  ;
    proj_proplist proj_op_ar L (ars :: 'sort list list) ;
    proj_proplist proj_op_s L (ss :: 'sort list)  ;
    enumfun op_par_fun_name' on T withvals pars gives arOfP  ;
    enumfun op_ar_fun_name' on T withvals ars gives arOf  ;
    enumfun op_s_fun_name' on T withvals ss gives stOf |]
  ==>  opsym_datatype T  &&&  define_opers_to_opsyms ops Cs uars  &&&
    arOfP_is arOfP  &&&  arOf_is arOf  &&&  stOf_is stOf  " by triv+

lemma [expl_frule]: "
  define_opers_to_opsyms (Cons c cs) (Cons C Cs) (Cons uar uars)
  ==>  oper_to_opsym c C  &&&  uar_of_sym C uar  &&&  define_opers_to_opsyms cs Cs uars"
   by triv+


definition
  op_rew_ready :: "'a => bool" where
  [MRjud 1 0]: "op_rew_ready x == True"
definition
  op_rews_ready :: "unit => proplist => prop" where
  [MRcolljud "NonFree.op_rew_ready_jud"]: "op_rews_ready x L == Trueprop True"

lemma [expl_frule]: "[|
  oper_to_opsym c C  &&&  stOf_is stOf  &&&  arOf_is arOf  &&&  arOfP_is arOfP  ;
    enumfun_rewr (stOf C) n s  ; enumfun_rewr (arOfP C) n2 par  ;
    enumfun_rewr (arOf C) n3 ar |]
  ==>  brule(  stOf C rewto s  )  &&&  brule(  arOfP C rewto par  )  &&&  brule(  arOf C rewto ar  )  &&&
       op_rew_ready C  "
  apply (simp add: brule_const_def rewto_const_def enumfun_rewr_def op_rew_ready_def)
  apply (triv, simp)+
  by simp






definition
  "rel_enum_name = (0::nat)"
definition
  "rel_par_fun_name = (0::nat)"
definition
  "rel_ar_fun_name = (0::nat)"


lemma [expl_frule]: "[|
  PROP coll_rel_with_ar () L  &&&  psort_datatype TYPE('psort)  &&&  sort_datatype TYPE('sort)  ;
    proplist_len L n  ;  try (nonzero n)  ;
    scopify_name rel_enum_name rel_enum_name'  ;
    scopify_name rel_par_fun_name rel_par_fun_name'  ;
    scopify_name rel_ar_fun_name rel_ar_fun_name'  ;

    enum_datatype rel_enum_name' n T Cs  ;

    proj_proplist proj_rel_rel L rels  ;
    proj_proplist proj_rel_uar L (uars :: userar list)  ;
    proj_proplist proj_rel_par L (parss :: 'psort list list)  ;
    proj_proplist proj_rel_ar L (arss :: 'sort list list)  ;
    enumfun rel_par_fun_name' on T withvals parss gives rarOfP  ;
    enumfun rel_ar_fun_name' on T withvals arss gives rarOf  |]
  ==>  relsym_datatype T  &&&  define_rels_to_relsyms rels Cs uars  &&&
     rarOfP_is rarOfP  &&&  rarOf_is rarOf  " by triv+


(* if no relations declared, invent dummy relation with trivial arity, no clauses, no rel_to_relsym mapping
   so it is never satisfied, but also never occurs in HCLs *)
lemma [expl_frule]: "[|
  PROP coll_rel_with_ar () L  &&&  psort_datatype TYPE('psort)  &&&  sort_datatype TYPE('sort)  ;
    try( proplist_len L 0 )  ;
    scopify_name rel_enum_name rel_enum_name'  ;
    scopify_name rel_par_fun_name rel_par_fun_name'  ;
    scopify_name rel_ar_fun_name rel_ar_fun_name'  ;

    enum_datatype rel_enum_name' (Suc 0) T [C]  ;

    enumfun rel_par_fun_name' on T withvals ([[]] :: 'psort list list) gives rarOfP  ;
    enumfun rel_ar_fun_name' on T withvals ([[]] :: 'sort list list) gives rarOf  ;
    enumfun_rewr (rarOfP C) rel_par_fun_name' []  ;
    enumfun_rewr (rarOf C) rel_ar_fun_name' []  |]
  ==>  relsym_datatype T  &&&  rarOfP_is rarOfP  &&&  rarOf_is rarOf  &&&
         brule(  rarOfP C rewto []  )  &&&  brule(  rarOf C rewto []  )"
  unfolding enumfun_rewr_def brule_const_def rewto_const_def apply simp by triv+



lemma [expl_frule]: "
  define_rels_to_relsyms (Cons c cs) (Cons C Cs) (Cons uar uars)
  ==>  rel_to_relsym c C  &&&  uar_of_sym C uar  &&&  define_rels_to_relsyms cs Cs uars" by triv+

definition
  rel_rew_ready :: "'a => bool" where
  [MRjud 1 0]: "rel_rew_ready x == True"
definition
  rel_rews_ready :: "unit => proplist => prop" where
  [MRcolljud "NonFree.rel_rew_ready_jud"]: "rel_rews_ready x L == Trueprop True"

lemma [expl_frule]: "[|
  rel_to_relsym c C  &&&  rarOf_is rarOf  &&&  rarOfP_is rarOfP  ;
    enumfun_rewr (rarOfP C) n par  ;  enumfun_rewr (rarOf C) n2 ar |]
  ==>  brule(  rarOfP C rewto par  )  &&&  brule(  rarOf C rewto ar  )  &&&  rel_rew_ready C  "
  apply (simp add: brule_const_def rewto_const_def enumfun_rewr_def rel_rew_ready_def)
  apply (triv, simp)+ by simp







(* NB: HOL has only schematic polymorphism, so we are not able to abstract psort_to_tyinterpr
     out of the param_sum construction *)
lemma [MR]: "[|  psort_to_type ps T  ;  decl_tyinterpr T TYPE('tau)  |] ==>
  psort_to_tyinterpr ps TYPE('tau)  " ..


definition
  partial_param_sum :: "'psort list => 'b itself => bool" where
  [MRjud 1 1]: "partial_param_sum psorts tau == True"
lemma partial_param_sumI[intro]: "partial_param_sum psorts i" by (simp add: partial_param_sum_def)

definition
  partial_param_sum_In :: "'psort list => 'psort => ('a => 'b) => bool" where
  [MRjud 2 1]: "partial_param_sum_In psorts ps i == inj i"


definition
  param_sum :: "unit => 'b itself => bool" where
  [MRjud 1 1]: "param_sum x tau == True"
lemma param_sumI[intro]: "param_sum x tau" by (simp add: param_sum_def)

definition
  param_sum_In :: "'psort => ('a => 'b) => bool" where
  [MRjud 1 1]: "param_sum_In ps i == inj i"



lemma partial_param_sum_In_step[MR]: "[|  partial_param_sum_In ms m2 (i :: 'tau2 => 'tau_param_sum)  ;
    psort_to_tyinterpr m TYPE('tau)  |] ==>
  partial_param_sum_In (Cons m ms) m2 ((Inr o i) :: 'tau2 => 'tau + 'tau_param_sum)  "
  unfolding partial_param_sum_In_def apply (rule inj_comp) by simp+

lemma partial_param_sum_In_base[MR]: "[|  partial_param_sum ms TYPE('tau_sum)  ;  psort_to_tyinterpr m TYPE('tau)  |] ==>
  partial_param_sum_In (Cons m ms) m (Inl :: 'tau => 'tau + 'tau_sum)  "
  unfolding partial_param_sum_In_def by simp



lemma partial_param_sum_base[MR]: "
  partial_param_sum [] TYPE(unit)  " by triv+

lemma partial_param_sum_step[MR]: "[| partial_param_sum ms TYPE('tau_sum)  ;  psort_to_tyinterpr m TYPE('tau)  |] ==>
  partial_param_sum (Cons m ms) TYPE('tau + 'tau_sum)  " by triv+






lemma [MR]: "PROP proj_psort_to_type_ps (Trueprop (psort_to_type ps T)) ps"
  by (simp add: proj_psort_to_type_ps_def)


lemma [expl_frule]: "[|
  PROP coll_psort_to_type () L   &&&   psort_datatype TYPE('psorts)  ;
    proj_proplist proj_psort_to_type_ps L (psorts :: 'psorts list)   |]
  ==>
    brule(  partial_param_sum_In psorts ps i  ==>
      param_sum_In ps i ) &&&

    brule(  partial_param_sum psorts TYPE('tau) ==>
      param_sum () TYPE('tau)  )  "
    unfolding brule_const_def partial_param_sum_In_def param_sum_In_def param_sum_def
    by (rule Pure.conjunctionI) simp+






definition inhab_params where
  [MRjud 1 0]: "inhab_params S == (EX x. S x)"

lemma empty_bij_img: "bij_betw f A B ==> B = {} ==> A = {}"
  by (simp add: bij_betw_empty2)

lemma nonempty_bij_dom: "A ~= {} ==> bij_betw f A B ==> B ~= {}"
  by (rule rev_contrapos[OF empty_bij_img])

lemma nonempty_bij_from_UNIV: "bij_betw f UNIV B ==> B ~= {}"
  apply (rule nonempty_bij_dom) by (rule UNIV_not_empty)


definition
  embed_tyinterpr :: "'psort => 'paramuni set => bool" where
  [MRjud 1 1]: "embed_tyinterpr ps S == True"

lemma [MR]: "  param_sum_In ps i  ==>
  embed_tyinterpr ps (range i)  "  by (simp add: embed_tyinterpr_def)

definition
  "params_fun_name = (0::nat)"

lemma [expl_frule]: "[|
  PROP coll_psort_to_type () L  &&&  psort_datatype TYPE('psort)  ;
    param_sum () TYPE('paramuni);
    proj_proplist proj_psort_to_type_ps L (psorts :: 'psort list)  ;
    metamap embed_tyinterpr psorts (embedded_param_sets :: 'paramuni set list) ;
    scopify_name params_fun_name params_fun_name'  ;
    enumfun params_fun_name' on TYPE('psort) withvals embedded_param_sets gives params |]
  ==> params_is params " ..

(* TODO(refactor): unschoen das reify_alg_iso jetzt schon abgesetzt wird *)
(*  Note: no isomap clause necessary  because parameters are always quantified variables *)
lemma [expl_frule]: "[|
  psort_to_type ps T  &&&  params_is params  ;
    param_sum_In ps (i :: 'tau => 'a)  ;
    enumfun_rewr (params ps) n (range i)  |]
  ==>   inhab_params (params ps)  &&&
        (sset (params ps))  paramisoto  (UNIV_s :: 'tau setoid)  via (the_inv i)  &&&
        reify_iso:  (sset (params ps))  isoto  (UNIV_s :: 'tau setoid)  via (the_inv i) "
unfolding param_sum_In_def inhab_params_def enumfun_rewr_def paramisotovia_const_def isotovia_const_def
apply (intro Pure.conjunctionI)
  apply (metis mem_def rangeI)
  apply (metis bij_betw_def bij_to_equi inj_on_the_inv_into the_inv_into_onto)
  by (metis bij_betw_def bij_to_equi inj_on_the_inv_into the_inv_into_onto)

definition
  "unreified_name = (0::nat)"

definition
  reg_UNIV_s_rew :: "unit => bool" where
  [MRjud 1 0]: "reg_UNIV_s_rew x == True"

(* brule needed because extra type variables *)
lemma [impl_frule]: "
  reg_UNIV_s_rew ()
  ==>  brule(  ((UNIV_s :: 'tau setoid) ~s~> (UNIV_s :: 'tau2 setoid))
               rewto
               (UNIV_s :: ('tau => 'tau2) setoid)  ) "
 by (simp add: brule_const_def rewto_const_def fun_setoid_UNIV_s)

(* Still true?: laeuft nur einmal, generiert aber irgendwie mehrfach exportierte
   pcond_with_ar im gleichen Kontext,
   wie sie auf unterschiedlichen Kontextebenen vorliegen sollten *)
(* NB: using paramisoto to make noncyclicity of dependencies explicit *)
lemma pcond_with_ar_gen[expl_frule]: "[|
  decl_pcond P T  &&&  psort_datatype TYPE('psort)  &&&  params_is params ;
    decl_pcond_interpr P (t :: 'tau)  ;
    extpred T  ;  type_to_interpr T TYPE('tau)  ;
    calc_pcond_par T parTs  ;  metamap type_to_psort parTs (pars :: 'psort list)  ;
    (sset (product (map params pars)) ~s~> (UNIV_s :: bool setoid))
      simpto AA  ;
    AA paramisoto AA' via f  ;
    reg_UNIV_s_rew () ==> AA' simpto (UNIV_s :: 'tau setoid)  ;
    concat names P unreified_name  = n'  ;
    scopify_name n' n'' ;
    define n'' := ((s_inv AA AA' f) t) giving c   |]
  ==>  pcond_with_ar P c T pars   &&&
       invariant (c, c) AA  &&&
       (curry_iso None reify_iso):  c : AA  isomapto  t : AA'  via f"
unfolding paramisotovia_const_def isotovia_const_def pcond_with_ar_def
          define_const_def simpto_const_def
apply (intro Pure.conjunctionI)
  apply (rule TrueI)
  apply (metis carOf_UNIV_s invariant_reflI iso_sDsetoid(1)
               iso_tuple_UNIV_I reg_UNIV_s_rew_def s_inv_carOf)
  unfolding isomapto_via_def apply(intro conjI)
    apply (metis UNIV_setoid elem_UNIV_sI elem_setdom_funsetoid)
    apply (metis UNIV_I carOf_UNIV_s reg_UNIV_s_rew_def)
    apply (metis iso_sDsetoid(1))
    apply (metis iso_sDsetoid(2))
    apply assumption
    by (metis elem_UNIV_sI reg_UNIV_s_rew_def s_inv_eqOf)


definition
  proj_prels :: "prop => ('paramuni list => bool) * 'psort list => prop" where
  [MRjud 1 1]: "proj_prels P cpar == Trueprop True"
definition
  prels_is :: "(('paramuni list => bool) * 'psort list) list => bool" where
  [MRjud 1 0]: "prels_is S == True"

lemma [MR]: "PROP proj_prels (Trueprop (pcond_with_ar P c T par)) (c, par)"
by (simp add: proj_prels_def)

lemma [expl_frule]: "[|
  PROP coll_pcond_with_ar () L  &&&  psort_datatype TYPE('psort)  ;
    param_sum () TYPE('paramuni)  ;
    proj_proplist proj_prels L (prels :: (('paramuni list => bool) * 'psort list) list)  |]
  ==>  prels_is prels" by (simp add: prels_is_def)




definition
  ref_atm_app :: "terms => ('sort,'opsym,'rlsym,'psort,'param) atm itself
                      => (('psort * pvar) list => ('sort,'opsym) trm list => ('sort,'opsym,'rlsym,'psort,'param) atm)
                      => type => bool" where
  [MRjud 2 2]: "ref_atm_app P tau t T == True"
lemma ref_atm_appI[intro]: "ref_atm_app P tau t T" by (simp add: ref_atm_app_def)

definition
  ref_app :: "terms => ('sort,'opsym,'rlsym,'psort,'param) atm itself
                   => (pvar list => ('sort,'opsym) trm list => ('sort,'opsym) trm)
                   => type => bool" where
  [MRjud 2 2]: "ref_app P tau t T == True"
lemma ref_appI[intro]: "ref_app P tau t T" by (simp add: ref_app_def)

definition
  ref_atm :: "terms =>  ('sort,'opsym,'rlsym,'psort,'param) atm itself
                   => ('sort,'opsym,'rlsym,'psort,'param) atm => bool" where
  [MRjud 2 1]: "ref_atm P tau t == True"
lemma ref_atmI[intro]: "ref_atm P tau t" by (simp add: ref_atm_def)

definition
  ref_hcl :: "terms => nat => ('sort,'opsym,'rlsym,'psort,'param) atm itself
                => ('sort,'opsym,'rlsym,'psort,'param) hcl => bool" where
  [MRjud 3 1]: "ref_hcl P i tau t == True"
lemma ref_hclI[intro]: "ref_hcl P i tau t" by (simp add: ref_hcl_def)

definition
  reflect_hcl :: "terms =>  ('sort,'opsym,'rlsym,'psort,'param) atm itself
               => ('sort,'opsym,'rlsym,'psort,'param) hcl => bool" where
  [MRjud 2 1]: "reflect_hcl P tau t == True"
lemma reflect_hclI[intro]: "reflect_hcl P tau t" by (simp add: reflect_hcl_def)





lemma [MR]:  "[|  try (decl_pcond P T)  ;  pcond_with_ar P c T pars   |] ==>
  ref_atm_app (PCond P) TYPE(('sort,'opsym,'rlsym,'psort,'param) atm)
    (% (pargs :: ('psort * pvar) list) (args :: ('sort,'opsym) trm list).
      Pcond c (map fst pargs) (map snd pargs)) T  " ..

lemma [MR]:  "[|  try (decl_rel R T)  ;  rel_to_relsym R rlsym  |] ==>
  ref_atm_app (Rel R) TYPE(('sort,'opsym,'rlsym,'psort,'param) atm)
    (% (pargs :: ('psort * pvar) list) (args :: ('sort,'opsym) trm list).
      Rl rlsym (map snd pargs) args) T  " ..

lemma [MR]: "[|  ref_atm_app e1 tau t1 (T1 =T=> T2)  ;  (PseudoVar i) hastype T1  ;  type_to_psort T1 (ps2 :: 'psort)  ;
    tau matches TYPE(('sort,'opsym,'rlsym,'psort,'param) atm)  |] ==>
  ref_atm_app (e1 $ (PseudoVar i)) tau (% (pargs :: ('psort * pvar) list).
     t1 (Cons (ps2, pvar i) pargs)) T2  " ..

lemma [MR]: "[|  e2 hastype T1  ;  try (T1 haskind IntType)  ;
    ref_atm_app e1 tau t1 (T1 =T=> T2)  ;
    ref_app e2 tau t2 T1  ;
    tau matches TYPE(('sort,'opsym,'rlsym,'psort,'param) atm)  |] ==>
  ref_atm_app (e1 $ e2) tau (%  (pargs :: ('psort * pvar) list) (args :: ('sort,'opsym) trm list).
     t1 pargs (Cons (t2 [] []) args)) T2  " ..


lemma [MR]:  "[|  try (decl_oper c T)  ;  oper_to_opsym c opsym  |] ==>
  ref_app (Oper c) tau (% pargs args. Op opsym pargs args) T  " ..

lemma [MR]: "[|  ref_app e1 tau t1 (T1 =T=> T2)  ;  (PseudoVar i) hastype T1  |] ==>
  ref_app (e1 $ (PseudoVar i)) tau (% pargs. t1 (Cons (pvar i) pargs)) T2  " ..

lemma [MR]: "[|  e2 hastype T1  ;  try (T1 haskind IntType)  ;  ref_app e1 tau t1 (T1 =T=> T2)  ;
    ref_app e2 tau t2 T1 |] ==>
  ref_app (e1 $ e2) tau (% pargs args. t1 pargs (Cons (t2 [] []) args)) T2  " ..



lemma [MR]: "  ref_atm_app e tau t bool  ==>
  ref_atm e tau (t [] [])  " ..

lemma [MR]: "[|  ref_app e tau t T  ;  ref_app e2 tau t2 T  ;  type_to_sort T s  |] ==>
  ref_atm (e === e2) tau (Eq s (t [] []) (t2 [] []))  " ..

lemma [MR]: "  ref_atm P tau t ==>
  ref_hcl P i tau (Horn [] t)  " ..

lemma [MR]: "[|  ref_atm P1 tau t1  ;  ref_hcl P i tau (Horn ts t)  |] ==>
  ref_hcl (P1 ---> P) i tau (Horn (Cons t1 ts) t)  " ..

lemma [MR]: "[|  T haskind ExtType  ;
    (PseudoVar i) hastype T  ==>  ref_hcl (P i) (Suc i) tau t  |] ==>
  ref_hcl (QUANT x:T. P x) i tau t  " ..

lemma [MR]: "[|  try( T haskind IntType )  ;  type_to_sort T s  ;
    [|  (PseudoVar i) hastype T  ;  ref_app (PseudoVar i) tau (% pargs args. Var s (var i)) T  |] ==>
      ref_hcl (P i) (Suc i) tau t  |] ==>
  ref_hcl (QUANT x:T. P x) i tau t  " ..

lemma [MR]: "[|  ref_hcl P 0 tau t  ;  t simpto t'  |] ==>
  reflect_hcl P tau t'  " ..


lemma [MR]: "PROP proj_reflected_hcl (Trueprop (reflected_hcl n hcl)) hcl" by (rule proj_reflected_hclI)

lemma [expl_frule]: "[|
  decl_hcl n hcl  &&&  sort_datatype TYPE('sort)  &&&  psort_datatype TYPE('psort)  &&&
      opsym_datatype TYPE('opsym)  &&&  relsym_datatype TYPE('rlsym)  ;
      param_sum () TYPE('paramuni)  ;
      reflect_hcl hcl TYPE(('sort,'opsym,'rlsym,'psort,'paramuni) atm) hcl'  |]
  ==> reflected_hcl n hcl'  " ..


lemma [expl_frule]: "[|
  PROP coll_reflected_hcl () L  &&&  sort_datatype TYPE('sort)  &&&  psort_datatype TYPE('psort)  &&&
      opsym_datatype TYPE('opsym)  &&& relsym_datatype TYPE('rlsym)  ;
    param_sum () TYPE('paramuni)  ;
    proj_proplist proj_reflected_hcl L (hcls :: ('sort,'opsym,'rlsym,'psort,'paramuni) hcl list)  |]
  ==>  hcls_is hcls " ..









(* instantiating the meta theory
   NB: we have to keep everything global, because typedefs are a global concept *)

record ('sort,'opsym,'rlsym,'psort,'paramuni) sig =
  stOf_pr :: "'opsym \<Rightarrow> 'sort"
  arOfP_pr :: "'opsym \<Rightarrow> 'psort list"
  arOf_pr :: "'opsym \<Rightarrow> 'sort list"
  rarOf_pr :: "'rlsym \<Rightarrow> 'sort list"
  rarOfP_pr :: "'rlsym \<Rightarrow> 'psort list"
  params_pr :: "'psort \<Rightarrow> 'paramuni set"
  prels_pr :: "(('paramuni list \<Rightarrow> bool) * 'psort list) list"
  hcls_pr :: "('sort,'opsym,'rlsym,'psort,'paramuni) hcl list"



definition my_sig_name where
  "my_sig_name = ( 0 :: nat )"

definition
  sig_is :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => bool" where
  [MRjud 1 0]: "sig_is sig == True"
lemma sig_isI[intro]: "sig_is sig" by (simp add: sig_is_def)
definition
  [MRjud 2 0]: "gen_in_hcls l hcls == (ALL hcl : set l. hcl : set hcls)"
definition
  [MRjud 1 1]: "in_hcls hcl hcls == hcl : set hcls"


(* wuerde zyklische Abhaengigkeit ergeben wenn simpto -> rewto Abhaengigkeit getrackt wuerde *)
lemma sigI[expl_frule]: "[|
  stOf_is stOf  &&&  arOfP_is arOfP  &&&  arOf_is arOf  &&&  rarOf_is rarOf  &&&
    rarOfP_is rarOfP  &&&  params_is params  &&&  prels_is prels  &&&  hcls_is hcls  &&&
    PROP op_rews_ready () x  &&&  PROP rel_rews_ready () x2  ;
    scopify_name my_sig_name my_sig_name'  ;
    define my_sig_name' := (| stOf_pr = stOf, arOfP_pr = arOfP, arOf_pr = arOf,
      rarOf_pr = rarOf, rarOfP_pr = rarOfP, params_pr = params, prels_pr = prels, hcls_pr = hcls |) giving sig  |]
  ==>
    brule(  stOf_pr sig rewto stOf  )  &&&  brule(  arOfP_pr sig rewto arOfP  )  &&&
    brule(  arOf_pr sig rewto arOf  )  &&&  brule(  rarOf_pr sig rewto rarOf  )  &&&
    brule(  rarOfP_pr sig rewto rarOfP  )  &&&  brule(  params_pr sig rewto params  )  &&&
    brule(  prels_pr sig rewto prels  )  &&&  brule(  hcls_pr sig rewto hcls  )  &&&
    sig_is sig  &&&  gen_in_hcls hcls (hcls_pr sig) "
    unfolding define_const_def brule_const_def rewto_const_def sig_is_def gen_in_hcls_def apply simp
    apply (triv, simp)+
    by simp

lemma [expl_frule]:
  "gen_in_hcls (Cons hcl hcls_rest) hcls
  ==>  in_hcls hcl hcls  &&& gen_in_hcls hcls_rest hcls "
  apply (simp add: gen_in_hcls_def in_hcls_def)
  by (triv, simp) simp



definition trms_const where
  [MRjud 3 0]: "trms_const s t sig == Signature.trms (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig) s t"
definition compatAtm_const where
  [MRjud 2 0]: "compatAtm_const atm sig ==
    Signature.compatAtm (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig) (rarOf_pr sig) (rarOfP_pr sig) (set (prels_pr sig)) atm"
definition compatHcl_const where
  [MRjud 2 0]: "compatHcl_const hcl sig ==
    Signature.compatHcl (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig) (rarOf_pr sig) (rarOfP_pr sig) (set (prels_pr sig)) hcl"

abbreviation trms where
  "trms sig s t == trms_const s t sig"
abbreviation compatAtm where
  "compatAtm sig atm == compatAtm_const atm sig"
abbreviation compatHcl where
  "compatHcl sig hcl == compatHcl_const hcl sig"

definition trmss_const where
  [MRjud 3 0]: "trmss_const ss ts sig == list_all2 (trms sig) ss ts"
abbreviation
  "trmss sig ss ts == trmss_const ss ts sig"


lemma trmss_nilD: "trmss sig [] ts ==> (ts = [])"
  by (simp add: trmss_const_def)
lemma trmss_consD: "trmss sig (Cons s ss) ts ==> (EX t ts'. ts = Cons t ts' & trms sig s t & trmss sig ss ts')"
  apply (simp add: trmss_const_def) by auto


lemma [MR]: "
  trms sig s (Var s x)  " unfolding trms_const_def by (simp add: Signature.trms.simps)

lemma [MR]: "[|
    (stOf_pr sig sigma) simpto s  ;  (arOf_pr sig sigma) simpto ss  ;
    length ps simpto i  ; length (arOfP_pr sig sigma)  simpto i  ;  trmss sig ss xs  |] ==>
  trms sig s (Op sigma ps xs)  "
    unfolding trms_const_def apply(simp add: Signature.trms.simps) unfolding simpto_const_def
    by (auto simp add: trmss_const_def trms_const_def)


lemma trmss_base[MR]: "
  trmss sig [] []  " unfolding trmss_const_def by simp

lemma trmss_step[MR]: "trms sig s x ==> trmss sig ss xs ==>
  trmss sig (Cons s ss) (Cons x xs)  "
    unfolding trmss_const_def by simp



definition member where
  [MRjud 2 0]: "member x xs == x : set xs"

(* low prio *)
lemma member_step[MR]: "member y xs ==>
  member y (Cons x xs)  " unfolding member_def by simp

(* high prio *)
lemma member_yes[MR]: "
  member x (Cons x xs)  " unfolding member_def by simp


lemma compatAtm_Pcond[MR]: "[|  prels_pr sig simpto prels  ;  member (R, ps) prels  ;
    length ps simpto i  ;  length xs simpto i  |] ==>
  compatAtm sig (Pcond R ps xs)  "
    unfolding compatAtm_const_def Signature.compatAtm_def member_def simpto_const_def by simp
lemma compatAtm_Eq[MR]: "[|  trms sig s t1  ;  trms sig s t2  |] ==>
  compatAtm sig (Eq s t1 t2)  "
    unfolding compatAtm_const_def trms_const_def Signature.compatAtm_def mem_def
    by simp
lemma compatAtm_Rl[MR]: "[|  (length ps) simpto i  ;  rarOfP_pr sig simpto rarOfP  ;
    rarOf_pr sig simpto rarOf  ;
    length (rarOfP rel) simpto i  ;
    rarOf rel simpto ar  ;
    trmss sig ar xs  |] ==>
  compatAtm sig (Rl rel ps xs)  "
    unfolding compatAtm_const_def trms_const_def Signature.compatAtm_def trmss_const_def simpto_const_def
    by simp



lemma compatHcl_eq[MR]: "compatAtm sig (Eq s t1 t2)  ==>
  compatHcl sig (Horn [] (Eq s t1 t2))"
unfolding compatHcl_const_def compatAtm_const_def trmss_const_def Signature.compatHcl_def by simp

lemma compatHcl_rel[MR]: "compatAtm sig (Rl rl ps ts)  ==>
  compatHcl sig (Horn [] (Rl rl ps ts))"
unfolding compatHcl_const_def compatAtm_const_def trmss_const_def Signature.compatHcl_def by simp

lemma compatHCL_step[MR]: "[|  compatHcl sig (Horn as a2)  ;  compatAtm sig a  |] ==>
  compatHcl sig (Horn (Cons a as) a2)"
unfolding compatHcl_const_def compatAtm_const_def Signature.compatHcl_def by simp



definition
  compatHcls :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig
    => ('sort,'opsym,'rlsym,'psort,'paramuni) hcl list => bool" where
  [MRjud 2 0]: "compatHcls sig hcls == (ALL hcl : set hcls. compatHcl sig hcl)"

lemma [MR]: "
  compatHcls sig []  "
    unfolding compatHcls_def by simp

lemma [MR]: "[|  compatHcl sig hcl  ;  compatHcls sig hcls  |] ==>
  compatHcls sig (Cons hcl hcls)  "
    unfolding compatHcls_def by simp



definition
  inhab :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => 'sort => bool" where
  [MRjud 2 0]: "inhab sig == Signature.inhab (stOf_pr sig) (arOf_pr sig)"

definition
  inhabimpl :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => 'sort list => 'sort => bool" where
  [MRjud 3 0]: "inhabimpl sig ss s == ((ALL s2 : set ss. inhab sig s2) --> inhab sig s)"




lemma [expl_frule]: "
  inhabimpl sig [] s
  ==>  inhab sig s  "
unfolding inhab_def inhabimpl_def by auto

lemma [expl_frule]: "[|
  inhabimpl sig (Cons s ss) s2  &&&  inhab sig s |]
  ==>  inhabimpl sig ss s2  "
unfolding inhabimpl_def apply simp apply (erule conjunctionE) by auto

lemma [expl_frule]: "[|
  sig_is sig  &&&  oper_to_opsym c C  ;  (stOf_pr sig C) simpto s  ;  (arOf_pr sig C) simpto ss  |]
  ==>  inhabimpl sig ss s  "
unfolding inhabimpl_def apply rule unfolding inhab_def simpto_const_def
  by (rule Signature.inhabI) auto




(* explicit judgement parameter to ease higher-order dependency analysis *)
definition lookup_conjs_const where
  [MRjud 2 0]: "lookup_conjs_const P J == P"
abbreviation
  lookup_conjs :: "'a => bool => bool" where
  "lookup_conjs J P == lookup_conjs_const P J"

(* unchecked to avoid dependency analysis declaring dependency on ARB judgement because P could be anything *)
lemma [MR_unchecked]: "  P  ==>
  lookup_conjs J P " by (simp add: lookup_conjs_const_def)

lemma [MR]: "[|  lookup_conjs J Q  ;  lookup_conjs J Q2  |] ==>
  lookup_conjs J (Q & Q2)  " by (simp add: lookup_conjs_const_def)

lemma [MR]: "
  lookup_conjs J True  " by (simp add: lookup_conjs_const_def)




definition lookup_inhab_conjs :: "bool => bool" where
  [MRjud 1 0]: "lookup_inhab_conjs P == P"

lemma [MR]: "[|
    sort_to_name_and_type s n Tdummy  ;
    errwith ''non-emptiness check failed for sort'' 0 n  |] ==>
  lookup_inhab_conjs (inhab sig s)  "  by (simp add: errwith_def)

lemma [MR]: "  try(  inhab sig s  )  ==>
  lookup_inhab_conjs (inhab sig s) "
  by (simp add: try_const_def lookup_inhab_conjs_def)

lemma [MR]: "[|  lookup_inhab_conjs Q  ;  lookup_inhab_conjs Q2  |] ==>
  lookup_inhab_conjs (Q & Q2)  " by (simp add: lookup_inhab_conjs_def)

lemma [MR]: "
  lookup_inhab_conjs True  " by (simp add: lookup_inhab_conjs_def)



term "HornTheory"
thm HornTheory_def

definition
  [MRjud 1 0]: "NonFreeMetaTheory sig == HornTheory  (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig)
     (rarOf_pr sig) (rarOfP_pr sig) (params_pr sig) (set (prels_pr sig)) (set (hcls_pr sig))"



(* tabulate arOfP, rarOfP *)
definition
  tabulate_arOfP :: "('opsym * 'psort list) list => ('relsym * 'psort list) list => bool" where
  [MRjud 2 0]: "tabulate_arOfP ars rars == True"
lemma tabulate_arOfPI[intro]: "tabulate_arOfP ars rars " by (simp add: tabulate_arOfP_def)
lemma tabulate_arOfP_easyI: "ars == ars ==> rars == rars ==> tabulate_arOfP ars rars "
  by (simp add: tabulate_arOfP_def)

definition
  process_opsym_conj ::  "('sort,'opsym,'rlsym,'psort,'paramuni) sig => bool => ('opsym * 'psort list) list => bool" where
  [MRjud 2 1]: "process_opsym_conj sig P ars == True"
lemma [intro]: "process_opsym_conj sig P ars" by (simp add: process_opsym_conj_def)

definition
  process_relsym_conj ::  "('sort,'opsym,'rlsym,'psort,'paramuni) sig => bool => ('rlsym * 'psort list) list => bool" where
  [MRjud 2 1]: "process_relsym_conj sig P rars == True"
lemma [intro]: "process_relsym_conj sig P rars" by (simp add: process_relsym_conj_def)


lemma [MR]: "[|
    process_opsym_conj sig Q1 ars1 ;
    process_opsym_conj sig Q2 ars2 |] ==>
  process_opsym_conj sig (Q1 & Q2) (ars1 @ ars2) " ..

lemma [MR]: "
  process_opsym_conj (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig)
    True ([] :: ('opsym * 'psort list) list)" ..

lemma [MR]: "
    arOfP_pr sig opsym  simpto  ar  ==>
  process_opsym_conj sig (opsym = opsym) [(opsym, ar)]" ..




lemma [MR]: "[|
    process_relsym_conj sig Q1 ars1 ;
    process_relsym_conj sig Q2 ars2 |] ==>
  process_relsym_conj sig (Q1 & Q2) (ars1 @ ars2) " ..

lemma [MR]: "
  process_relsym_conj (sig :: ('sort,'opsym,'relsym,'psort,'paramuni) sig)
    True ([] :: ('relsym * 'psort list) list)" ..

lemma [MR]: "
    rarOfP_pr sig relsym  simpto  rar  ==>
  process_relsym_conj sig (relsym = relsym) [(relsym, rar)]" ..

ML {*
  structure Tabulate_arOfP_Data = Generic_Data(
    type T = (term list) Net.net
    val empty = Net.empty
    val extend = I
    fun merge (net1, net2) = Net.merge (K true) (net1, net2)
  );
  fun tabulate_arOfP_lthytransform (ars_ct, [rars_ct]) lthy =
    let
      val ars = metaize_list (Thm.term_of ars_ct)
      val rars = metaize_list (Thm.term_of rars_ct)
      (* TODO(refactor): store in aux ctxt only *)
      val lthy2 = lthy |> MetaRec.add_non_pervasive_declaration (fn _ =>
         Tabulate_arOfP_Data.map (
           fold (fn t => Net.insert_term (K true) (HOLogic.dest_prod t |> apsnd metaize_list))
             (ars @ rars)))
      val thy2 = ProofContext.theory_of lthy2
      val th = @{thm tabulate_arOfP_easyI} OF
        (map Thm.reflexive [ars_ct, rars_ct])
    in
      ((th, []), lthy2)
   end
*}

setup {*
  Context.theory_map (MetaRec.add_lthy_transform "NonFree.tabulate_arOfP_jud" "tabulate_arOfP_lthytransf"
    tabulate_arOfP_lthytransform)
*}




(* NB: I don't use  lookup_conjs (inhab sig)  to make higher-order dependency analysis easier *)
lemma NonFreeMetaTheoryI[expl_frule]: "[|
  sig_is (sig :: ('sort,'opsym,'relsym,'psort,'paramuni) sig) ;
  hcls_pr sig  simpto  hcls  ;
  params_pr sig  simpto  params  ;
  compatHcls sig hcls  ;

  enum_datatype_quant_unrollrew (ALL s. inhab sig s) Q   ;
  lookup_inhab_conjs Q  ;

  enum_datatype_quant_unrollrew (ALL ps. inhab_params (params ps)) Q2  ;
  lookup_conjs (inhab_params :: 'paramuni set => bool) Q2  ;

  enum_datatype_quant_unrollrew (ALL x::'opsym. x = x) opsym_conj  ;
  enum_datatype_quant_unrollrew (ALL x::'relsym. x = x) relsym_conj  ;
  process_opsym_conj sig opsym_conj ars  ;
  process_relsym_conj sig relsym_conj rars  ;
  ars  simpto  ars2  ;
  rars  simpto  rars2  ;
  tabulate_arOfP ars2 rars2  |]
  ==> NonFreeMetaTheory sig "
  unfolding NonFreeMetaTheory_def HornTheory_def compatHcls_def compatHcl_const_def inhab_def
    inhab_params_def enum_datatype_quant_unrollrew_def lookup_inhab_conjs_def
    lookup_conjs_const_def simpto_const_def tabulate_arOfP_def
  by simp


term "HornTheory.Hop"
thm HornTheory.Hop_def
definition
  intOpHCL :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => 'opsym =>
   'paramuni list => ('sort,'opsym,'paramuni) trmHCL list => ('sort,'opsym,'paramuni) trmHCL"
where
  [MRjud 1 0]: "intOpHCL sig == HornTheory.Hop (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig) (rarOfP_pr sig)
                   (params_pr sig) (set (hcls_pr sig))"


thm HornTheory.htrms_def
definition trmsHCL :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig
    => 'sort => ('sort,'opsym,'paramuni) trmHCL set" where
  [MRjud 1 0]: "trmsHCL sig == HornTheory.htrms (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig)
                  (rarOfP_pr sig) (params_pr sig) (set (hcls_pr sig))"

thm HornTheory.Hrel_def
definition
  intRlHCL :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => 'rlsym =>
    'paramuni list => ('sort,'opsym,'paramuni) trmHCL list => bool" where
  [MRjud 1 0]: "intRlHCL sig == HornTheory.Hrel (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig)
                  (rarOfP_pr sig) (params_pr sig) (set (hcls_pr sig))"

thm "HornTheory.compat_Hop"


lemma bij_typ: "bij_betw f A B ==> x : A ==> f x : B"
  unfolding bij_betw_def by auto

lemma intOpHCL_trmsHCL[simp]:
assumes sig: "NonFreeMetaTheory sig"
and ps: "list_all2 (params_pr sig) (arOfP_pr sig \<sigma>) ps"
and Hs: "list_all2 (trmsHCL sig) (arOf_pr sig \<sigma>) Hs"
shows "intOpHCL sig \<sigma> ps Hs \<in> trmsHCL sig (stOf_pr sig \<sigma>)"
proof-
  let ?stOf = "stOf_pr sig"  let ?arOfP = "arOfP_pr sig"
  let ?arOf = "arOf_pr sig"  let ?rarOfP = "rarOfP_pr sig"
  let ?params = "params_pr sig"  let ?HCL = "set (hcls_pr sig)"
  let ?intSt = "trmsHCL sig"  let ?intOp = "intOpHCL sig"
  have "Signature.compat ?stOf ?arOfP ?arOf ?params (trmsHCL sig) (intOpHCL sig)"
  unfolding trmsHCL_def intOpHCL_def
  apply(rule HornTheory.compat_Hop)
  using sig unfolding NonFreeMetaTheory_def .
  thus ?thesis unfolding mem_def
  by(rule Signature.compat_elim[of ?stOf ?arOfP ?arOf ?params ?intSt ?intOp, OF _ ps Hs])
qed

(* fixme: move where belongs: *)
lemma carOf_sset_fun_setoid[simp]:
"carOf ((sset A) ~s~> (sset B)) = funSS A B"
unfolding fun_setoid_def sset_def sfun_eq_def_raw funS_def by auto

lemma  intOpHCL_fun_setoid[simp]:
assumes "NonFreeMetaTheory sig"
shows "intOpHCL sig \<sigma> \<in> carOf(
       (sset (list_all2 (params_pr sig) (arOfP_pr sig \<sigma>)) ~s~>
        sset (list_all2 (trmsHCL sig) (arOf_pr sig \<sigma>)) ~s~>
        sset (trmsHCL sig (stOf_pr sig \<sigma>))))"
by (metis assms carOf_sset elem_setdom_funsetoid fun_setoid
          intOpHCL_trmsHCL mem_def set_setoid)

lemma [expl_frule]: "[|
  NonFreeMetaTheory sig &&& oper_to_opsym c opsym  ;
    uar_of_sym opsym uar  ;
    (map (params_pr sig) (arOfP_pr sig opsym)) simpto As  ;
    (map (trmsHCL sig) (arOf_pr sig opsym)) simpto Bs  ;
    trmsHCL sig (stOf_pr sig opsym) simpto C  ;
    (curry_iso (Some uar) reify_iso): (sset (product As) ~s~> sset (product Bs) ~s~> sset C) isoto DD via f  ;
    define c := f (intOpHCL sig opsym) giving c' |]
  ==>
     invariant (intOpHCL sig opsym, intOpHCL sig opsym) (sset (product As) ~s~> sset (product Bs) ~s~> sset C)  &&&
     (curry_iso None reify_iso): (intOpHCL sig opsym) : (sset (product As) ~s~> sset (product Bs) ~s~> sset C)
         isomapto  c' : DD via f  &&&
     userar_decl (intOpHCL sig opsym) uar"
apply(intro Pure.conjunctionI)
  unfolding invariant_def apply(intro conjI)
    unfolding simpto_const_def define_const_def
              atomize_eq curry_iso_def atomize_conj isotovia_const_def
    apply (force, force, force)
    unfolding simpto_const_def atomize_eq curry_iso_def atomize_conj isomapto_via_def
    apply(intro conjI)
      apply force
      apply (metis  (no_types) product_list_all2 intOpHCL_fun_setoid iso_sDfunsp sfun_ty)
      apply force
      apply (metis iso_sDsetoid(2))
      apply force
      apply (metis (no_types) intOpHCL_fun_setoid iso_sDsetoid(1)
                   iso_sDwf product_list_all2 srefl)
    unfolding userar_decl_def ..

(* softtyping is trivial to prove! *)
lemma [expl_frule]: "[|
  NonFreeMetaTheory sig &&& rel_to_relsym R relsym  ;
    uar_of_sym relsym uar  ;
    (map (params_pr sig) (rarOfP_pr sig relsym)) simpto As  ;
    (map (trmsHCL sig) (rarOf_pr sig relsym)) simpto Bs  ;
    (sset (product As) ~s~> sset (product Bs) ~s~> (UNIV_s :: bool setoid)) matches AA  ;
    (curry_iso (Some uar) reify_iso): AA isoto AA' via f  ;
    define R := f (intRlHCL sig relsym) giving R' |]
  ==>
    invariant (intRlHCL sig relsym, intRlHCL sig relsym) AA   &&&
    (curry_iso None reify_iso):
          (intRlHCL sig relsym) : (sset (product As) ~s~> sset (product Bs) ~s~> (UNIV_s :: bool setoid))
            isomapto  R' : AA' via f  &&&
    userar_decl (intRlHCL sig relsym) uar"
apply(intro Pure.conjunctionI)
  unfolding invariant_def fst_conv snd_conv simpto_const_def
  unfolding matches_const_def apply(intro conjI)
    apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
    apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
    apply (metis eq_UNIV_sI fun_setoid_eqOf_eq sfun_eq_def)
    unfolding curry_iso_def isomapto_via_def apply(intro conjI)
      apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
      unfolding define_const_def atomize_eq isotovia_const_def
      apply (metis (no_types) UNIV_I carOf_sset elem_setdom_funsetoid fun_setoid
                   fun_setoid_carOf_eq iso_sDfunsp set_setoid sfun_ty)
      apply (metis iso_sDsetoid(1))
      apply (metis iso_sDsetoid(2))
      apply assumption
      unfolding iso_s_def mem_Collect_eq
      apply (metis (no_types) elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid srefl)  unfolding userar_decl_def ..


definition reified_name where
  "reified_name == (0 :: nat)"


lemma [expl_frule]: "
  NonFreeMetaTheory sig  &&&  sort_to_name_and_type s ndummy Tdummy
  ==> nonempty (trmsHCL sig s) "
    unfolding nonempty_def trmsHCL_def NonFreeMetaTheory_def
    apply (drule conjunctionD1)
    unfolding mem_def
    by (rule HornTheory.ex_htrms)

lemma type_definition_bij_betw:
assumes "type_definition Rep Abs A"
shows "bij_betw Abs A UNIV"
using assms unfolding type_definition_def bij_betw_def inj_on_def
by (metis assms type_definition.Abs_image)

lemma [expl_frule]: "[|
  sort_to_name_and_type s n Tdummy  &&&  NonFreeMetaTheory sig  &&& nonempty (trmsHCL sig s)  ;
    decl_tyvars () alphas  ;
    typedef n alphas via (tyvar_interpr :: tyvar => dummyT itself => bool)
      := trmsHCL sig s gives TYPE('tau) Rep Abs  |]
  ==>  reify_iso:  (sset (trmsHCL sig s))  isoto  (UNIV_s :: 'tau setoid) via Abs  "
   unfolding typedef_const_def isotovia_const_def
   atomize_conj apply(rule bij_to_equi) by(rule type_definition_bij_betw)





(* satHCL processing *)


(* collecting variables coded in ML for speed *)
ML {*
  fun fold_applied_heads f t =
    let val (_, ts) = strip_comb t
    in
      f t #> fold (fold_applied_heads f) ts
    end ;

  fun veq ((s1, v1), (s2, v2)) = s1 aconv s2 andalso v1 aconv v2 ;
  fun arOfP lthy opsym =
    case Net.lookup (Tabulate_arOfP_Data.get (Context.Proof lthy)) (Net.key_of_term opsym) of
      [ar] => ar
    | ars => error ("Tabulate_arOfP_Data lookup for sym "^Syntax.string_of_term lthy opsym
       ^" is non-singular: "^PolyML.makestring ars)
  val rarOfP = arOfP

  fun collect_vars lthy t = ([], [])
    |> fold_applied_heads
        (fn (Const(@{const_name Var}, _) $ s $ v) =>
            apsnd (insert veq (s, v))
         |  (Const(@{const_name Op}, _) $ opsym $ pvs $ _) =>
            apfst (fold (insert veq) (arOfP lthy opsym ~~ metaize_list pvs))
         |  (Const(@{const_name Rl}, _) $ relsym $ pvs $ _) =>
            apfst (fold (insert veq) (rarOfP lthy relsym ~~ metaize_list pvs))
         | (Const(@{const_name Pcond}, _) $ _ $ pss $ pvs) =>
            apfst (fold (insert veq) (metaize_list pss ~~ metaize_list pvs))
         | _ => I)
        t
    |> pairself rev ;
*}

ML {*
  case @{typ "('sort,'opsym,'rlsym,'psort,'paramuni) sig"} of
    Type(tycon, l) => (tycon, l)
*}


definition
  collectVarsHcl :: "('sort,'opsym,'relsym,'psort,'paramuni) hcl => ('sort,'opsym,'relsym,'psort,'paramuni) sig =>
                       ('psort * pvar) list * ('sort * var) list => bool" where
  [MRjud 2 1]: "collectVarsHcl H sig ls == True"
lemma collectVarsHclI[intro]: "collectVarsHcl H sig ls" by (simp add: collectVarsHcl_def)
lemma collectVarsHcl_easyI: "H ==H ==> sig == sig ==> ls == ls ==> collectVarsHcl H sig ls"
  by (simp add: collectVarsHcl_def)

ML {*
  fun collectVarsHcl_proc ctxt (clause_ct, [sig_ct], _) =
    let
      val thy = ProofContext.theory_of ctxt
      val (sortT, psortT) = case Thm.ctyp_of_term sig_ct |> Thm.typ_of of
          Type("NonFree.sig.sig_ext", [sortT, _, _, psortT, _, _]) => (sortT, psortT)
        | _ => error "collectVarsHcl_proc: sig_t not of signature type"

      val (pvs, vs) = collect_vars ctxt (Thm.term_of clause_ct)
      val res_ct = HOLogic.mk_prod (
          pvs |> map HOLogic.mk_prod |> holize_list thy (HOLogic.mk_prodT (psortT, @{typ "pvar"})),
          vs |> map HOLogic.mk_prod |> holize_list thy (HOLogic.mk_prodT (sortT, @{typ "var"})))
        |> cterm_of thy
      val th = @{thm "collectVarsHcl_easyI"} OF (map Thm.reflexive [clause_ct, sig_ct, res_ct])
    in
      (th, [res_ct])
    end
*}

setup {*
  Context.theory_map (MetaRec.add_syn_proc "NonFree.collectVarsHcl_jud" "collectVarsHcl_proc" collectVarsHcl_proc)
*}





(* now implicit in Signature *)
definition compatPvar where
  "compatPvar sig == (% intPvar. (ALL ps px. params_pr sig ps (intPvar ps px)))"
definition compatVar where
  "compatVar == (% intSt intVar. (ALL s x. intSt s (intVar s x)))"

lemma compatPvar_hlp:
"compatPvar sig intPvar = (intPvar \<in> (PI ps : UNIV. UNIV -> params_pr sig ps))"
unfolding compatPvar_def Pi_def by (smt Collect_def iso_tuple_UNIV_I mem_def)

lemma compatPvar_as_set: "compatPvar sig = (PI ps: UNIV. UNIV -> params_pr sig ps)"
  apply (rule ext) by (simp add: compatPvar_hlp mem_def)

lemma compatVar_hlp: "compatVar intSt intVar = (intVar : (PI s : UNIV. UNIV -> intSt s))"
unfolding compatVar_def Pi_def by (smt Collect_def iso_tuple_UNIV_I mem_def)

lemma compatVar_as_set: "compatVar intSt = (PI s : UNIV. UNIV -> intSt s)"
  apply (rule ext) by (simp add: compatVar_hlp mem_def)

thm Signature.intTrm_def
definition intTrm where
  "intTrm sig == (% intSt. Signature.intTrm (arOfP_pr sig))"
definition satAtm where
  "satAtm sig == (% intSt. Signature.satAtm (arOfP_pr sig) (rarOfP_pr sig))"
definition
  "satHcl sig == Signature.satHcl (arOfP_pr sig) (rarOfP_pr sig) (params_pr sig)"

lemma [MR]: "
  holdsAll P [] --> Q  rewto  Q  " by (simp add: rewto_const_def)
lemma [MR]: "
  holdsAll P (Cons x xs) --> Q  rewto  P x --> holdsAll P xs --> Q  " by (simp add: rewto_const_def imp_conjL)



definition update2 where
  "update2 x1 x2 y f = (% x1' x2'. if x1 = x1' & x2 = x2' then y else f x1' x2')"

lemma update2_lem1: "update2 x1 x2 (f x1 x2) f = f"
  apply (rule ext, rule ext)
  by (simp add: update2_def)
lemma update2_lem2:"update2 x1 x2 y f x1 x2 == y"
  by (simp add: update2_def)
lemma update2_lem3:"x1 ~= x1' ==> update2 x1 x2 y f x1' x2' == f x1' x2'"
  by (simp add: update2_def)
lemma update2_lem4:"x2 ~= x2' ==> update2 x1 x2 y f x1' x2' == f x1' x2'"
  by (simp add: update2_def)
lemma update2_lem5: "update2 x1 x2 y f x1' x2' ==
  (if x1 = x1' & x2 = x2' then y else f x1' x2')"
  by (simp add: update2_def)


lemma PiE': "f : (PI x:A. B x) ==> ((!! x. x : A ==> f x : B x) ==> P) ==> P" by auto
lemma PiE2': "f : (PI x:A. PI y : B. C x y) ==> ((!! x y. x : A ==> y : B ==> f x y : C x y) ==> P) ==> P" by auto


lemma unfold_piquant: "(ALL f : (PI a : UNIV. UNIV -> C a). P f)
       = (ALL y : (C :: 'a => 'c set) x1. (ALL f : (PI a : (UNIV :: 'a set). (UNIV :: 'b set) -> C a).
         P (update2 (x1 :: 'a) (x2 :: 'b) y f))) "
proof
  assume H:"ALL y:C x1. ALL f:PI a:UNIV. UNIV -> C a. P (update2 x1 x2 y f)"
  show "ALL f:PI a:UNIV. UNIV -> C a. P f"
  proof
   fix f :: "'a => 'b => 'c"
   assume fty: "f : (PI a:UNIV. UNIV -> C a)"
   hence applty: "f x1 x2 : C x1" by auto
   from H have H': "!! y f. y : C x1 ==> f : (PI a:UNIV. UNIV -> C a) ==> P (update2 x1 x2 y f)"  by auto
   from H'[OF applty fty] have "P (update2 x1 x2 (f x1 x2) f)" .
   thus "P f" by (simp add: update2_lem1)
  qed
next
  assume H: "ALL f:PI a:UNIV. UNIV -> C a. P f"
  show "ALL y:C x1. ALL f:PI a:UNIV. UNIV -> C a. P (update2 x1 x2 y f)"
  proof (rule+)
    fix y :: 'c and f :: "'a => 'b => 'c" assume yty: "y : (C x1)" and fty: "f : (PI a:UNIV. UNIV -> C a)"
    hence "(update2 x1 x2 y f) :  (PI a:UNIV. UNIV -> C a)" apply (simp add: update2_def)
    apply (rule Pi_I)+  apply (erule PiE2') apply (case_tac "x = x1") by simp+
    thus "P (update2 x1 x2 y f)" using H by auto
  qed
qed




definition
  reg_implication_curry_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_implication_curry_rews x == True"

lemma [impl_frule]:
  "reg_implication_curry_rews ()
  ==>
     brule(  (Q1 & Q2 --> Q')  rewto (Q1 --> Q2 --> Q')  ) &&&
     brule(  (True --> Q')  rewto  Q'  )  "
  by (triv, (simp add: brule_const_def rewto_const_def imp_conjL)+)



definition
  reg_vareval_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_vareval_rews x == True"

definition
  update2_rew :: "'a => 'a => bool" where
  [MRjud 1 1]: "update2_rew t t' == (t = t')"


lemma neq_simpto_TrueD: "x ~= x2 simpto True ==> x ~= x2"
  by (simp add: simpto_const_def)


lemma [MR]: "var n = var n2 rewto n = n2" by (simp add: rewto_const_def)
lemma [MR]: "pvar n = pvar n2 rewto n = n2" by (simp add: rewto_const_def)

(* only try to show unequality of variables, as we don't make use of
   sorts contributing to variable identity here *)
(*lemma (* [MR] *): "[|  x2 ~= x2' simpto True  ;  update2_rew (f x1' x2') z |] ==>
  update2_rew (update2 x1 x2 y f x1' x2')  z  "
  apply (drule neq_simpto_TrueD)
  by (simp add: update2_rew_def update2_def update2_lem4 simpto_const_def)

(* high prio *)
lemma (*[MR]*): "update2_rew (update2 x1 x2 y f x1 x2)  y"
  by (simp add: update2_rew_def update2_lem2) *)





fun
  list_to_ptupel
where
  "list_to_ptupel xs_sets Nil = pNil"
| "list_to_ptupel xs_sets (Cons x xs) =
     pCons (hd xs_sets) (tl xs_sets) x (list_to_ptupel (tl xs_sets) xs)"


lemma [MR]: "
  list_to_ptupel Nil Nil  rewto  pNil  "
  by (simp add: rewto_const_def)
lemma [MR]: "
  list_to_ptupel (Cons x_set xs_sets) (Cons x xs)  rewto
     pCons x_set xs_sets x (list_to_ptupel xs_sets xs)"
  by (simp add: rewto_const_def)


lemma list_to_ptupel_simp: "list_to_ptupel xs_sets xs = xs"
  apply (induct xs arbitrary: xs_sets)
  apply (simp add: pNil_def)
  by (simp add: pCons_def)


lemma [impl_frule]: "
  reg_vareval_rews ()
  ==>
    brule(  (update2 x1 x2 y f x1' x2')  rewto  (if x1 = x1' & x2 = x2' then y else f x1' x2')  ) &&&
    brule(  (if True then e1 else e2) rewto e1  ) &&&
    brule(  (if False then e1 else e2) rewto e2  ) &&&

    brule(  intTrm sig intSt intOp intPvar intVar (Var s x)  rewto  intVar s x  ) &&&
    brule(  intTrm sig intSt intOp intPvar intVar (Op sigma pvl ts)  rewto
      intOp sigma
        (list_to_ptupel (map (params_pr sig) (arOfP_pr sig sigma))
           (map2 intPvar (arOfP_pr sig sigma) pvl))
        (list_to_ptupel (map intSt (arOf_pr sig sigma))
           (map (intTrm sig intSt intOp intPvar intVar) ts))  )  &&&
    brule(  satAtm sig intSt intOp (op =) intRl intPvar intVar (Pcond R psl pxl)  rewto
      R (list_to_ptupel (map (params_pr sig) psl)
           (map2 intPvar psl pxl))  )  &&&
    brule(  satAtm sig intSt intOp (op =) intRl intPvar intVar (Eq s t1 t2)  rewto
      eqOf (sset (intSt s)) (intTrm sig intSt intOp intPvar intVar t1)
        (intTrm sig intSt intOp intPvar intVar t2)  ) &&&
    brule(  satAtm sig intSt intOp (op =) intRl intPvar intVar (Rl rl pxl ts)  rewto
      intRl rl
        (list_to_ptupel (map (params_pr sig) (rarOfP_pr sig rl)) (map2 intPvar (rarOfP_pr sig rl) pxl))
        (list_to_ptupel (map intSt (rarOf_pr sig rl)) (map (intTrm sig intSt intOp intPvar intVar) ts))  )  "
   unfolding rewto_const_def brule_const_def try_const_def simpto_const_def
   apply (simp add: list_to_ptupel_simp)
   apply (intro Pure.conjunctionI)
   apply (simp add: update2_lem5) apply simp+
   by (simp add: intTrm_def Signature.intTrm.simps satAtm_def Signature.satAtm_def Signature.satPcond_def
     Signature.satEq_def Signature.satRl_def)+




definition
  reg_prod_unfold_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_prod_unfold_rews x == True"

lemma [impl_frule]: "
  reg_prod_unfold_rews ()
  ==>
    brule(  (ALL xs : product []. P(xs))  rewto  P(pNil)  )  &&&
    brule(  (ALL xs : product (Cons A As). P(xs))  rewto
      (SALL x : sset A. ALL xs : product As. P(pCons A As x xs))  )"
    unfolding brule_const_def rewto_const_def
    apply (rule Pure.conjunctionI)
    apply (simp add: pNil_def)
    apply (simp add: pCons_def SALL_on_sset)
    apply (rule eq_reflection)
    by auto








definition
  unroll_v_quant :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => ('sort * var) list => bool => bool => bool" where
  [MRjud 3 1]: "unroll_v_quant sig vs P P' == (P = P')"
definition
  unroll_pv_quant :: "('sort,'opsym,'rlsym,'psort,'paramuni) sig => ('psort * pvar) list * ('sort * var) list
    => bool => bool => bool" where
  [MRjud 3 1]: "unroll_pv_quant sig vs P P' == (P = P')"

(* lemma "(ALL x : A. P x) == (ALL y : A. P (update2 s v y x)" *)

lemma alleqI: "(!! x. x : A ==> P x = P' x) ==> (ALL x: A. P x) = (ALL x: A. P' x)"
  by auto

lemma [MR]: "[|  !! x.  x : intSt s  ==>
    unroll_v_quant sig vs
      (ALL intVar : compatVar intSt . P(update2 s v x intVar))
      (P'(x))  |] ==>
  unroll_v_quant sig (Cons (s, v) vs) (ALL intVar : compatVar intSt. P(intVar))
    (SALL x : sset (intSt s). P'(x))  "
  unfolding unroll_v_quant_def
   apply (simp add: compatVar_as_set SALL_on_sset)
   apply (subst unfold_piquant)
   apply (rule alleqI)
   by auto



definition
  images_nonempty :: "('a => 'b set) => bool" where
  [MRjud 1 0]: "images_nonempty f == (ALL x. EX y. f x y)"

lemma images_nonempty_AC_D: "images_nonempty f ==> (EX g. ALL x z. f x (g x z))"
  unfolding images_nonempty_def
  apply (rule choice)
  by auto


(* Vorbedingung: reg_vareval_rews, reg_implication_curry_rews
   schon im Kontext vom Aufrufer ausgefuehrt wurden *)
lemma [MR]: "[|
      P0 simpto (ALL (intVar :: 'a => 'b => 'c) : compatVar intSt. P)  ;
     images_nonempty intSt   |] ==>
  unroll_v_quant sig [] P0 P  "
    apply (drule images_nonempty_AC_D)
    apply (simp add: unroll_v_quant_def simpto_const_def compatVar_def mem_def)
    proof -
      assume H: "EX (g :: 'a => 'b => 'c). ALL x z. intSt x (g x z)"
      show "((EX (intVar :: 'a => 'b => 'c). ALL s x. intSt s (intVar s x)) --> P) = P"
        by (simp add: H)
    qed

lemma [MR]: "[|  P0 simpto (ALL (intPvar :: 'a => 'b => 'c) : compatPvar sig. P)  ;
    images_nonempty (params_pr sig)  ;  unroll_v_quant sig vs P P'  |] ==>
  unroll_pv_quant sig ([], vs) P0 P'  "
    apply (simp add: unroll_v_quant_def unroll_pv_quant_def simpto_const_def compatPvar_def mem_def)
    apply (drule images_nonempty_AC_D)
    proof -
      assume H: "EX g::'a => 'b => 'c. ALL (x::'a) z::'b. params_pr sig x (g x z)"
      show "((EX intPvar::'a => 'b => 'c. ALL (ps::'a) px::'b. params_pr sig ps (intPvar ps px)) --> P') = P'"
         by (simp add: H)
    qed




lemma [MR]: "[|  params_pr sig simpto params  ;
    !! x.  x : params ps  ==>
      unroll_pv_quant sig (pvs, vs)
        (ALL intPvar : compatPvar sig. P(update2 ps pv x intPvar))
        (P'(x))  |] ==>
  unroll_pv_quant sig (Cons (ps, pv) pvs, vs) (ALL intPvar : compatPvar sig. P(intPvar))
    (SALL x : sset (params ps). P'(x))  "
  unfolding unroll_pv_quant_def simpto_const_def
   apply (simp add: compatPvar_as_set SALL_on_sset)
   apply (subst unfold_piquant)
   apply (rule alleqI)
   by auto

definition sat_in_termmodel_name where
  "sat_in_termmodel_name = (0 :: nat)"

definition
  [MRjud 1 0]: "reg_setoid_prop_rew x == True"

lemma [impl_frule]:  "
  reg_setoid_prop_rew ()
  ==>  reg_UNIV_s_rew ()  &&&
       brule(  (SALL x:UNIV_s. P x)  rewto  (ALL x. P x)  )  &&&
       brule(  (eqOf UNIV_s t1 t2)  rewto  (t1 = t2)  )"
  apply (simp add: brule_const_def rewto_const_def setoid_all_def eqOf_UNIV_s reg_UNIV_s_rew_def)
  by (triv, simp, triv) simp

definition
  reg_atomize_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_atomize_rews x == True"

lemma reg_atomize_rews[impl_frule]: "
  reg_atomize_rews ()
  ==>
    brule(  (Trueprop (P1 & P2))  rewto  (P1 &&& P2)  )  &&&
    brule(  (Trueprop (P1 --> P2))  rewto  (P1 ==> P2)  )  &&&
    brule(  (Trueprop (ALL x. P x))  rewto  (!! x. P x)  )  "
  unfolding brule_const_def rewto_const_def
  apply (rule conjunctionI)
  apply rule apply (rule conjunctionI, simp, simp)
  apply (erule conjunctionE) apply simp
  apply (rule conjunctionI) apply (rule, blast, blast)
  by (rule, blast+)


lemma isomapto_via_idD: "phi: t : UNIV_s isomapto t' : UNIV_s via id ==> t = t'"
  unfolding isomapto_via_def
  by simp

lemma NonFreeMetaTheory_images_nonempty_params_pr:
assumes "NonFreeMetaTheory (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig)"
shows "images_nonempty (params_pr sig)"
using assms
unfolding NonFreeMetaTheory_def HornTheory_def images_nonempty_def by auto

lemma NonFreeMetaTheory_images_nonempty_trmsHCL:
assumes "NonFreeMetaTheory (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig)"
shows "images_nonempty (trmsHCL sig)"
using assms unfolding NonFreeMetaTheory_def HornTheory_def images_nonempty_def
using HornTheory.inhab_imp_ex_htrms unfolding trmsHCL_def
by (metis HornTheory.ex_htrms NonFreeMetaTheory_def assms)

(* TODO Andy: get rid of holdsAll(2) and metamap: use list_all(2) instead *)
lemma holdsAll[simp]:
"holdsAll = list_all"
proof(intro ext)
  fix \<phi> xs show "holdsAll \<phi> xs = list_all \<phi> xs"
  apply(induct xs) by auto
qed

lemma holdsAll2_length:
assumes "holdsAll2 \<phi> xs ys"
shows "length xs = length ys"
using assms apply(induct xs arbitrary: ys) by auto

lemma holdsAll2[simp]:
"holdsAll2 = list_all2"
proof(intro ext)
  fix \<phi> xs ys
  show "holdsAll2 \<phi> xs ys = list_all2 \<phi> xs ys"
  proof-
    {assume "length xs = length ys"
     hence ?thesis
     apply(induct rule: list_induct2) by auto
    }
    thus ?thesis
    using holdsAll2_length list_all2_lengthD by blast
  qed
qed

lemma metamap_length:
assumes "metamap \<phi> xs ys"
shows "length xs = length ys"
using assms apply(induct) by auto

lemma metamap[simp]:
"metamap = list_all2"
proof(intro ext)
  fix \<phi> xs ys
  show "metamap \<phi> xs ys = list_all2 \<phi> xs ys"
  proof-
    {assume "length xs = length ys"
     hence ?thesis
     apply(induct rule: list_induct2)
       apply (metis list_all2_Nil metamap_nil)
       by (simp, smt impossible_Cons list.inject list.size(3) metamap.simps)
    }
    thus ?thesis
    using metamap_length list_all2_lengthD by blast
  qed
qed

lemma sat_HCL:
assumes nf: "NonFreeMetaTheory sig" and hcl: "in_hcls hcl (hcls_pr sig)"
shows "satHcl sig (trmsHCL sig) (intOpHCL sig) (op =) (intRlHCL sig) hcl"
using assms unfolding NonFreeMetaTheory_def in_hcls_def
unfolding satHcl_def trmsHCL_def intOpHCL_def intRlHCL_def
by (rule HornTheory.sat_HCL)

lemma holdsAtm:
assumes nf: "NonFreeMetaTheory sig"
and hcls: "in_hcls (Horn atms atm) (hcls_pr sig)"
and ipv: "intPvar \<in> compatPvar sig" and iv: "intVar \<in> compatVar (trmsHCL sig)"
and ha:
"holdsAll
   (satAtm sig (trmsHCL sig) (intOpHCL sig) (op =) (intRlHCL sig) intPvar intVar)
   atms"
shows "satAtm sig (trmsHCL sig) (intOpHCL sig) (op =) (intRlHCL sig) intPvar intVar atm"
proof-
  let ?intSt = "trmsHCL sig"  let ?intOp = "intOpHCL sig"
  let ?intRl = "intRlHCL sig" let ?hcl = "Horn atms atm"
  have "satHcl sig ?intSt ?intOp (op =) ?intRl ?hcl"
  using sat_HCL[OF nf hcls] .
  thus ?thesis using ipv iv ha
  unfolding satHcl_def Signature.satHcl_def satAtm_def holdsAll
  unfolding compatPvar_def compatVar_def mem_def by auto
qed

lemma [expl_frule]:
assumes
NM:
"NonFreeMetaTheory (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig) &&&
 reflected_hcl n (Horn atms atm)" and
hcls: "in_hcls (Horn atms atm) (hcls_pr sig)"
and c: "collectVarsHcl (Horn atms atm) sig (pvs, vs)"
and matches:
"(ALL intPvar : compatPvar sig. ALL intVar : compatVar (trmsHCL sig).
   holdsAll (satAtm sig (trmsHCL sig) (intOpHCL sig) (op =)
             (intRlHCL sig) intPvar intVar) atms
   \<longrightarrow>
 satAtm sig (trmsHCL sig) (intOpHCL sig) (op =) (intRlHCL sig) intPvar intVar atm)
 matches P"
and unroll:
"\<lbrakk>images_nonempty (trmsHCL sig);  images_nonempty (params_pr sig);
  reg_vareval_rews () ;  reg_implication_curry_rews ()\<rbrakk> \<Longrightarrow>
 unroll_pv_quant sig (pvs, vs) P P2"
and curry: "(curry_iso None reify_iso):  P2 : UNIV_s  isomapto  P3 : UNIV_s via id"
and P4:
"\<lbrakk>reg_setoid_prop_rew ()  ;  reg_atomize_rews ()\<rbrakk> \<Longrightarrow>  (Trueprop P3) simpto PROP P4"
shows "note (PROP P4) named n"
unfolding note_const_def
proof-
  have nf: "NonFreeMetaTheory sig" and rf: "reflected_hcl n (Horn atms atm)"
  using NM unfolding atomize_conj by simp+
  have P unfolding matches[unfolded matches_const_def atomize_eq, THEN sym]
  using holdsAtm[OF nf hcls] by blast
  moreover have "P = P2" using unroll
  unfolding unroll_pv_quant_def reg_vareval_rews_def
  reg_implication_curry_rews_def
  using NonFreeMetaTheory_images_nonempty_params_pr[OF nf]
        NonFreeMetaTheory_images_nonempty_trmsHCL[OF nf] by auto
  moreover have "P2 = P3" using curry by (rule isomapto_via_idD)
  moreover have "Trueprop P3 \<equiv> PROP P4"
  using P4 unfolding reg_setoid_prop_rew_def reg_atomize_rews_def simpto_const_def by simp
  ultimately show "PROP P4" by auto
qed

lemma piquant_insert_rew: "(ALL P : (PI s1 : (insert s SS). A(s1)). Q(P))
       = (ALL Ps : A(s). ALL P2 : (PI s1 : SS. A(s1)). Q(% s2. if s = s2 then Ps else P2 s2))"
  proof
    assume H:"ALL P:Pi (insert s SS) A. Q P"
    show "ALL Ps:A s. ALL P2:Pi SS A. Q (%s2. if s = s2 then Ps else P2 s2)"
    proof rule+
      fix Ps P2
      assume Psty: "Ps : A s" and P2ty: "P2 : Pi SS A"
      have B: "(%s2. if s = s2 then Ps else P2 s2) : Pi (insert s SS) A"
       apply (rule Pi_I) apply (case_tac "x = s") apply simp apply (rule Psty)
       apply simp by (rule Pi_mem[OF P2ty])
      from H have H': "!! P. P : Pi (insert s SS) A  ==> Q P" by auto
      show "Q (%s2. if s = s2 then Ps else P2 s2)"
        by (auto intro: H'[OF B])
    qed
  next
    assume H: "ALL Ps:A s. ALL P2:Pi SS A. Q (%s2. if s = s2 then Ps else P2 s2)"
    show "ALL P:Pi (insert s SS) A. Q P"
    proof
      fix P
      assume Pty: "P:Pi (insert s SS) A"
      hence Psty: "P s : A s" by auto
      have Pty2: "P : Pi SS A" apply (rule Pi_I) by (auto intro: Pi_mem[OF Pty])
      from H have H': "!! Ps P2. Ps : A s ==> P2 : Pi SS A ==> Q (%s2. if s = s2 then Ps else P2 s2)" by auto
      have rew: "(%s2. if s = s2 then P s else P s2) = P" by (rule ext, simp)
      show "Q P"
       by (rule H'[OF Psty Pty2, simplified rew])
    qed
  qed



definition
  reg_unroll_indpred_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_unroll_indpred_rews x == True"

lemma [impl_frule]:
  "reg_unroll_indpred_rews () &&& enum_datatype_univ_rew t1 t2
   ==> brule( t1 rewto t2 ) "
    apply (drule conjunctionD2)
    by (simp add: enum_datatype_univ_rew_def brule_const_def rewto_const_def)

(* lemma [impl_frule]:
  "reg_unroll_indpred_rews () &&& enum_datatype_constreq_rew n t1 t2
   ==> brule( t1 rewto t2 ) " *)

lemma [impl_frule]:
  "reg_unroll_indpred_rews ()
   ==>
     brule(
       (ALL f : (PI s1 : (insert s SS). carOf (AA s1)). P(f))  rewto
         (SALL fs : AA(s). ALL f2 : (PI s1 : SS. carOf (AA s1)). P(% s2. if s = s2 then fs else f2 s2)) ) &&&
     brule(  (ALL f : (PI s1 : {}. A(s1)). P')  rewto  P'  )  &&&
     brule(  (if True then e1 else e2)  rewto  e1  )  &&&
     brule(  (if False then e1 else e2)  rewto  e2  )  &&&
     reg_implication_curry_rews () "
      apply (simp add: rewto_const_def brule_const_def piquant_insert_rew
        reg_implication_curry_rews_def setoid_all_def)
      by (triv, simp)+ simp




definition
  induction_rule :: "prop => prop" where
  [MRjud 1 0]: "induction_rule P == P"

definition induction_rule_name where
  "induction_rule_name = (0::nat)"


definition
  deriv_unrollrew where
  [MRjud 1 1]: "deriv_unrollrew TYPE('a) P2 == (ALL (P :: 'a => bool). (ALL x::'a. P(x)) = P2 P)"

lemma [MR]: "[|
    !! (P::'a => bool). enum_datatype_quant_unrollrew (ALL x :: 'a. P(x)) (P2(P)) |] ==>
  deriv_unrollrew TYPE('a) P2 "
  unfolding deriv_unrollrew_def enum_datatype_quant_unrollrew_def by simp

lemma induct_HCL:
assumes nf: "NonFreeMetaTheory sig" and
H: "H \<in> trmsHCL sig s"
and IH:
"\<forall>\<sigma>.
  \<forall>ps\<in>product (map (params_pr sig) (arOfP_pr sig \<sigma>)).
  \<forall>xs\<in>product (map (trmsHCL sig) (arOf_pr sig \<sigma>)).
    holdsAll2 \<phi> (arOf_pr sig \<sigma>) xs \<longrightarrow> \<phi> (stOf_pr sig \<sigma>) (intOpHCL sig \<sigma> ps xs)"
shows "\<phi> s H"
apply(rule HornTheory.induct_HCL
       [OF nf[unfolded NonFreeMetaTheory_def]
           H[unfolded NonFreeMetaTheory_def trmsHCL_def mem_def]])
using IH unfolding in_product_list_all2 Ball_def holdsAll2
unfolding trmsHCL_def intOpHCL_def by auto

lemma [expl_frule]:
assumes nf: "NonFreeMetaTheory (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig)"
and enum:
"enum_datatype_quant_unrollrew
  (ALL s. ALL P : (PI s2 : (UNIV :: 'sort set).
                  carOf (sset (trmsHCL sig s2) ~s~> (UNIV_s :: bool setoid))).
   SALL x : sset (trmsHCL sig s).
   (ALL sigma. ALL ps : product (map (params_pr sig) (arOfP_pr sig sigma)).
    ALL xs : product (map (trmsHCL sig) (arOf_pr sig sigma)).
        holdsAll2 P (arOf_pr sig sigma) xs -->
        P (stOf_pr sig sigma) (intOpHCL sig sigma ps xs))
        --> P s x)
       Q2"
and deriv: "deriv_unrollrew TYPE('opsym) unrollctxt"
and simpto:
"[| !! Q. (ALL sigma::'opsym. Q(sigma)) rewto unrollctxt(Q)  ;
          reg_unroll_indpred_rews () ;  reg_prod_unfold_rews () |] ==>
          Q2 simpto Q3"
and curry:
"(curry_iso None reify_iso):  Q3 : UNIV_s  isomapto  Q4 : UNIV_s via id"
and reg:
"[|reg_setoid_prop_rew ();  reg_atomize_rews ()  |]  ==>  (Trueprop Q4) simpto (PROP Q5)"
and scop:
"scopify_name induction_rule_name induction_rule_name'"
shows
"PROP induction_rule Q5  &&&
 note (PROP Q5) named induction_rule_name'"
proof-
  have Q2
  unfolding enum[unfolded enum_datatype_quant_unrollrew_def[unfolded atomize_eq], symmetric]
  using induct_HCL[OF nf] unfolding SALL_on_sset by auto
  moreover have "Q2 = Q3" using simpto deriv
  unfolding simpto_const_def rewto_const_def
  reg_unroll_indpred_rews_def reg_prod_unfold_rews_def atomize_eq
  deriv_unrollrew_def by auto
  moreover have "Q3 = Q4" using curry by (rule isomapto_via_idD)
  moreover have "Trueprop Q4 \<equiv> PROP Q5"
  using reg unfolding reg_setoid_prop_rew_def reg_atomize_rews_def simpto_const_def by simp
  ultimately
  show "PROP induction_rule Q5" and "note (PROP Q5) named induction_rule_name'"
  unfolding induction_rule_def note_const_def by auto
qed




(* Algebra Konstruktion *)
(*
  * Interpretationsuniversum als Summentyp konstruieren,
  * intSt als entsprechende Bilder unter Einbettungen in die Summe definieren
  * Interpretationen der Konstanten, Relationen ins Interpretationuniversum liften,
    dabei uncurrien und als intOp, intRl definieren
  * Kompatibilitaet (dh Soft-Typisierung) der entstandenen Konstanten, Relationen damit dischargen
    (Eigenschaft des Liftings)
  * satHCL hcl in dieser Interpretation normalisieren und mit proven_hcl des Benutzers abgleichen,
    dischargen
  * fuer jede Sorte s  iterHCL sig intSt intOp intRl s  im Interpretationsuniversum (von Termmodell, Algebra)
    softtypen und liften zu Benutzertypen
  * postprocessing von
      ALL sigma. ALL ps : product (map (params_pr sig) (arOfP_pr sig sigma)).  ALL ts : product (map (trmsHCL sig) (arOf_pr sig sigma)).
        iterHCL sig intSt intOp intRl (stOf_pr sig sigma) (intOpHCL sig sigma ps ts) =
          intOp sigma ps (map2 (iterHCL sig intSt intOp intRl) (arOf_pr sig sigma) ts)
    ueber Ausrollen des sigma-Quantors, product,map-Entfaltung und isotrans
*)

definition
  decl_alg_interpr :: "type => 'a itself => bool" ("_ alginterpr _" 20) where
  [MRjud 1 1]: "decl_alg_interpr T tau == True"
lemma decl_alg_interprI[intro]: "decl_alg_interpr T tau" by (simp add: decl_alg_interpr_def)
lemma decl_alg_interpr_easyI: "T == T ==> tau == tau ==> decl_alg_interpr T tau"
  by (simp add: decl_alg_interpr_def)

definition
  doing_alg_interpr :: "unit => bool" where
  [MRjud 1 0]: "doing_alg_interpr x == True"

definition
  decl_oper_alg_interpr :: "oper => 'a => bool" ("_ operalginterpr _" 20) where
  [MRjud 1 1]: "decl_oper_alg_interpr c t == True"
lemma decl_oper_alg_interprI[intro]: "decl_oper_alg_interpr c t"
  by (simp add: decl_oper_alg_interpr_def)
lemma decl_oper_alg_interpr_easyI: "c == c ==> t == t ==> decl_oper_alg_interpr c t"
  by (simp add: decl_oper_alg_interpr_def)

definition
  decl_rel_alg_interpr :: "rel => 'a => bool" ("_ relalginterpr _" 20) where
  [MRjud 1 1]: "decl_rel_alg_interpr R t == True"
lemma decl_rel_alg_interprI[intro]: "decl_rel_alg_interpr R t"
  by (simp add: decl_rel_alg_interpr_def)
lemma decl_rel_alg_interpr_easyI: "R == R ==> t == t ==> decl_rel_alg_interpr R t"
  by (simp add: decl_rel_alg_interpr_def)

definition
  alg_sum :: "unit => 'a itself => bool" where
  [MRjud 1 1]: "alg_sum x tau == True"
definition
  alg_sum_In :: "'sort => ('a => 'b) => bool" where
  [MRjud 1 1]: "alg_sum_In s i == inj i"

definition
  sort_to_alg_interpr :: "'sort => 'a itself => bool" where
  [MRjud 1 1]: "sort_to_alg_interpr s tau == True"

(* wird vom Benutzer als Fakt dann angegeben und
   angestossene forward-Rules pruefen ob richtige
   Dinge bewiesen wurden indem man
      proven_hcl interpr_hcl
   als MetaRec-Premisse hat, wobei interpr_hcl die
   Semantik von hcl ist *)
definition
  proven_hcl :: "bool => bool" where
  [MRjud 1 0]: "proven_hcl P == P"
lemma proven_hclI[intro]: "P ==> proven_hcl P"
  by (simp add: proven_hcl_def)

definition
  there_are_proven_hcls :: "unit => bool" where
  [MRjud 1 0]: "there_are_proven_hcls x == True"
lemma there_are_proven_hclsI[intro]: "there_are_proven_hcls ()" by (simp add: there_are_proven_hcls_def)


lemma [expl_frule]: "
  proven_hcl some_hcl
  ==> there_are_proven_hcls ()  " ..


lemma [expl_frule]: "[|
  decl_alg_interpr T TYPE('tau)  ;  T haskind IntType  ;  type_to_sort T s  |]
  ==>  sort_to_alg_interpr s TYPE('tau)   " by (simp add: sort_to_alg_interpr_def)

lemma [expl_frule]: "
  decl_alg_interpr T TYPE('tau)
  ==> doing_alg_interpr ()"
  by (simp add: doing_alg_interpr_def)


definition
  partial_alg_sum :: "'sort list => 'b itself => bool" where
  [MRjud 1 1]: "partial_alg_sum sorts tau == True"
lemma partial_alg_sumI[intro]: "partial_alg_sum sorts i" by (simp add: partial_alg_sum_def)

definition
  partial_alg_sum_In :: "'sort list => 'sort => ('a => 'b) => bool" where
  [MRjud 2 1]: "partial_alg_sum_In sorts s i == (inj i)"



lemma partial_alg_sum_In_step[MR]: "[|  partial_alg_sum_In ss s2 (i :: 'tau2 => 'tau_sum)  ;
    sort_to_alg_interpr s TYPE('tau)  |] ==>
  partial_alg_sum_In (Cons s ss) s2 ((Inr o i) :: 'tau2 => 'tau + 'tau_sum)  "
  unfolding partial_alg_sum_In_def apply (rule inj_comp) by simp+

lemma partial_alg_sum_In_base[MR]: "[|  partial_alg_sum ss TYPE('tau_sum)  ;  sort_to_alg_interpr s TYPE('tau)  |] ==>
  partial_alg_sum_In (Cons s ss) s (Inl :: 'tau => 'tau + 'tau_sum)  "
  by (simp add: partial_alg_sum_In_def)



lemma partial_alg_sum_base[MR]: "
  partial_alg_sum [] TYPE(unit)  " by triv+

lemma partial_alg_sum_step[MR]: "[| partial_alg_sum ss TYPE('tau_sum)  ;  sort_to_alg_interpr s TYPE('tau)  |] ==>
  partial_alg_sum (Cons s ss) TYPE('tau + 'tau_sum)  " by triv+



lemma [MR]: "PROP proj_sort_to_name_and_type_s (Trueprop (sort_to_name_and_type s n T)) s" by (rule proj_sort_to_name_and_type_sI)

lemma [expl_frule]: "[|
  doing_alg_interpr ()  &&&  PROP coll_sort_to_name_and_type () L  &&&  sort_datatype TYPE('sort) ;
    proj_proplist proj_sort_to_name_and_type_s L (sorts :: 'sort list)  |]
  ==>
    brule(  partial_alg_sum_In sorts s i  ==>
      alg_sum_In s i )  &&&

    brule(  partial_alg_sum sorts TYPE('tau) ==>
      alg_sum () TYPE('tau)  )  "
  unfolding brule_const_def alg_sum_def alg_sum_In_def partial_alg_sum_In_def
  apply (rule conjunctionI)
  apply assumption
  by (rule TrueI)



definition
  intSt_is :: "('sort => 'a) => bool" where
  [MRjud 1 0]: "intSt_is intSt == True"
lemma intSt_isI[intro]: "intSt_is intSt" by (simp add: intSt_is_def)

definition constr_intSt :: "'sort => 'a => bool" where
  [MRjud 1 1]: "constr_intSt s v == True"
lemma constr_intStI[intro]: "constr_intSt s v" by (simp add: constr_intSt_def)

definition intSt_name where
  "intSt_name = (0 :: nat)"


lemma [MR]: " alg_sum_In s i ==>
  constr_intSt s (range i)  " ..


(* TODO(feature): wenn decl_alg_interpr fehlen lieber ordentlichen Fehler geben *)
lemma [expl_frule]: "[|
  doing_alg_interpr ()  &&&  PROP coll_sort_to_name_and_type () L &&& sort_datatype TYPE('sort)  ;
    alg_sum () TYPE('algsum)  ;
    proj_proplist proj_sort_to_name_and_type_s L (sorts :: 'sort list)  ;
    metamap constr_intSt sorts (intStvals :: 'algsum set list) ;
    scopify_name intSt_name intSt_name'  ;
    enumfun intSt_name' on TYPE('sort) withvals intStvals gives intSt |]
  ==>
    intSt_is intSt  " ..



definition inhab_intSt where
  [MRjud 1 0]: "inhab_intSt S == (EX x. x : S)"


lemma [expl_frule]: "[|
  sort_to_name_and_type s ndummy Tdummy  &&&  intSt_is intSt  ;
    alg_sum_In s (i :: 'tau => 'a)  ;
    enumfun_rewr (intSt s) name_dummy (range i)  |]
  ==>
    reify_iso:  (sset (intSt s)) isoto (UNIV_s :: 'tau setoid) via (the_inv i)  &&&
    inhab_intSt (intSt s)  "
  unfolding alg_sum_In_def enumfun_rewr_def inhab_intSt_def
  apply simp
  apply (rule conjunctionI)
  unfolding isotovia_const_def
  apply (metis bij_betw_def bij_to_equi inj_on_the_inv_into the_inv_into_onto)
  by (metis rangeI)



definition
  backlifted_oper_alg_interpr where
  [MRjud 1 5]: "backlifted_oper_alg_interpr c t' AA f t AA' ==
     (curry_iso None reify_iso):  t' : AA  isomapto  t : AA'  via f  "

definition coll_backlifted_oper_alg_interpr :: "unit => proplist => prop" where
  [MRcolljud "NonFree.backlifted_oper_alg_interpr_jud" trigger: "NonFree.doing_alg_interpr_jud"]:
  "coll_backlifted_oper_alg_interpr x L == Trueprop True"


definition
  intOp_softtyping :: "bool => bool" where
  [MRjud 1 0]: "intOp_softtyping P == P"
definition
  coll_intOp_softtyping :: "unit => proplist => prop" where
  [MRcolljud "NonFree.intOp_softtyping_jud" trigger: "NonFree.doing_alg_interpr_jud"]:
    "coll_intOp_softtyping x L == Trueprop True"
definition
  intOp_compat where
  [MRjud 3 0]: "intOp_compat sig intSt intOp ==
    Signature.compat (stOf_pr sig) (arOfP_pr sig) (arOf_pr sig)
      (params_pr sig) intSt intOp"


definition
  intOp_is :: "('opsym => 'paramuni list => 'alguni list => 'alguni) => bool" where
  [MRjud 1 0]: "intOp_is intOp == True"
lemma intOp_isI[intro]: "intOp_is intOp" by (simp add: intOp_is_def)
definition
  intRl_is :: "('opsym => 'paramuni list => 'alguni list => bool) => bool" where
  [MRjud 1 0]: "intRl_is intRl == True"
lemma intRl_isI[intro]: "intRl_is intRl" by (simp add: intRl_is_def)

definition
  proj_backlifted_oper_alg_interpr_t' :: "prop => ('paramuni list => 'alguni list => 'alguni) => prop" where
  [MRjud 1 1]: "proj_backlifted_oper_alg_interpr_t' P t' == Trueprop True"


lemma [expl_frule]: "[|
  decl_oper_alg_interpr c (t :: 'tau)  &&&  intSt_is intSt  &&&  NonFreeMetaTheory sig  ;
    oper_to_opsym c sigma  ;
    uar_of_sym sigma uar  ;
    reg_prod_unfold_rews () ==>
      (sset (product (map (params_pr sig) (arOfP_pr sig sigma))) ~s~> sset(product (map intSt (arOf_pr sig sigma)))
          ~s~> sset (intSt (stOf_pr sig sigma)))
        simpto AA  ;
    (curry_iso (Some uar) reify_iso):  AA  isoto  AA' via f  ;
    reg_UNIV_s_rew () ==>
      AA' simpto (UNIV_s :: 'tau setoid)  |]
  ==>  backlifted_oper_alg_interpr c (s_inv AA AA' f t) AA f t AA' "
unfolding backlifted_oper_alg_interpr_def isomapto_via_def isotovia_const_def
          simpto_const_def reg_UNIV_s_rew_def
apply (intro conjI)
  apply (metis elem_UNIV_sI s_inv_carOf)
  apply (metis elem_UNIV_sI)
  apply (metis iso_sDsetoid(1))
  apply (metis UNIV_setoid)
  apply assumption
  by (metis elem_UNIV_sI s_inv_eqOf)

lemma [MR]: "PROP proj_backlifted_oper_alg_interpr_t' (Trueprop (backlifted_oper_alg_interpr c t' A f t A')) t'"
  by (simp add: proj_backlifted_oper_alg_interpr_t'_def)

definition
  "intOp_name = (0::nat)"

(* TODO(feature): wenn decl_oper_alg_interpr fehlen ordentlichen Fehler geben *)
lemma [expl_frule]: "[|
  doing_alg_interpr ()  &&&  PROP coll_backlifted_oper_alg_interpr () L  &&&  opsym_datatype TYPE('opsym) ;
    param_sum () TYPE('paramuni)  ;  alg_sum () TYPE('alguni) ;
    proj_proplist proj_backlifted_oper_alg_interpr_t' L (t's :: ('paramuni list => 'alguni list => 'alguni) list)  ;
    scopify_name intOp_name intOp_name'  ;
    enumfun intOp_name' on TYPE('opsym) withvals t's gives intOp |]
  ==> intOp_is intOp  " ..

lemma [expl_frule]: "[|
  intOp_is intOp  &&&  intSt_is intSt  &&&  NonFreeMetaTheory sig  &&&  oper_to_opsym c sigma  ;
    uar_of_sym sigma uar  ;
    enumfun_rewr (intOp sigma) n t'  ;
    backlifted_oper_alg_interpr c t' AA f t AA'  ;
    (sset (product (map (params_pr sig) (arOfP_pr sig sigma))) ~s~> sset (product (map intSt (arOf_pr sig sigma)))
       ~s~> sset (intSt (stOf_pr sig sigma)))
      matches AA0  ;
    reg_prod_unfold_rews () ==>
      AA0 simpto AA  |]
  ==>
      invariant (intOp sigma, intOp sigma) AA  &&&
      (curry_iso None reify_iso):  (intOp sigma) : AA  isomapto  t : AA'  via f  &&&
      userar_decl (intOp sigma) uar  &&&
      intOp_softtyping (intOp sigma : carOf AA0) "
  unfolding intOp_softtyping_def backlifted_oper_alg_interpr_def enumfun_rewr_def simpto_const_def reg_prod_unfold_rews_def
  apply (rule conjunctionI)
  unfolding invariant_def fst_conv snd_conv atomize_conj
    apply(intro conjI)
      apply (metis isomapto_carOf1)
      apply (metis isomapto_carOf1)
      apply (metis iso_sDsetoid(1) isomapto_carOf1 isomapto_iso_s srefl)
    apply(intro conjI)
      apply metis
      unfolding userar_decl_def apply metis
      by (metis isomapto_carOf1)


lemma [expl_frule]:
assumes nf:
"NonFreeMetaTheory sig  &&&  intSt_is intSt  &&&  intOp_is intOp &&&
 PROP coll_intOp_softtyping () L"
and enum:
"enum_datatype_quant_unrollrew
 (ALL sigma. intOp_softtyping (
    intOp sigma : carOf (sset (product (map (params_pr sig) (arOfP_pr sig sigma)))
            ~s~> sset (product (map intSt (arOf_pr sig sigma))) ~s~> sset (intSt (stOf_pr sig sigma)))))
       Q"
and lookup: "lookup_conjs intOp_softtyping  Q"
shows "intOp_compat sig intSt intOp"
proof-
  have Q: Q using lookup unfolding lookup_conjs_const_def .
  thus ?thesis unfolding intOp_compat_def Signature.compat_def using Q unfolding
  enum[unfolded enum_datatype_quant_unrollrew_def product_list_all2
                intOp_softtyping_def, THEN sym]
  by (metis (no_types) carOf_fun_setoid carOf_sset mem_def sfun_ty)
qed


definition
  backlifted_rel_alg_interpr where
  [MRjud 1 5]: "backlifted_rel_alg_interpr R t' AA f t AA' ==
     (curry_iso None reify_iso):  t' : AA  isomapto  t : AA'  via f  "

definition coll_backlifted_rel_alg_interpr :: "unit => proplist => prop" where
  [MRcolljud "NonFree.backlifted_rel_alg_interpr_jud" trigger: "NonFree.doing_alg_interpr_jud"]:
  "coll_backlifted_rel_alg_interpr x L == Trueprop True"

definition
  proj_backlifted_rel_alg_interpr_t' :: "prop => ('paramuni list => 'alguni list => bool) => prop" where
  [MRjud 1 1]: "proj_backlifted_rel_alg_interpr_t' P t' == Trueprop True"


lemma [expl_frule]: "[|
  decl_rel_alg_interpr R (t :: 'tau)  &&&  intSt_is intSt  &&&  NonFreeMetaTheory sig;
    rel_to_relsym R relsym  ;
    uar_of_sym relsym uar  ;
    reg_prod_unfold_rews () ==>
      (sset (product (map (params_pr sig) (rarOfP_pr sig relsym))) ~s~> sset (product (map intSt (rarOf_pr sig relsym)))
          ~s~> (UNIV_s :: bool setoid))
        simpto AA  ;
    (curry_iso (Some uar) reify_iso):  AA  isoto  AA'  via f  ;
    reg_UNIV_s_rew () ==>  AA' simpto (UNIV_s :: 'tau setoid)  |]
  ==>  backlifted_rel_alg_interpr R (s_inv AA AA' f t) AA f t AA' "
  unfolding backlifted_rel_alg_interpr_def isomapto_via_def isotovia_const_def simpto_const_def reg_UNIV_s_rew_def
apply (intro conjI)
  apply (metis elem_UNIV_sI s_inv_carOf)
  apply (metis UNIV_I carOf_UNIV_s)
  apply (metis iso_sDsetoid(1))
  apply (metis UNIV_setoid)
  apply assumption
  by (metis elem_UNIV_sI s_inv_eqOf)


lemma [MR]: "PROP proj_backlifted_rel_alg_interpr_t' (Trueprop (backlifted_rel_alg_interpr c t' AA f t AA')) t'"
  by (simp add: proj_backlifted_rel_alg_interpr_t'_def)

definition
  "intRl_name = (0::nat)"

definition
  there_are_rels :: "unit => bool" where
  [MRjud 1 0]: "there_are_rels x == True"
lemma there_are_relsI[intro]: "there_are_rels x" by (simp add: there_are_rels_def)

lemma [expl_frule]: "[|
  doing_alg_interpr ()  &&&  PROP coll_backlifted_rel_alg_interpr () L  &&&  relsym_datatype TYPE('rlsym)  ;
    param_sum () TYPE('paramuni)  ;   alg_sum () TYPE('alguni)  ;
    proplist_len L n  ;   try (nonzero n)  ;
    proj_proplist proj_backlifted_rel_alg_interpr_t' L (t's :: ('paramuni list => 'alguni list => bool) list)  ;
    scopify_name intRl_name intRl_name'  ;
    enumfun intRl_name' on TYPE('rlsym) withvals t's gives intRl  |]
  ==> intRl_is intRl &&& there_are_rels () " by triv+

(* user has declared no relations, so only our the dummy relation is present
   note that isotrans rules for dummy relation are not be needed, as it does not occur in HCLs *)
lemma [expl_frule]: "[|
  doing_alg_interpr ()  &&&  PROP coll_backlifted_rel_alg_interpr () L  &&&  relsym_datatype TYPE('rlsym)  ;
    param_sum () TYPE('paramuni)  ;  alg_sum () TYPE('alguni)  ;
    try( proplist_len L 0 )  ;
    scopify_name intRl_name intRl_name'  ;
    enumfun intRl_name' on TYPE('rlsym) withvals [(% (pxs :: 'paramuni list) (xs :: 'alguni list). False)] gives intRl |]
  ==> intRl_is intRl  " ..



lemma [expl_frule]: "[|
  intRl_is intRl  &&&  intSt_is intSt  &&&  rel_to_relsym R relsym  &&&  NonFreeMetaTheory sig  ;
    uar_of_sym relsym uar  ;
    enumfun_rewr (intRl relsym) n t'  ;
    backlifted_rel_alg_interpr R t' AA f t A'  ;
    (sset (product (map (params_pr sig) (rarOfP_pr sig relsym))) ~s~>
       sset (product (map intSt (rarOf_pr sig relsym))) ~s~> (UNIV_s :: bool setoid))
      matches AA0  ;
    reg_prod_unfold_rews () ==>
      AA0 simpto AA  |]
  ==>
      invariant (intRl relsym, intRl relsym) AA  &&&
      (curry_iso None reify_iso):  (intRl relsym) : AA  isomapto  t : A'  via f  &&&
      userar_decl (intRl relsym) uar  "
unfolding backlifted_rel_alg_interpr_def enumfun_rewr_def simpto_const_def
          reg_prod_unfold_rews_def atomize_conj
apply(intro conjI)
  unfolding invariant_def fst_conv snd_conv
  apply(intro conjI)
    unfolding matches_const_def atomize_eq
    apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
    apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
    apply auto[]
    unfolding isomapto_via_def apply(intro conjI)
      apply (metis elem_UNIV_sI elem_setdom_funsetoid fun_setoid set_setoid)
      apply metis
      apply (metis fun_setoid set_setoid)
      apply metis
      apply metis
      apply metis
    unfolding userar_decl_def by simp


definition
  hcls_satisfied where
  [MRjud 4 0]: "hcls_satisfied sig intSt intOp intRl ==
     (ALL hcl : set (hcls_pr sig). satHcl sig intSt intOp (op =) intRl hcl)"


(* Calculate reified HCLs that have to be proven by the user, based on information
   that has already been given.
   The ML version of the package works as follows:
     * no proven_hcl facts are declared, thus the construction runs
       only until hcls_satisfied is needed.
     * sig_is, intSt_is, intOp_is, intRl_is are extracted from the pool of facts,
     * the reified hcls are calculated via metarecursion with calc_reified_hcls,
     * the user is given the (preprocessed) goal to prove the reified hcls,
     * the hcls_satisfied fact is added to the pool of facts and we run
       the construction to completion *)
(* Idee: wieder mit der satHCL Infrastruktur die mit der
    Algebra interpretierten Hornklauseln unter curry_iso transformieren
    und mit denen vom Benutzer bewiesenen Formeln abgleichen.
    So spart man sich den uncurry Isomorphismus *)
definition
  calc_reified_hcls where
  [MRjud 4 1]: "calc_reified_hcls sig intSt intOp intRl Ps ==
    (hcls_satisfied sig intSt intOp intRl = (ALL P : set Ps. P))  "

lemma reified_hcls_to_hcls_satisfied:
  "calc_reified_hcls sig intSt intOp intRl Ps ==> (ALL P : set Ps. P) ==> hcls_satisfied sig intSt intOp intRl"
  by (simp add: calc_reified_hcls_def)

definition
  reify_hcl where
  [MRjud 5 1]: "reify_hcl sig intSt intOp intRl hcl P ==
    (NonFreeMetaTheory sig --> images_nonempty intSt --> satHcl sig intSt intOp (op =) intRl hcl = P)"


lemma [MR]:
assumes collect: "collectVarsHcl (Horn atms atm) sig (pvs, vs)"
and matches:
"(ALL intPvar : compatPvar sig. ALL intVar : compatVar intSt.
     holdsAll (satAtm sig intSt intOp (op =) intRl intPvar intVar) atms
     --> satAtm sig intSt intOp (op =) intRl intPvar intVar atm)
 matches P"
and unroll:
"[|images_nonempty intSt  ;  images_nonempty (params_pr sig)  ;
   reg_vareval_rews ()  ;  reg_implication_curry_rews ()  |] ==>
  unroll_pv_quant sig (pvs, vs) P P2"
and curry:
"(curry_iso None reify_iso):  P2 : UNIV_s  isomapto  P3 : UNIV_s  via id"
and simpto: "reg_setoid_prop_rew ()  ==> P3 simpto P4"
shows "reify_hcl sig intSt intOp intRl (Horn atms atm) P4 "
unfolding reify_hcl_def proof(intro impI)
  assume nf: "NonFreeMetaTheory sig" and ine: "images_nonempty intSt"
  have "(satHcl sig intSt intOp op = intRl (Horn atms atm)) = P"
  using matches unfolding matches_const_def
  unfolding holdsAll satHcl_def Signature.satHcl_def satAtm_def
  unfolding compatPvar_def compatVar_def Ball_def mem_def by auto
  moreover have "P = P2" using unroll
  unfolding unroll_pv_quant_def reg_vareval_rews_def
  reg_implication_curry_rews_def
  using NonFreeMetaTheory_images_nonempty_params_pr[OF nf] ine by auto
  moreover have "P2 = P3" using curry by (rule isomapto_via_idD)
  moreover have "P3 = P4"
  using simpto unfolding simpto_const_def reg_setoid_prop_rew_def by auto
  ultimately show "(satHcl sig intSt intOp op = intRl (Horn atms atm)) = P4" by auto
qed

lemma list_all2_pred_list_all:
assumes "list_all2 (\<lambda> x. op = (\<phi> x)) xs Ps" (is "list_all2 ?chi xs Ps")
shows "list_all \<phi> xs \<longleftrightarrow> list_all id Ps"
proof-
  have l: "length xs = length Ps" using assms by (metis list_all2_lengthD)
  show ?thesis unfolding list_all_length id_def apply safe
  by (smt assms list_all2_conv_all_nth)+
qed

lemma list_all2_pred:
assumes "list_all2 (\<lambda> x. op = (\<phi> x)) xs Ps"
shows "(\<forall> x \<in> set xs. \<phi> x) \<longleftrightarrow> (\<forall> P \<in> set Ps. P)"
using list_all2_pred_list_all[OF assms] unfolding list_all_iff id_def .

lemma [MR]:
assumes nf: "NonFreeMetaTheory sig"
and as: "alg_sum () TYPE('alguni)"
and simpto: "hcls_pr sig simpto hcls"
and enum: "enum_datatype_quant_unrollrew (ALL s. inhab_intSt (intSt s)) Q"
and lookup: "lookup_conjs (inhab_intSt :: 'alguni set => bool) Q"
and mm: "metamap (reify_hcl sig intSt intOp intRl) hcls Ps"
shows "calc_reified_hcls sig intSt intOp intRl Ps"
proof-
  have hcls: "hcls_pr sig = hcls" using simpto unfolding simpto_const_def by simp
  have "\<forall>s. inhab_intSt (intSt s)" using enum unfolding enum_datatype_quant_unrollrew_def
  using lookup unfolding lookup_conjs_const_def by simp
  hence im: "images_nonempty intSt" unfolding inhab_intSt_def images_nonempty_def mem_def .
  have "metamap
        (\<lambda>hcl P. satHcl sig intSt intOp op = intRl hcl = P)
        hcls Ps"
  using mm im nf unfolding reify_hcl_def_raw by auto
  thus ?thesis
  unfolding calc_reified_hcls_def hcls_satisfied_def hcls metamap
  by(rule list_all2_pred)
qed




definition
  reg_ball_unroll_rews :: "unit => bool" where
  [MRjud 1 0]: "reg_ball_unroll_rews x == True"

lemma [impl_frule]: "
  reg_ball_unroll_rews ()
  ==>
     brule(  (ALL x : set (Cons a as). P x) rewto (P a & (ALL x : set as. P x))  )  &&&
     brule(  (ALL x : set []. P x) rewto True  )  "
  unfolding brule_const_def rewto_const_def
  apply (rule conjunctionI)
  by simp+

lemma ball_unroll_simps:
  "(ALL x : set (Cons a as). P x) == P a & (ALL x : set as. P x)"
  "ALL x : set []. P x == True"
  by simp+



(* only executed if there is a proven_hcl fact, indicating that
   this is a manual invocation which does not directly give hcls_satisfied *)
lemma [expl_frule]:
assumes nf:
"NonFreeMetaTheory (sig :: ('sort,'opsym,'rlsym,'psort,'paramuni) sig)
      &&&  intSt_is intSt  &&&  intOp_is intOp  &&&  intRl_is intRl
      &&&  there_are_proven_hcls ()"
and calc: "calc_reified_hcls sig intSt intOp intRl Ps"
and simpto: "reg_ball_unroll_rews () ==> (ALL P : set Ps. proven_hcl P)  simpto Q"
and lookup: "lookup_conjs proven_hcl Q"
shows "hcls_satisfied sig intSt intOp intRl"
proof-
  have Q: "Q" using lookup unfolding lookup_conjs_const_def .
  hence "\<forall>P\<in>set Ps. P"
  using simpto unfolding simpto_const_def reg_ball_unroll_rews_def proven_hcl_def by auto
  thus ?thesis using calc unfolding calc_reified_hcls_def by simp
qed


definition iter_op_clauses_name where
  "iter_op_clauses_name = (0::nat)"
definition iter_rel_clauses_name where
  "iter_rel_clauses_name = (0::nat)"


thm HornTheory.iter_def

(* fake dependency on sort to get easy setoid inference *)
definition
  "iterHCL sig == (% intOp s. HornTheory.iter intOp)"

definition
  "iterHCL_reified_name = (0::nat)"

(* HACK: we use auxilliary facts of this form to get around the spurious
   cyclic dependency via the isomorphic transfer needed for hcls_satisfied,
   while also waiting for these clauses when transforming properties
   using the iterator under the curry isomorphism later on.
   Proper solution needs higher-order dependency analysis with
   markers in the isomorphis transfer signifying the phases
    paramisoto, curry_iso, curry_iso_with_iter   *)
definition
  iter_isomap_clause where
  [MRjud 1 4]:  "iter_isomap_clause t AA t' AA' f ==
    invariant (t, t) AA  &
    (curry_iso None reify_iso): t : AA  isomapto  t' : AA' via f "

(* unchecked to avoid the cyclic dependency via the isomorphic transfer
   needed for hcls_satisfied *)
lemma [MR_unchecked]: "
    iter_isomap_clause (iterHCL sig intOp s) AA t' AA' f  ==>
  invariant (iterHCL sig intOp s, iterHCL sig intOp s) AA "
  by (simp add: iter_isomap_clause_def)
lemma [MR_unchecked]: "
    iter_isomap_clause (iterHCL sig intOp s) AA t' AA' f  ==>
  (curry_iso None reify_iso): (iterHCL sig intOp s) : AA  isomapto  t' : AA' via f  "
  by (simp add: iter_isomap_clause_def)

definition
  coll_iter_isomap_clause :: "unit => proplist => prop" where
  [MRcolljud "NonFree.iter_isomap_clause_jud" trigger: "NonFree.hcls_satisfied_jud"]:
    "coll_iter_isomap_clause x L == Trueprop True"

definition
  decl_iter_name :: "type => 'a => bool" where
  [MRjud 1 1]: "decl_iter_name T n == True"
lemma decl_iter_nameI[intro]: "decl_iter_name T n" by (simp add: decl_iter_name_def)
lemma decl_iter_name_easyI: "T==T ==> n==n ==> decl_iter_name T n" by (simp add: decl_iter_name_def)

definition
  calc_iter_name :: "'sort => 'a => bool" where
  [MRjud 1 1]: "calc_iter_name s n == True"
lemma calc_iter_nameI[intro]: "calc_iter_name s n" by (simp add: calc_iter_name_def)

(* low prio *)
lemma [MR]: "[|
    sort_to_name_and_type s sort_name Tdummy  ;
    concat names iterHCL_reified_name sort_name = n  |] ==>
  calc_iter_name s n  " ..

(* high prio *)
lemma [MR]: "[|
   sort_to_name_and_type s sort_name T  ;
   try (decl_iter_name T n)  |] ==>
  calc_iter_name s n  " ..

lemma iter_intSt:
assumes nf: "NonFreeMetaTheory sig"
and compat: "intOp_compat sig intSt intOp"
and hcl: "hcls_satisfied sig intSt intOp intRl"
and H: "H \<in> trmsHCL sig s"
shows "iterHCL sig intOp s H \<in> intSt s"
unfolding iterHCL_def mem_def
apply(rule HornTheory.iter_intSt[OF nf[unfolded NonFreeMetaTheory_def]
                                    compat[unfolded intOp_compat_def]])
using hcl H unfolding hcls_satisfied_def satHcl_def Ball_def trmsHCL_def mem_def by auto

lemma [expl_frule]:
assumes nf:
"NonFreeMetaTheory sig  &&&  intSt_is intSt  &&&
 intOp_is intOp  &&&  intRl_is intRl &&&
 sort_to_name_and_type s sort_name Tdummy &&&
 intOp_compat sig intSt intOp &&&
 hcls_satisfied sig intSt intOp intRl"
and matches:
"(sset (trmsHCL sig s) ~s~> sset (intSt s)) matches AA"
and isoto:
"(curry_iso None reify_iso):  AA  isoto AA' via f"
and simpto: "reg_UNIV_s_rew ()  ==>  AA' simpto UNIV_s"
and calc: "calc_iter_name s n"
and defi: "define n := f (iterHCL sig intOp s) giving c"
shows "iter_isomap_clause (iterHCL sig intOp s) AA c AA' f"
unfolding iter_isomap_clause_def proof(intro conjI)
  have nf: "NonFreeMetaTheory sig"
  and compat: "intOp_compat sig intSt intOp"
  and hcl: "hcls_satisfied sig intSt intOp intRl"
  using nf unfolding atomize_conj by auto
  have AA: "AA = sset (trmsHCL sig s) ~s~> sset (intSt s)"
  using matches unfolding matches_const_def by auto
  have iter: "iterHCL sig intOp s \<in> carOf AA"
  unfolding AA using iter_intSt[OF nf compat hcl]
  by (metis carOf_sset elem_setdom_funsetoid set_setoid)
  show inv: "invariant (iterHCL sig intOp s, iterHCL sig intOp s) AA"
  unfolding invariant_def fst_conv snd_conv proof(intro conjI)
    show "eqOf AA (iterHCL sig intOp s) (iterHCL sig intOp s)"
    by (metis iter AA fun_setoid set_setoid srefl)
  qed(insert iter, auto)
  have f: "f \<in> AA ~=~> AA'" using isoto unfolding isotovia_const_def .
  have c: "c = f (iterHCL sig intOp s)"
  using defi unfolding define_const_def atomize_eq .
  show "curry_iso None reify_iso: iterHCL sig intOp s : AA isomapto c : AA' via f"
  unfolding isomapto_via_def apply(intro conjI)
    apply (rule iter)
    apply (metis f c iter iso_sDfunsp sfun_elim)
    apply (metis isoto isotoE)
    apply (metis isoto isotoE)
    apply (rule f)
    by (metis c f iso_sDsetoid(1) iso_sDwf iter srefl)
qed

(* schlecht als map formulierbar wegen res_sets Nutzung in pCons *)
fun
  pmap2 where
  "pmap2 Nil f Nil Nil = pNil"
| "pmap2 (Cons res_set res_sets) f (Cons x xs) (Cons y ys) =
     pCons res_set res_sets (f x y) (pmap2 res_sets f xs ys)"

lemma [MR]: "
  pmap2 Nil f Nil pNil  rewto  pNil"  by (simp add: rewto_const_def pNil_def)
lemma [MR]: "
  pmap2 (Cons res_set res_sets) f (Cons x xs) (pCons A As y ys)  rewto
     pCons res_set res_sets (f x y) (pmap2 res_sets f xs ys)"  by (simp add: rewto_const_def pCons_def)

lemma length_pmap2:
assumes l: "length res_sets = length xs"
and xs_ys: "length xs = length ys"
shows "pmap2 res_sets f xs ys = map2 f xs ys"
using xs_ys l apply(induct arbitrary: res_sets rule: list_induct2)
apply(simp add: pNil_def)
by (simp, smt length_Suc_conv pCons_def pmap2.simps(2))


definition
  iter_op_clauses :: "prop => prop" where
  [MRjud 1 0]: "iter_op_clauses P == PROP P"
definition
  iter_rel_clauses :: "prop => prop"  where
  [MRjud 1 0]: "iter_rel_clauses P == PROP P"


lemma map2_map:
assumes "length xs = length ys"
shows "map2 (\<lambda> x. f) xs ys = map f ys"
using assms apply(induct rule: list_induct2) by auto


lemma iterHCL_Hop:
assumes nf: "NonFreeMetaTheory sig"
and compat: "intOp_compat sig intSt intOp"
and hcl: "hcls_satisfied sig intSt intOp intRl"
and ps: "list_all2 (params_pr sig) (arOfP_pr sig \<sigma>) ps"
and ts: "list_all2 (trmsHCL sig) (arOf_pr sig \<sigma>) ts"
shows
"iterHCL sig intOp (stOf_pr sig \<sigma>) (intOpHCL sig \<sigma> ps ts) =
 intOp \<sigma> ps
    (pmap2 (map intSt (arOf_pr sig \<sigma>)) (iterHCL sig intOp)
                  (arOf_pr sig \<sigma>) ts)"
(is "_ = intOp \<sigma> ps (pmap2 ?rs ?f ?xs ?ys)")
proof-
  have l1: "length ?rs = length ?xs" by simp
  have l2: "length ?xs = length ?ys" using ts by (metis list_all2_lengthD)
  have 3: "pmap2 ?rs ?f ?xs ?ys = map2 ?f ?xs ?ys"
  using length_pmap2[OF l1 l2] .
  show ?thesis unfolding 3
  using hcl[unfolded hcls_satisfied_def]
  using HornTheory.iter_Hop[OF nf[unfolded NonFreeMetaTheory_def]
                               compat[unfolded intOp_compat_def]]
  unfolding intOp_compat_def Signature.compat_def
  unfolding iterHCL_def intOpHCL_def satHcl_def unfolding map2_map[OF l2] by blast
qed

lemma [expl_frule]:
assumes nf:
"NonFreeMetaTheory sig  &&&  intSt_is intSt  &&&  intOp_is intOp  &&&  intRl_is intRl &&&
 hcls_satisfied sig intSt intOp intRl &&&
 intOp_compat sig intSt intOp   &&&
 PROP coll_iter_isomap_clause () L"
and as: "alg_sum () TYPE('alguni)"
and enum: "enum_datatype_quant_unrollrew (ALL s. inhab_intSt (intSt s)) Q"
and lookup: "lookup_conjs (inhab_intSt :: 'alguni set => bool) Q"
and enum2:
"enum_datatype_quant_unrollrew
 (ALL sigma. ALL ps : product (map (params_pr sig) (arOfP_pr sig sigma)).
  ALL ts : product (map (trmsHCL sig) (arOf_pr sig sigma)).
     eqOf (sset (intSt (stOf_pr sig sigma)))
          (iterHCL sig intOp (stOf_pr sig sigma) (intOpHCL sig sigma ps ts))
          (intOp sigma ps (pmap2 (map intSt (arOf_pr sig sigma))  (iterHCL sig intOp)
                                 (arOf_pr sig sigma) ts)))
      P1"
and simpto: "reg_prod_unfold_rews () ==> P1 simpto P2"
and curry: "(curry_iso None reify_iso):  P2 : UNIV_s  isomapto  P3 : UNIV_s  via id"
and simpto2:
"[|reg_setoid_prop_rew ()  ;  reg_atomize_rews ()  |] ==> Trueprop(P3) simpto (PROP P4)"
and scope: "scopify_name iter_op_clauses_name iter_op_clauses_name'"
shows
"PROP (iter_op_clauses P4) &&&
 note (PROP P4) named iter_op_clauses_name'"
proof-
  have nf: "NonFreeMetaTheory sig"
  and hcl: "hcls_satisfied sig intSt intOp intRl"
  and compat: "intOp_compat sig intSt intOp"
  using nf apply - apply(erule Pure.conjunctionD1)
  apply(drule Pure.conjunctionD2, drule Pure.conjunctionD2,
        drule Pure.conjunctionD2, drule Pure.conjunctionD2)
  apply(erule Pure.conjunctionD1)
  apply(drule Pure.conjunctionD2, drule Pure.conjunctionD2,
        drule Pure.conjunctionD2, drule Pure.conjunctionD2, drule Pure.conjunctionD2)
  by (erule Pure.conjunctionD1)
  have P1 unfolding enum2[unfolded enum_datatype_quant_unrollrew_def, symmetric]
  unfolding product_list_all2 using iterHCL_Hop[OF nf compat hcl]
  unfolding Ball_def mem_def by auto
  moreover have "P1 = P2"
  using simpto unfolding reg_prod_unfold_rews_def simpto_const_def by simp
  moreover have "P2 = P3" using curry unfolding isomapto_via_def
  by (metis curry isomapto_via_idD)
  moreover have "Trueprop P3 \<equiv> PROP P4"
  using simpto2 unfolding reg_setoid_prop_rew_def reg_atomize_rews_def simpto_const_def
  by auto
  ultimately show "PROP (iter_op_clauses P4)"
  unfolding iter_op_clauses_def by auto
  thus "note PROP P4 named iter_op_clauses_name'"
  unfolding note_const_def iter_op_clauses_def .
qed

lemma iterHCL_Hrel:
assumes nf: "NonFreeMetaTheory sig"
and compat: "intOp_compat sig intSt intOp"
and hcl: "hcls_satisfied sig intSt intOp intRl"
and ps: "list_all2 (params_pr sig) (rarOfP_pr sig \<pi>) ps"
and ts: "list_all2 (trmsHCL sig) (rarOf_pr sig \<pi>) ts"
and int: "intRlHCL sig \<pi> ps ts"
shows
"intRl \<pi> ps
    (pmap2 (map intSt (rarOf_pr sig \<pi>)) (iterHCL sig intOp)
            (rarOf_pr sig \<pi>) ts)"
(is "intRl \<pi> ps (pmap2 ?rs ?f ?xs ?ys)")
proof-
  have l1: "length ?rs = length ?xs" by simp
  have l2: "length ?xs = length ?ys" using ts by (metis list_all2_lengthD)
  have 3: "pmap2 ?rs ?f ?xs ?ys = map2 ?f ?xs ?ys"
  using length_pmap2[OF l1 l2] .
  show ?thesis unfolding 3
  using hcl[unfolded hcls_satisfied_def]
  using HornTheory.iter_Hrel[OF nf[unfolded NonFreeMetaTheory_def]
                               compat[unfolded intOp_compat_def] _
                               int[unfolded intRlHCL_def]]
  unfolding iterHCL_def satHcl_def unfolding map2_map[OF l2] by blast
qed


lemma [expl_frule]:
assumes nf:
"NonFreeMetaTheory sig  &&&  intSt_is intSt  &&&  intOp_is intOp  &&&  intRl_is intRl &&&
 there_are_rels ()  &&&  hcls_satisfied sig intSt intOp intRl &&&
 intOp_compat sig intSt intOp  &&&  PROP coll_iter_isomap_clause () L"
and as: "alg_sum () TYPE('alguni)"
and enum: "enum_datatype_quant_unrollrew (ALL s. inhab_intSt (intSt s)) Q"
and lookup: "lookup_conjs (inhab_intSt :: 'alguni set => bool) Q"
and enum2:
"enum_datatype_quant_unrollrew
      (ALL rel. ALL ps : product (map (params_pr sig) (rarOfP_pr sig rel)).
        ALL ts : product (map (trmsHCL sig) (rarOf_pr sig rel)).
          intRlHCL sig rel ps ts
          --> intRl rel ps (pmap2 (map intSt (rarOf_pr sig rel))  (iterHCL sig intOp)
                                 (rarOf_pr sig rel) ts))
      P1"
and simpto:
"reg_prod_unfold_rews () ==> P1 simpto P2"
and curry: "(curry_iso None reify_iso):  P2 : UNIV_s  isomapto  P3 : UNIV_s  via id"
and simpto2:
"[|reg_setoid_prop_rew ()  ;  reg_atomize_rews ()  |] ==>
       Trueprop(P3) simpto (PROP P4)"
and scope: "scopify_name iter_rel_clauses_name iter_rel_clauses_name'"
shows
"PROP (iter_rel_clauses P4) &&&
 note (PROP P4) named iter_rel_clauses_name'"
proof-
  have nf: "NonFreeMetaTheory sig"
  and hcl: "hcls_satisfied sig intSt intOp intRl"
  and compat: "intOp_compat sig intSt intOp" using nf apply -
  apply(erule Pure.conjunctionD1)
  apply(drule Pure.conjunctionD2, drule Pure.conjunctionD2,
        drule Pure.conjunctionD2, drule Pure.conjunctionD2, drule Pure.conjunctionD2)
  apply(erule Pure.conjunctionD1)
  apply(drule Pure.conjunctionD2, drule Pure.conjunctionD2,
        drule Pure.conjunctionD2, drule Pure.conjunctionD2,
        drule Pure.conjunctionD2, drule Pure.conjunctionD2)
  by (erule Pure.conjunctionD1)
  have P1 unfolding enum2[unfolded enum_datatype_quant_unrollrew_def, symmetric]
  unfolding product_list_all2 using iterHCL_Hrel[OF nf compat hcl]
  unfolding Ball_def mem_def by auto
  moreover have "P1 = P2"
  using simpto unfolding reg_prod_unfold_rews_def simpto_const_def by simp
  moreover have "P2 = P3" using curry unfolding isomapto_via_def
  by (metis curry isomapto_via_idD)
  moreover have "Trueprop P3 \<equiv> PROP P4"
  using simpto2 unfolding reg_setoid_prop_rew_def reg_atomize_rews_def simpto_const_def
  by auto
  ultimately show "PROP (iter_rel_clauses P4)"
  unfolding iter_rel_clauses_def by auto
  thus "note PROP P4 named iter_rel_clauses_name'"
  unfolding note_const_def iter_rel_clauses_def .
qed





(*
ML {*
  MetaRec.print_depgraph (Context.Proof @{context})
*}
*)



(* for user declaration of relation interpretations *)
definition
  interpretedas_const :: "'a => 'b => bool" ("_ interpretedas _") where
  "interpretedas_const x y = True"



end
