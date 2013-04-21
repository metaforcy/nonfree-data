theory Terms_with_Bindings
imports Prelim
begin

(* type_synonym var = nat type_synonym const = nat *)

nonfreedata ('var,'const) trm =
    Var 'var | Ct 'const | App "('var,'const) trm" "('var,'const) trm" | Lam 'var "('var,'const) trm"
  | subst "('var,'const) trm" "('var,'const) trm" 'var (* subst X Y z = X[Y/z] *)
where
  subst_V1: "subst (Var x) X x = X"
| subst_Ct: "subst (Ct c) X x = Ct c"
| subst_V2: "neq x y \<Longrightarrow> subst (Var x) Y y = Var x"
| subst_App: "subst (App X Y) Z z = App (subst X Z z) (subst Y Z z)"
| subst_Lam: "\<lbrakk>neq x y ; fresh x Y\<rbrakk> \<Longrightarrow> subst (Lam x X) Y y = Lam x (subst X Y y)"
| fresh_V: "neq x y \<Longrightarrow> fresh x (Var y)"
| fresh_Ct: "fresh x (Ct c)"
| fresh_App: "\<lbrakk>fresh x Y ; fresh x Z\<rbrakk> \<Longrightarrow> fresh x (App Y Z)"
| fresh_Lam1: "fresh x (Lam x X)"
| fresh_Lam2: "fresh x Y \<Longrightarrow> fresh x (Lam y Y)"
| Lam_subst:  "\<lbrakk>neq y x ; fresh y X\<rbrakk> \<Longrightarrow> Lam y (subst X (Var y) x) = Lam x X"
| fresh_subst: "\<lbrakk>fresh x X; fresh x Z\<rbrakk> \<Longrightarrow>  fresh x (subst X Z z)"

declare subst_V1[simp] subst_V2[simp] subst_Ct[simp] subst_App[simp] subst_Lam[simp]
        fresh_V[simp] fresh_Ct[simp] fresh_App[simp] fresh_Lam1[simp] fresh_Lam2[simp]
        Lam_subst[simp] fresh_subst[simp]

(* Count number of free occurrences of a variable in a trm: *)
nonfreeiter
  numoccs :: "('var,'const) trm \<Rightarrow> ('var \<Rightarrow> nat)"
where
  "numoccs (Var x) = (\<lambda> z. if x = z then 1 else 0)"
| "numoccs (Ct c) = (\<lambda> z. 0)"
| "numoccs (App X Y)  = (\<lambda> z. numoccs X z + numoccs Y z)"
| "numoccs (Lam x X) = (\<lambda> z. if x = z then 0 else numoccs X z)"
| "numoccs (subst X Y y) = (\<lambda> z.
     if y = z then numoccs X y * numoccs Y z
     else numoccs X z + numoccs X y * numoccs Y z)"
| "(fresh :: 'var \<Rightarrow> ('var,'const) trm \<Rightarrow> bool) interpretedas (\<lambda> x (occs :: 'var \<Rightarrow> nat). occs x = 0)"
by (auto simp: algebra_simps)

datatype 'const const = Old 'const | lam | app

(* HOAS encoding of lambda trms in themselves, proved adequate at definition time! *)
nonfreeiter
  enc :: "('var,'const) trm \<Rightarrow> ('var,'const const) trm"
where
  "enc (Var x) = Var x"
| "enc (Ct c) = Ct (Old c)"
| "enc (App X Y) = App (App (Ct app) (enc X)) (enc Y)"
| "enc (Lam x X) = App (Ct lam) (Lam x (enc X))"
| "enc (subst X Y y) = subst (enc X) (enc Y) y"
| "(fresh :: 'var \<Rightarrow> ('var,'const) trm \<Rightarrow> bool) interpretedas
   (fresh :: 'var \<Rightarrow> ('var,'const const) trm \<Rightarrow> bool)"
by auto

(* Interpretation of trms in semantic domains: *)

locale Semantics =
fixes APP :: "'dom \<Rightarrow> 'dom \<Rightarrow> 'dom"
  and LAM :: "('dom \<Rightarrow> 'dom) \<Rightarrow> 'dom"
begin

nonfreeiter
  sem :: "('var,'const) trm \<Rightarrow> ('const \<Rightarrow> 'dom) \<Rightarrow> ('var \<Rightarrow> 'dom) \<Rightarrow> 'dom"
where
  "sem (Var x) = (\<lambda> \<xi> \<rho>. \<rho> x)"
| "sem (Ct c) = (\<lambda> \<xi> \<rho>. \<xi> c)"
| "sem (App X Y) = (\<lambda> \<xi> \<rho>. APP (sem X \<xi> \<rho>) (sem Y \<xi> \<rho>))"
| "sem (Lam x X) = (\<lambda> \<xi> \<rho>. LAM (\<lambda> d. sem X \<xi> (\<rho> (x := d))))"
| "sem (subst X Y y) = (\<lambda> \<xi> \<rho>. sem X \<xi> (\<rho> (y := sem Y \<xi> \<rho>)))"
| "(fresh :: 'var \<Rightarrow> ('var,'const) trm \<Rightarrow> bool) interpretedas
   (\<lambda> x (K :: ('const \<Rightarrow> 'dom) \<Rightarrow> ('var \<Rightarrow> 'dom) \<Rightarrow> 'dom).
      \<forall> \<xi> \<rho>1 \<rho>2. (\<forall> y. y \<noteq> x \<longrightarrow> \<rho>1 y = \<rho>2 y) \<longrightarrow>  K \<xi> \<rho>1 = K \<xi> \<rho>2)"
apply (auto intro!: ext
       arg_cong[of _ _ LAM] arg_cong[of _ _ AP] arg_cong2[of _ _ _ _ APP])
apply (metis fun_upd_other fun_upd_twist)
proof- (* todo: clean up proof *)
  fix x' x'a \<rho>1 \<rho>2 d assume "\<forall>y. y \<noteq> x' \<longrightarrow> \<rho>1 y = \<rho>2 y"
  hence "\<rho>1(x' := d) = \<rho>2(x' := d)" by auto
  thus "x'a (\<rho>1(x' := d)) = x'a (\<rho>2(x' := d))" by simp
qed

end (* context Semantics *)

(* Relativized depth, assuming weights for each (free) variable, is an
  instance of the semantic-domain interpretation:  *)
interpretation I : Semantics where APP = max and LAM = "\<lambda> K. Suc (K (0::nat))" done

definition wdepth :: "('var,'const) trm \<Rightarrow> ('var \<Rightarrow> nat) \<Rightarrow> nat" where
"wdepth X \<equiv> I.sem X (\<lambda> c. 0)"

lemma wdepth_simps[simp]:
  "wdepth (Var x) \<rho> = \<rho> x"
  "wdepth (Ct c) \<rho> = 0"
  "wdepth (App X Y) \<rho> = max (wdepth X \<rho>) (wdepth Y \<rho>)"
  "wdepth (Lam x X) \<rho> = Suc (wdepth X (\<rho> (x := 0)))"
  "wdepth (subst X Y y) \<rho> = wdepth X (\<rho> (y := wdepth Y \<rho>))"
  "\<lbrakk>fresh x X; \<And> y. y \<noteq> x \<Longrightarrow>  \<rho>1 y = \<rho>2 y\<rbrakk> \<Longrightarrow>  wdepth X \<rho>1 = wdepth X \<rho>2"
unfolding wdepth_def by auto

(* The usual depth operator is obtained with weigth 0 for all variables: *)
definition "depth X \<equiv> wdepth X (\<lambda> x. 0)"

lemma depth_simps[simp]:
  "depth (Var x) = 0"
  "depth (Ct c) = 0"
  "depth (App X Y) = max (depth X) (depth Y)"
  "depth (Lam x X) = Suc (depth X)"
unfolding depth_def by simp_all (metis fun_upd_triv)

lemma depth_subst_var[simp]: "depth (subst X (Var z) x) = depth X"
unfolding depth_def by simp (metis fun_upd_triv)

(* Some setup: *)
definition "isVar X \<equiv> \<exists> x. X = Var x"
definition "isCt X \<equiv> \<exists> c. X = Ct c"
definition "isApp X \<equiv> \<exists> X1 X2. X = App X1 X2"
definition "isLam X \<equiv> \<exists> x X1. X = Lam x X1"
definition "issubst X \<equiv> \<exists> X1 X2 x. X = subst X1 X2 x"

lemma nchotomy_aux: "isVar X \<or> isCt X \<or> isApp X \<or> isLam X \<or> issubst X"
apply(induction X) unfolding isVar_def isCt_def isApp_def isLam_def issubst_def by blast+

lemma cases_aux:
"\<lbrakk>isVar X \<Longrightarrow>  \<phi>; isCt X \<Longrightarrow>  \<phi>; isApp X \<Longrightarrow>  \<phi>; isLam X \<Longrightarrow>  \<phi>; issubst X \<Longrightarrow>  \<phi>\<rbrakk> \<Longrightarrow> \<phi>"
using nchotomy_aux by auto

lemma isVar_subst:
assumes "isVar X1" shows "isVar (subst X1 X2 x) \<or> subst X1 X2 x = X2"
proof-
  obtain x1 where X1: "X1 = Var x1" using assms unfolding isVar_def by auto
  show ?thesis unfolding isVar_def X1 by (cases "x = x1") auto
qed

lemma isCt_subst:
assumes "isCt X1" shows "subst X1 X2 x = X1"
using assms unfolding isCt_def by auto

lemma isApp_subst:
assumes "isApp X1" shows "isApp (subst X1 X2 x)"
using assms unfolding isApp_def by fastforce

lemma finite_nonFresh:
fixes X :: "('var,'const) trm"
assumes i: "\<not> finite (UNIV::'var set)" (* X :: "('var::infinite,'const) term" *)
shows "finite {z. \<not> fresh z X}"
proof (induction X)
  fix x::'var
  have "{z. \<not> fresh z (Var x)} \<subseteq> {x}" by (auto, case_tac "x = xa", auto)
  thus "finite {z. \<not> fresh z (Var x)}" by (metis finite.simps subset_singletonD)
next
  fix c::'const show "finite {z::'var. \<not> fresh z (Ct c)}" using i by auto
next
  fix X1 X2 :: "('var,'const) trm"
  assume "finite {z::'var. \<not> fresh z X1}" (is "finite ?A1")
     and "finite {z::'var. \<not> fresh z X2}" (is "finite ?A2")
  moreover have "{z::'var. \<not> fresh z (App X1 X2)} \<subseteq> ?A1 \<union> ?A2" (is "?B \<subseteq> _") by auto
  ultimately show "finite ?B"
  by (metis finite_UnI finite_subset)
next
  fix x :: 'var and X1 :: "('var,'const) trm"
  assume "finite {z::'var. \<not> fresh z X1}" (is "finite ?A1")
  moreover have "finite {x}" by simp
  moreover have "{z::'var. \<not> fresh z (Lam x X1)} \<subseteq> ?A1 \<union> {x}" (is "?B \<subseteq> _") by auto
  ultimately show "finite ?B" by (metis finite_UnI finite_subset)
next
  fix x :: 'var and X1 X2 :: "('var,'const) trm"
  assume "finite {z::'var. \<not> fresh z X1}" (is "finite ?A1")
     and "finite {z::'var. \<not> fresh z X2}" (is "finite ?A2")
  moreover have "{z::'var. \<not> fresh z (subst X1 X2 x)} \<subseteq> ?A1 \<union> ?A2" (is "?B \<subseteq> _") by auto
  ultimately show "finite ?B" by (metis finite_UnI finite_subset)
qed

lemma ex_fresh:
fixes T :: "('var,'const) trm set"
assumes i: "\<not> finite (UNIV::'var set)" (* X :: "('var::infinite,'const) term" *)
and f: "finite A" and F: "finite T"
shows "\<exists> z. (\<forall> X \<in> T. fresh z X) \<and> z \<notin> A"
proof-
  have "finite ((\<Union> X \<in> T. {z. \<not> fresh z X}) \<union> A)" (is "finite ?B")
  using finite_nonFresh[OF i] f F by auto
  hence "UNIV - ?B \<noteq> {}" by (metis finite.emptyI finite_Diff2 i)
  thus ?thesis by auto
qed

lemma isLam_subst:
fixes X :: "('var,'const) trm"
assumes i: "\<not> finite (UNIV::'var set)" and "isLam X"
shows "isLam (subst X X2 x)"
proof-
  obtain x1 X1 where X: "X = Lam x1 X1" using assms unfolding isLam_def by auto
  then obtain y1 where y1: "fresh y1 X1" "fresh y1 X2" "y1 \<noteq> x1" "y1 \<noteq> x"
  using ex_fresh[of "{x1,x}" "{X1,X2}", OF i] by auto
  hence 1: "Lam x1 X1 = Lam y1 (subst X1 (Var y1) x1)" using subst_Lam by auto
  show ?thesis unfolding X 1 isLam_def using y1 by (auto simp del: Lam_subst)
qed

(* A term is either a variable, or a constant, or an application, or an abstraction: *)
lemma nchotomy:
fixes X :: "('var,'const) trm"
assumes i: "\<not> finite (UNIV::'var set)"
shows "isVar X \<or> isCt X \<or> isApp X \<or> isLam X"
proof (induction X)
  fix x :: 'var and X1 X2 :: "('var,'const) trm"
  assume X1: "isVar X1 \<or> isCt X1 \<or> isApp X1 \<or> isLam X1"
  and X2: "isVar X2 \<or> isCt X2 \<or> isApp X2 \<or> isLam X2"
  let ?Y = "subst X1 X2 x"
  show "isVar ?Y \<or> isCt ?Y \<or> isApp ?Y \<or> isLam ?Y"
  using X1 proof(elim disjE)
    assume "isVar X1"
    from isVar_subst[OF this, of X2 x] X2 show ?thesis by fastforce
  qed (insert X1, auto simp: isCt_subst isApp_subst isLam_subst[OF i])
qed (auto simp: isVar_def isCt_def isApp_def isLam_def)

(* Picking fresh vars: *)
definition pickFresh :: "(var,'const) trm list \<Rightarrow> var list \<Rightarrow> var"
where "pickFresh Xs xs \<equiv> SOME x. (\<forall> X \<in> set Xs. fresh x X) \<and> x \<notin> set xs"

lemma pickFresh:
"(\<forall> X \<in> set Xs. fresh (pickFresh Xs xs) X) \<and> pickFresh Xs xs \<notin> set xs"
unfolding pickFresh_def by (rule someI_ex, rule ex_fresh) auto

lemma fresh_pickFresh[simp]: "X \<in> set Xs \<Longrightarrow>  fresh (pickFresh Xs xs) X"
using pickFresh by auto

lemma notIn_pickFresh[simp]: "pickFresh Xs xs \<notin> set xs"
using pickFresh by auto



end

