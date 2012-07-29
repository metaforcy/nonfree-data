header {* Some preliminaries on equivalence relations and quotients *}

(* author: Andrei Popescu *)

theory Equiv_Relation2 imports Preliminaries 
begin


(* Recall the following constants and lemmas: 

term Eps
term "A//r"
lemmas equiv_def
lemmas refl_on_def   
 -- note that "reflexivity on" also assumes inclusion of the relation's field into r

*)

definition proj :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set"
where "proj r x = r `` {x}"


definition univ :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set \<Rightarrow> 'b)"
where "univ f X == f (Eps X)"


lemma proj_preserves:
"x \<in> A \<Longrightarrow> proj r x \<in> A//r"
unfolding proj_def by (rule quotientI)


lemma proj_in_iff:
assumes "equiv A r"
shows "(proj r x \<in> A//r) = (x \<in> A)"
apply(rule iffI)  apply(auto simp add: proj_preserves) 
unfolding proj_def quotient_def proof auto
  fix y assume y: "y \<in> A" and "r `` {x} = r `` {y}"
  moreover have "y \<in> r `` {y}" using assms y unfolding equiv_def refl_on_def by auto
  ultimately have "(x,y) \<in> r" by auto
  thus "x \<in> A" using assms unfolding equiv_def refl_on_def by auto
qed 


lemma proj_iff: 
"\<lbrakk>equiv A r; {x,y} \<subseteq> A\<rbrakk> \<Longrightarrow> (proj r x = proj r y) = ((x,y) \<in> r)"
unfolding proj_def by (auto simp add: eq_equiv_class_iff)

lemma in_proj: "\<lbrakk>equiv A r; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> proj r x"
unfolding proj_def equiv_def refl_on_def by auto


lemma proj_image: "(proj r) ` A = A//r"
unfolding proj_def_raw quotient_def by auto


lemma in_quotient_imp_non_empty:
assumes "equiv A r" and "X \<in> A//r"
shows "X \<noteq> {}"
proof-
  obtain x where "x \<in> A \<and> X = r `` {x}" using assms unfolding quotient_def by auto
  hence "x \<in> X" using assms equiv_class_self by fastsimp
  thus ?thesis by auto
qed


lemma in_quotient_imp_in_rel: 
"\<lbrakk>equiv A r; X \<in> A//r; {x,y} \<subseteq> X\<rbrakk> \<Longrightarrow> (x,y) \<in> r"
using assms quotient_eq_iff by fastsimp


lemma in_quotient_imp_closed: 
"\<lbrakk>equiv A r; X \<in> A//r; x \<in> X; (x,y) \<in> r\<rbrakk> \<Longrightarrow> y \<in> X"
unfolding quotient_def equiv_def trans_def by auto


lemma in_quotient_imp_subset: 
"\<lbrakk>equiv A r; X \<in> A//r\<rbrakk> \<Longrightarrow> X \<subseteq> A"
using assms in_quotient_imp_in_rel equiv_type by fastsimp


lemma equiv_Eps_in: 
assumes  ECH: "equiv A r" and X: "X \<in> A//r"
shows "Eps X \<in> X"
proof(rule "someI2_ex", auto simp add: mem_def)
  have "\<exists> x. x \<in> X" using assms in_quotient_imp_non_empty by fastsimp
  thus "\<exists>x. X x" unfolding mem_def .
qed


lemma equiv_Eps_preserves:
assumes  ECH: "equiv A r" and X: "X \<in> A//r"
shows "Eps X \<in> A"
proof(rule "someI2_ex")
  have "\<exists> x. x \<in> X" using assms in_quotient_imp_non_empty by fastsimp
  thus "\<exists> x. X x" unfolding mem_def .
next
  fix x assume "X x" hence "x \<in> X" unfolding mem_def . 
  moreover have "X \<subseteq> A" using assms in_quotient_imp_subset by fastsimp
  ultimately show "x \<in> A" by auto
qed
  

lemma proj_Eps:
assumes "equiv A r" and "X \<in> A//r"
shows "proj r (Eps X) = X"
unfolding proj_def proof(auto)
  fix x assume x: "x \<in> X"
  thus "(Eps X, x) \<in> r" using assms equiv_Eps_in in_quotient_imp_in_rel by fastsimp
next
  fix x assume "(Eps X,x) \<in> r"
  thus "x \<in> X" using assms equiv_Eps_in in_quotient_imp_closed by fastsimp
qed


lemma Eps_proj: 
assumes "equiv A r" and "x \<in> A"
shows "(Eps(proj r x), x) \<in> r"
proof-
  have 1: "proj r x \<in> A//r" using assms proj_preserves by fastsimp
  hence "Eps(proj r x) \<in> proj r x" using assms equiv_Eps_in by auto
  moreover have "x \<in> proj r x" using assms in_proj by fastsimp
  ultimately show ?thesis using assms 1 in_quotient_imp_in_rel by fastsimp
qed


lemma equiv_Eps_iff:
assumes "equiv A r" and "{X,Y} \<subseteq> A//r"
shows "((Eps X,Eps Y) \<in> r) = (X = Y)"
proof-
  have "Eps X \<in> X \<and> Eps Y \<in> Y" using assms equiv_Eps_in by auto
  thus ?thesis using assms quotient_eq_iff by fastsimp
qed


lemma equiv_Eps_inj_on:
assumes "equiv A r"
shows "inj_on Eps (A//r)"
unfolding inj_on_def proof clarify
  fix X Y assume X: "X \<in> A//r" and Y: "Y \<in> A//r" and Eps: "Eps X = Eps Y"
  hence "Eps X \<in> A" using assms equiv_Eps_preserves by auto
  hence "(Eps X, Eps Y) \<in> r" 
  using assms Eps unfolding quotient_def equiv_def refl_on_def by auto
  thus "X= Y" using X Y assms equiv_Eps_iff by auto
qed


lemma univ_commute[simp]:
assumes ECH: "equiv A r" and RES: "f respects r" and x: "x \<in> A"
shows "(univ f) (proj r x) = f x"
unfolding univ_def proof-
  have prj: "proj r x \<in> A//r" using x proj_preserves by fastsimp
  hence "Eps (proj r x) \<in> A" using ECH equiv_Eps_preserves by fastsimp
  moreover have "proj r (Eps (proj r x)) = proj r x" using ECH prj proj_Eps by fastsimp
  ultimately have "(x, Eps (proj r x)) \<in> r" using x ECH proj_iff by fastsimp
  thus "f (Eps (proj r x)) = f x" using RES unfolding congruent_def by auto
qed


lemma univ_unique:
assumes ECH: "equiv A r" and
        RES: "f respects r" and  COM: "\<forall> x \<in> A. G (proj r x) = f x"
shows "\<forall> X \<in> A//r. G X = univ f X"
proof
  fix X assume "X \<in> A//r"
  then obtain x where x: "x \<in> A" and X: "X = proj r x" using ECH proj_image[of r A] by blast
  have "G X = f x" unfolding X using x COM by simp
  thus "G X = univ f X" unfolding X using ECH RES x univ_commute by fastsimp
qed


lemma univ_preserves: 
assumes ECH: "equiv A r" and RES: "f respects r" and 
       PRES: "\<forall> x \<in> A. f x \<in> B"
shows "\<forall> X \<in> A//r. univ f X \<in> B"
proof
  fix X assume "X \<in> A//r"
  then obtain x where x: "x \<in> A" and X: "X = proj r x" using ECH proj_image[of r A] by blast
  hence "univ f X = f x" using assms univ_commute by fastsimp
  thus "univ f X \<in> B" using x PRES by auto
qed




end
