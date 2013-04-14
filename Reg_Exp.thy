theory Reg_Exp
imports NonFree
uses "input.ML"
begin

(* Regular expressions as the freely generated Kleene algebra: *)

nonfreedata 'a exp = Let 'a | Zero | One | Plus "'a exp" "'a exp" |
                     Times "'a exp" "'a exp" | Star "'a exp"
where
   Plus_Assoc: "Plus (Plus e1 e2) e3 = Plus e1 (Plus e2 e3)"
 | Plus_Comm: "Plus e1 e2 = Plus e2 e1"
 | Plus_Zero: "Plus Zero e = e"
 | Plus_Idem: "Plus e e = e"
 | Times_Assoc: "Times (Times e1 e2) e3 = Times e1 (Times e2 e3)"
 | Times_One: "Times One e = e"
 | Times_Zero: "Times Zero e = Zero"
 | Times_Plus: "Times e1 (Plus e2 e3) = Plus (Times e1 e2) (Times e1 e3)"
 | Star_Left: "Plus (Plus One (Times (Star e) e)) (Star e) = Star e"
 | Star_Right: "Plus (Plus One (Times e (Star e))) (Star e) = Star e"
 | Star_Left_Min: "Plus (Times e e1) e1 = e1 \<Longrightarrow> Plus (Times (Star e) e1) e1 = e1"
 | Star_Right_Min: "Plus (Times e1 e) e1 = e1 \<Longrightarrow> Plus e1 (Times e1 (Star e)) = e1"

lemma concat_append_singl: "List.concat (xss @ [xs]) = List.concat xss @ xs"
by auto

definition "Append L1 L2 \<equiv> { w1 @ w2 | w1 w2. w1 \<in> L1 \<and> w2 \<in> L2}"

lemma Append_Assoc: "Append (Append L1 L2) L3 = Append L1 (Append L2 L3)"
unfolding Append_def by auto (metis append_assoc)+

lemma Append_Singl_Nil: "Append {[]} L = L"
unfolding Append_def by auto

lemma Append_emp: "Append {} L = {}"
unfolding Append_def by auto

lemma Append_Un: "Append L (L1 \<union> L2) = Append L L1 \<union> Append L L2"
unfolding Append_def by auto

inductive_set Kstar for L where
Nil: "[] \<in> Kstar L"
|
Append: "\<lbrakk>w \<in> L; w1 \<in> Kstar L\<rbrakk> \<Longrightarrow> w @ w1 \<in> Kstar L"

lemma incl_Kstar[simp]: "w \<in> L \<Longrightarrow> w \<in> Kstar L"
by (metis Kstar.Append Kstar.Nil append_Nil2)

lemma append_Kstar: "\<lbrakk>w \<in> Kstar L; w1 \<in> L\<rbrakk> \<Longrightarrow> w @ w1 \<in> Kstar L"
apply(induction rule: Kstar.induct) by (auto intro: Kstar.intros)

lemma Append_Kstar_R: "Append L (Kstar L) \<subseteq> Kstar L"
unfolding Append_def by (auto intro: Kstar.intros)

lemma Append_Kstar_L: "Append (Kstar L) L \<subseteq> Kstar L"
unfolding Append_def by (auto intro: append_Kstar)

lemma Append_Kstar_Min_L:
assumes "Append L1 L \<subseteq> L"  shows "Append (Kstar L1) L \<subseteq> L"
unfolding Append_def proof safe
  fix x w1 w2 assume "w1 \<in> Kstar L1" and "w2 \<in> L"
  thus "w1 @ w2 \<in> L"
  using assms unfolding Append_def by (induction rule: Kstar.induct) auto
qed

lemma Append_Kstar_Min_R:
assumes "Append L L1 \<subseteq> L"  shows "Append L (Kstar L1) \<subseteq> L"
unfolding Append_def proof safe
  fix x w1 w2 assume "w2 \<in> Kstar L1" and "w1 \<in> L"
  thus "w1 @ w2 \<in> L"
  apply(induction arbitrary: w1 rule: Kstar.induct) using assms unfolding Append_def apply auto
  sorry (* TODO *)
qed

nonfreeiter lang :: "'a exp \<Rightarrow> 'a list set"
where
  "lang (Let a) = {[a]}"
| "lang Zero = {}"
| "lang One = {[]}"
| "lang (Plus e1 e2) = lang e1 \<union> lang e2"
| "lang (Times e1 e2) = Append (lang e1) (lang e2)"
| "lang (Star e) = Kstar (lang e)"
apply (metis sup.commute)
apply (metis Sup_fin.idem)
apply (metis sup_bot_left)
apply auto[]
apply (metis Kstar.Nil)
apply (metis Append_Kstar_L subsetD)
apply (metis Append_Singl_Nil)
apply (metis Un_left_commute sup.commute)
apply auto[]
apply (metis Kstar.Nil)
apply (metis Append_Kstar_R subsetD)
apply (metis Append_Un)
apply (metis Append_emp)
apply (metis Append_Assoc)
apply (metis Append_Kstar_Min_L Un_commute sup_absorb1 sup_ge1)
by (metis Append_Kstar_Min_R Un_upper2 sup.commute sup_absorb1)

(* TODO: The monoid powerset interpretation and the instance to relation algebra *)



end