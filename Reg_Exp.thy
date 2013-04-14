theory Reg_Exp
imports NonFreeInput
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

(* Interpretation as abstract relation algebra, on the powerset of a monoid: *)
definition Mult :: "('a::monoid_mult) set \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
"Mult P Q \<equiv> {p * q | p q. p \<in> P \<and> q \<in> Q}"

declare algebra_simps[simp]

lemma Mult_Assoc: "Mult (Mult L1 L2) L3 = Mult L1 (Mult L2 L3)"
unfolding Mult_def apply (auto simp: algebra_simps)
apply metis sorry

lemma Mult_Singl_One: "Mult {1} L = L"
unfolding Mult_def by auto

lemma Mult_emp: "Mult {} L = {}"
unfolding Mult_def by auto

lemma Mult_Un: "Mult L (L1 \<union> L2) = Mult L L1 \<union> Mult L L2"
unfolding Mult_def by auto

inductive_set Mstar for L :: "('a::monoid_mult) set" where
One: "1 \<in> Mstar L"
|
Times: "\<lbrakk>w \<in> L; w1 \<in> Mstar L\<rbrakk> \<Longrightarrow> w * w1 \<in> Mstar L"

lemma incl_Mstar[simp]: "w \<in> L \<Longrightarrow> w \<in> Mstar L"
using Mstar.intros by (metis mult_1_right)

lemma append_Mstar: "\<lbrakk>w \<in> Mstar L; w1 \<in> L\<rbrakk> \<Longrightarrow> w * w1 \<in> Mstar L"
apply(induction rule: Mstar.induct) by (auto intro: Mstar.intros)

lemma Mult_Mstar_R: "Mult L (Mstar L) \<subseteq> Mstar L"
unfolding Mult_def by (auto intro: Mstar.intros)

lemma Mult_Mstar_L: "Mult (Mstar L) L \<subseteq> Mstar L"
unfolding Mult_def by (auto intro: append_Mstar)

lemma Mult_Mstar_Min_L:
assumes "Mult L1 L \<subseteq> L"  shows "Mult (Mstar L1) L \<subseteq> L"
unfolding Mult_def proof safe
  fix x w1 w2 assume "w1 \<in> Mstar L1" and "w2 \<in> L"
  thus "w1 * w2 \<in> L"
  using assms unfolding Mult_def by (induction rule: Mstar.induct) auto
qed

lemma Mult_Mstar_Min_R:
assumes "Mult L L1 \<subseteq> L"  shows "Mult L (Mstar L1) \<subseteq> L"
unfolding Mult_def proof safe
  fix x w1 w2 assume "w2 \<in> Mstar L1" and "w1 \<in> L"
  thus "w1 * w2 \<in> L"
  proof (induction arbitrary: w1 rule: Mstar.induct)
    case (Times w w1 w1a)
    hence "w1a * w \<in> L" using assms unfolding Mult_def by auto
    from Times.IH[OF this] show ?case by simp
  qed auto
qed

nonfreeiter kinter :: "('a \<Rightarrow> 'b::monoid_mult) \<Rightarrow> 'a exp \<Rightarrow> 'b set"
where
  "kinter f (Let a) = {f a}"
| "kinter f Zero = {}"
| "kinter f One = {1}"
| "kinter f (Plus e1 e2) = kinter f e1 \<union> kinter f e2"
| "kinter f (Times e1 e2) = Mult (kinter f e1) (kinter f e2)"
| "kinter f (Star e) = Mstar (kinter f e)"
apply (metis sup.commute)
apply (metis Sup_fin.idem)
apply (metis sup_bot_left)
apply auto[]
apply (metis Mstar.One)
apply (metis Mult_Mstar_L subsetD)
apply (metis Mult_Singl_One)
apply (metis Un_left_commute sup.commute)
apply auto[]
apply (metis Mstar.One)
apply (metis Mult_Mstar_R subsetD)
apply (metis Mult_Un)
apply (metis Mult_emp)
apply (metis Mult_Assoc)
apply (metis Mult_Mstar_Min_L Un_commute sup_absorb1 sup_ge1)
by (metis Mult_Mstar_Min_R Un_upper2 sup.commute sup_absorb1)

(* Instantiation to regaular languages: *)
instantiation list :: (type)monoid_mult begin
  definition times_list where "xs * ys = xs @ ys"
  definition one_list where "1 = []"
  instance apply default unfolding times_list_def one_list_def by auto

definition "lang \<equiv> kinter (\<lambda> a. [a])"
abbreviation "Append \<equiv> Mult :: 'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
abbreviation "Lstar \<equiv> Mstar :: 'a list set \<Rightarrow> 'a list set"

lemma lang_simps:
  "lang (Let a) = {[a]}"
  "lang Zero = {}"
  "lang One = {[]}"
  "lang (Plus e1 e2) = lang e1 \<union> lang e2"
  "lang (Times e1 e2) = Append (lang e1) (lang e2)"
  "lang (Star e) = Lstar (lang e)"
unfolding lang_def by (auto simp: times_list_def one_list_def)

(* Instantiation to algebra of relations: *)






end
