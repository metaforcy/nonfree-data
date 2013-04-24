(* Alternative descriptions of finite sets and the transport of the
recursors to the type of sets *)
theory FSets_Alternatives
imports FSets_Bags
begin


section{* Finite sets initial semi-lattice with unit (ACIU): *}

nonfreedata 'a fsetS = SEmp | SSingl 'a | SUni "'a fsetS" "'a fsetS"
where
  Assoc: "SUni (SUni A1 A2) A3 = SUni A1 (SUni A2 A3)"
| Comm: "SUni A1 A2 = SUni A2 A1"
| Idem: "SUni A A = A"
| Id: "SUni SEmp A = A"

declare Idem[simp]  declare Id[simp]

lemma SUni_SEmp[simp]: "SUni A SEmp = A"
by (metis Comm Id)

nonfreeiter from_fsetS :: "'a fsetS \<Rightarrow> 'a fset"
where
  "from_fsetS SEmp = Emp"
| "from_fsetS (SSingl a) = Singl a"
| "from_fsetS (SUni A1 A2) = Uni (from_fsetS A1) (from_fsetS A2)"
apply auto using Uni_assoc Uni_com by metis+

nonfreeiter to_fsetS :: "'a fset \<Rightarrow> 'a fsetS"
where
  "to_fsetS Emp = SEmp"
| "to_fsetS (Ins a A) = SUni (SSingl a) (to_fsetS A)"
by (metis Assoc Idem Comm)+

lemma from_fsetS_to_fsetS[simp]: "from_fsetS (to_fsetS A) = A"
by (induct A) (auto simp: Singl_def)

lemma asFSetsS_Uni[simp]: "to_fsetS (Uni A B) = SUni (to_fsetS A) (to_fsetS B)"
apply(induction A) apply auto using Assoc
apply metis done

lemma to_fsetS_from_fsetS[simp]: "to_fsetS (from_fsetS A) = A"
apply(induction A) by (auto simp: Singl_def)


section{* Nonempty finite sets, as initial semilattice (ACI): *}

nonfreedata 'a fsetN = NSingl 'a | NUni "'a fsetN" "'a fsetN"
where
  AssocN: "NUni (NUni A1 A2) A3 = NUni A1 (NUni A2 A3)"
| CommN: "NUni A1 A2 = NUni A2 A1"
| IdemN: "NUni A A = A"

nonfreeiter memN :: "'a \<Rightarrow> 'a fsetN \<Rightarrow> bool"
where
  "memN b (NSingl a) = (a = b)"
| "memN b (NUni A B) = (memN b A \<or> memN b B)"
using Ins2 by auto

nonfreeiter from_fsetN :: "'a fsetN \<Rightarrow> 'a fset"
where
  "from_fsetN (NSingl a) = Singl a"
| "from_fsetN (NUni A1 A2) = Uni (from_fsetN A1) (from_fsetN A2)"
apply auto using Uni_assoc Uni_com by metis+

lemma mem_from_fsetN[simp]:
"mem a (from_fsetN A) \<longleftrightarrow> memN a A"
by (induction A) (auto simp: Singl_def)

definition "to_fsetN A \<equiv> SOME N. from_fsetN N = A"

lemma from_fsetN_to_fsetN: "A \<noteq> Emp \<Longrightarrow> from_fsetN (to_fsetN A) = A"
unfolding to_fsetN_def apply(rule someI_ex) apply(induction A, simp_all)
by (metis Singl_def Uni_Emp2 Uni_Ins2 from_fsetN.simps)

lemma from_fsetN_not_Emp[simp]: "from_fsetN A \<noteq> Emp"
by(induction A) auto

lemma from_fsetN_inj[simp]: "from_fsetN A = from_fsetN B \<longleftrightarrow> A = B"
by sorry2

lemma to_fsetN_from_fsetN[simp]: "to_fsetN (from_fsetN A) = A"
by (metis from_fsetN_inj from_fsetN_not_Emp from_fsetN_to_fsetN)

lemma to_fsetN_Ins[simp]: "A \<noteq> Emp \<Longrightarrow> to_fsetN (Ins a A) = NUni (NSingl a) (to_fsetN A)"
by (metis Singl_def Uni.simps from_fsetN.simps from_fsetN_to_fsetN to_fsetN_from_fsetN)

lemma to_fsetN_Ins_Emp[simp]: "to_fsetN (Ins a Emp) = NSingl a"
by (metis Singl_def from_fsetN.simps(2) to_fsetN_from_fsetN)

lemma to_fsetN_inj[simp]:
assumes "A \<noteq> Emp" and "B \<noteq> Emp"
shows "to_fsetN A = to_fsetN B \<longleftrightarrow> A = B"
by (metis assms from_fsetN_to_fsetN)

lemma memN_to_fsetN[simp]:
"A \<noteq> Emp \<Longrightarrow> memN a (to_fsetN A) \<longleftrightarrow> mem a A"
by (metis from_fsetN_to_fsetN mem_from_fsetN)

lemma to_fsetN_Uni[simp]:
assumes "A \<noteq> Emp" and "B \<noteq> Emp"
shows "to_fsetN (Uni A B) = NUni (to_fsetN A) (to_fsetN B)"
by (metis assms from_fsetN.simps from_fsetN_to_fsetN to_fsetN_from_fsetN)


section{* Nonempty finite sets, as singleton-insert view: *}

nonfreedata 'a fsetNN = NNSingl 'a | NNIns 'a "'a fsetNN"
where
  NNIns1: "NNIns a (NNIns a A) = NNIns a A"
| NNIns2: "NNIns a1 (NNIns a2 A) = NNIns a2 (NNIns a1 A)"

nonfreeiter memNN :: "'a \<Rightarrow> 'a fsetNN \<Rightarrow> bool"
where
  "memNN b (NNSingl a) = (a = b)"
| "memNN b (NNIns a A) = (a = b \<or> memNN b A)"
using Ins2 by auto

nonfreeiter from_fsetNN :: "'a fsetNN \<Rightarrow> 'a fset"
where
  "from_fsetNN (NNSingl a) = Singl a"
| "from_fsetNN (NNIns a A) = Ins a (from_fsetNN A)"
using Ins2 by auto

lemma mem_from_fsetNN[simp]:
"mem a (from_fsetNN A) \<longleftrightarrow> memNN a A"
by (induction A, auto simp: Singl_def)

definition "to_fsetNN A \<equiv> SOME NN. from_fsetNN NN = A"

lemma from_fsetNN_to_fsetNN: "A \<noteq> Emp \<Longrightarrow> from_fsetNN (to_fsetNN A) = A"
unfolding to_fsetNN_def apply(rule someI_ex) apply(induction A, simp_all)
by (metis Singl_def from_fsetNN.simps)

lemma from_fsetNN_not_Emp[simp]: "from_fsetNN A \<noteq> Emp"
by(induction A) auto

lemma from_fsetNN_inj[simp]: "from_fsetNN A = from_fsetNN B \<longleftrightarrow> A = B"
by sorry2

lemma to_fsetNN_from_fsetNN[simp]: "to_fsetNN (from_fsetNN A) = A"
by (metis from_fsetNN_inj from_fsetNN_not_Emp from_fsetNN_to_fsetNN)

lemma to_fsetNN_Ins[simp]: "A \<noteq> Emp \<Longrightarrow> to_fsetNN (Ins a A) = NNIns a (to_fsetNN A)"
by (metis from_fsetNN.simps from_fsetNN_to_fsetNN to_fsetNN_from_fsetNN)

lemma to_fsetNN_inj[simp]:
assumes "A \<noteq> Emp" and "B \<noteq> Emp"
shows "to_fsetNN A = to_fsetNN B \<longleftrightarrow> A = B"
by (metis assms from_fsetNN_to_fsetNN)

lemma memNN_to_fsetNN[simp]:
"A \<noteq> Emp \<Longrightarrow> memNN a (to_fsetNN A) \<longleftrightarrow> mem a A"
by (metis from_fsetNN_to_fsetNN mem_from_fsetNN)

lemma to_fsetNN_Ins_Emp[simp]:
"to_fsetNN (Ins a Emp) = NNSingl a"
by (metis Singl_def from_fsetNN.simps to_fsetNN_from_fsetNN)


section{* Cover existing fold functions: *}

(* Isabelle's fold for finite sets: *)
locale Isabelle =
fixes f :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
assumes f_assoc: "f (f a b) c = f a (f b c)"
    and f_comm: "f a b = f b a"
begin

nonfreeiter fold1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<times> 'b"
where
  "fold1 g z Emp = (Emp, z)"
| "fold1 g z (Ins a A) =
   (case fold1 g z A of (A,b) \<Rightarrow> (Ins a A, if mem a A then b else f (g a) b))"
using f_comm f_assoc Ins2 by auto

lemma fold1: "fold1 g z A = (A',b) \<Longrightarrow> A = A'"
by (induct arbitrary: A' b rule: fset_induct) (auto split: prod.splits)

definition fold :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'b"
where "fold g z = snd o (fold1 g z)"

lemma fold_simps[simp]:
  "fold g z Emp = z"
  "fold g z (Ins a A) = (if mem a A then fold g z A else f (g a) (fold g z A))"
  "\<not> mem a A \<Longrightarrow> fold g z (Ins a A) = f (g a) (fold g z A)"
unfolding fold_def using fold1 by (fastforce split: prod.splits)+

end

(* HOL4 and PVS fold for finite sets: *)
locale HOL4_PVS =
fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
assumes f_left_comm: "f a1 (f a2 b) = f a2 (f a1 b)"
begin

nonfreeiter fold1 :: "'b \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<times> 'b"
where
  "fold1 z Emp = (Emp, z)"
| "fold1 z (Ins a A) =
   (case fold1 z A of (A,b) \<Rightarrow> (Ins a A, if mem a A then b else f a b))"
using f_left_comm Ins2 by force+

lemma fold1: "fold1 z A = (A',b) \<Longrightarrow> A = A'"
by (induct arbitrary: A' b rule: fset_induct) (auto split: prod.splits)

definition fold :: "'b \<Rightarrow> 'a fset \<Rightarrow> 'b"
where "fold z = snd o (fold1 z)"

lemma fold_simps[simp]:
  "fold z Emp = z"
  "fold z (Ins a A) = (if mem a A then fold z A else f a (fold z A))"
  "\<not> mem a A \<Longrightarrow> fold z (Ins a A) = f a (fold z A)"
unfolding fold_def using fold1 by (fastforce split: prod.splits)+

end

(* Isabelle's fold for nonempty finite sets: *)
locale Isabelle_NE =
fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
assumes f_assoc: "f (f a b) c = f a (f b c)"
    and f_comm: "f a b = f b a"
begin

nonfreeiter fold1 :: "'a fsetNN \<Rightarrow> 'a fsetNN \<times> 'a"
where
  "fold1 (NNSingl a) = (NNSingl a, a)"
| "fold1 (NNIns a A) =
   (case fold1 A of (A,b) \<Rightarrow> (NNIns a A, if memNN a A then b else f a b))"
using f_comm f_assoc NNIns1 NNIns2 by fastforce+

lemma fold1: "fold1 A = (A',b) \<Longrightarrow> A = A'"
by (induction A arbitrary: A' b) (auto split: prod.splits)

definition fold :: "'a fsetNN \<Rightarrow> 'a"
where "fold = snd o fold1"

lemma fold_simps[simp]:
  "fold (NNSingl a) = a"
  "fold (NNIns a A) = (if memNN a A then fold A else f a (fold A))"
  "\<not> memNN a A \<Longrightarrow> fold (NNIns a A) = f a (fold A)"
unfolding fold_def using fold1 by (fastforce split: prod.splits)+

end


section{* Transfer to the type 'a set *}

definition fold_fset :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
"fold_fset E I = iter_fset E I o asFset"

(* Fold equations coming from 'a fset : *)
lemma fold_fset_emp:
assumes "\<And>a b. I a (I a b) = I a b"
and "\<And> a1 a2 b. I a1 (I a2 b) = I a2 (I a1 b)"
shows "fold_fset E I {} = E"
unfolding fold_fset_def comp_def using assms apply simp
apply(rule fset_iter_rews) by auto

lemma fold_fset_insert:
assumes A: "finite A"
and "\<And>a b. I a (I a b) = I a b"
and "\<And> a1 a2 b. I a1 (I a2 b) = I a2 (I a1 b)"
shows "fold_fset E I (insert a A) = I a (fold_fset E I A)"
unfolding fold_fset_def comp_def using assms apply simp
apply(rule fset_iter_rews) by auto

definition fold_fsetS :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
"fold_fsetS E S U = iter_fsetS E S U o (to_fsetS o asFset)"

(* Fold equations coming from 'a fsetS : *)
lemma fold_fsetS_emp:
assumes "\<And>a b c. U (U a b) c = U a (U b c)"
and "\<And> a b. U a b = U b a"
and "\<And> a. U a a = a"
and "\<And> a. U a E = a"
shows "fold_fsetS E S U {} = E"
unfolding fold_fsetS_def comp_def using assms apply simp
apply(rule fsetS_iter_rews) by auto

lemma fold_fsetS_singl:
assumes "\<And>a b c. U (U a b) c = U a (U b c)"
and "\<And> a b. U a b = U b a"
and "\<And> a. U a a = a"
and "\<And> a. U a E = a"
shows "fold_fsetS E S U {a} = S a"
unfolding fold_fsetS_def comp_def using assms apply simp
apply(rule fsetS_iter_rews) by auto

lemma fold_fsetS_Un:
assumes A: "finite A" and B: "finite B"
and "\<And>a b c. U (U a b) c = U a (U b c)"
and "\<And> a b. U a b = U b a"
and "\<And> a. U a a = a"
and "\<And> a. U a E = a"
shows "fold_fsetS E S U (A \<union> B) = U (fold_fsetS E S U A) (fold_fsetS E S U B)"
unfolding fold_fsetS_def comp_def using assms apply simp
apply(rule fsetS_iter_rews) by auto

(* Fold equations coming from 'a fsetN : *)
definition fold_fsetN :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
"fold_fsetN S U \<equiv> iter_fsetN S U o (to_fsetN o asFset)"

lemma fold_fsetN_singl:
assumes "\<And>a b c. U (U a b) c = U a (U b c)"
and "\<And> a b. U a b = U b a"
and "\<And> a. U a a = a"
shows "fold_fsetN S U {a} = S a"
unfolding fold_fsetN_def comp_def using assms apply simp
apply(rule fsetN_iter_rews) by auto

lemma fold_fsetN_Un:
assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
and "\<And>a b c. U (U a b) c = U a (U b c)"
and "\<And> a b. U a b = U b a"
and "\<And> a. U a a = a"
shows "fold_fsetN S U (A \<union> B) = U (fold_fsetN S U A) (fold_fsetN S U B)"
unfolding fold_fsetN_def comp_def using assms apply simp
apply(rule fsetN_iter_rews) by auto

(* Fold equations coming from 'a fsetNN : *)
definition fold_fsetNN :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b" where
"fold_fsetNN S I \<equiv> iter_fsetNN S I o (to_fsetNN o asFset)"

lemma fold_fsetNN_singl:
assumes "\<And>a1 a2 b. I a1 (I a2 b) =  I a2 (I a1 b)"
and "\<And>a b. I a (I a b) = I a b"
shows "fold_fsetNN S I {a} = S a"
unfolding fold_fsetNN_def comp_def using assms apply simp
apply(rule fsetNN_iter_rews) by auto

lemma fold_fsetNN_Un:
assumes A: "finite A" "A \<noteq> {}"
and "\<And>a1 a2 b. I a1 (I a2 b) =  I a2 (I a1 b)"
and "\<And>a b. I a (I a b) =  I a b"
shows "fold_fsetNN S I (insert a A) = I a (fold_fsetNN S I A)"
unfolding fold_fsetNN_def comp_def using assms apply simp
apply(rule fsetNN_iter_rews) by auto


(* TODO: Remove the 2 sorries. *)




end
