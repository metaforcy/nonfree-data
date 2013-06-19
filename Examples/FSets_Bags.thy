(* The types of finite sets and bags *)
theory FSets_Bags
imports "../NonFreeInput"
begin


(* Datatype of finite sets: *)
nonfreedata 'a fset = Emp | Ins 'a "'a fset"
where
  Ins1: "Ins a (Ins a A) = Ins a A"
| Ins2: "Ins a1 (Ins a2 A) = Ins a2 (Ins a1 A)"

declare Ins1[simp]

(* Datatype of bags: *)
nonfreedata 'a bag = BEmp | BIns 'a "'a bag"
where BIns: "BIns a1 (BIns a2 B) = BIns a2 (BIns a1 B)"


nonfreeiter fset_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
where
  "fset_map f Emp = Emp"
| "fset_map f (Ins a A) = Ins (f a) (fset_map f A)"
by (auto simp: Ins1 Ins2)

nonfreeiter bag_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a bag \<Rightarrow> 'b bag"
where
  "bag_map f BEmp = BEmp"
| "bag_map f (BIns a B) = BIns (f a) (bag_map f B)"
by (auto simp: BIns)

(* Membership of an item in a finite set *)
nonfreeiter mem :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool"
where
  "mem a Emp = False"
| "mem a (Ins b B) = (a = b \<or> mem a B)"
by auto

lemma mem_Ins[simp]: "mem a A \<Longrightarrow> Ins a A = A"
by (induction arbitrary: a rule: fset_induct) (auto simp: Ins2)

(* Multiplicity of an item in bag *)
nonfreeiter mult :: "'a \<Rightarrow> 'a bag \<Rightarrow> nat"
where
  "mult a BEmp = 0"
| "mult a (BIns b B) = (if a = b then Suc (mult a B) else mult a B)"
by (auto simp: BIns)

(* Flattening operator from bags to finite sets *)
nonfreeiter flat :: "'a bag \<Rightarrow> 'a fset"
where
  "flat BEmp = Emp"
| "flat (BIns a B) = Ins a (flat B)"
by (auto simp: Ins2)

lemma mem_flat_mult[simp]: "mem a (flat A) \<longleftrightarrow> mult a A \<noteq> 0"
by (induction rule: bag_induct) auto

(* Embedding of finite sets into bags *)
nonfreeiter embed :: "'a fset \<Rightarrow> 'a bag"
where
  "embed Emp = BEmp"
| "embed (Ins a A) = (if mult a (embed A) = 0 then BIns a (embed A) else embed A)"
by (auto simp: BIns)

lemma mult_embed_mem[simp]: "mult a (embed A) \<noteq> 0 \<longleftrightarrow> mem a A"
by (induction rule: fset_induct) auto

(* Cardinal of finite sets: *)
nonfreeiter card1 :: "'a fset \<Rightarrow> 'a fset * nat"
where
  "card1 Emp = (Emp, 0)"
| "card1 (Ins a A) = (case card1 A of (A,n) \<Rightarrow> (Ins a A, if mem a A then n else Suc n))"
by (auto simp: Ins2)

lemma card1: "card1 A = (A',n) \<Longrightarrow> A = A'"
by (induct arbitrary: A' n rule: fset_induct) (auto split: prod.splits)

definition card :: "'a fset \<Rightarrow> nat" where "card \<equiv> snd o card1"

lemma card_simps[simp]:
  "card Emp = 0"
  "card (Ins a A) = (if mem a A then card A else Suc (card A))"
unfolding card_def using card1 by (auto split: prod.splits)

(* Sum of a numeric function over a finite set: *)
nonfreeiter sum1 :: "('a \<Rightarrow> nat) \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<times> nat"
where
  "sum1 f Emp = (Emp, 0)"
| "sum1 f (Ins a A) = (case sum1 f A of (A,n) \<Rightarrow> (Ins a A, if mem a A then n else n + f a))"
by (auto simp: Ins2)

lemma sum1: "sum1 f A = (A',n) \<Longrightarrow> A = A'"
by (induct arbitrary: A' n rule: fset_induct) (auto split: prod.splits)

definition sum :: " ('a \<Rightarrow> nat) \<Rightarrow> 'a fset \<Rightarrow> nat" where "sum f \<equiv> snd o sum1 f"

lemma sum_simps[simp]:
  "sum f Emp = 0"
  "sum f (Ins a A) = (if mem a A then sum f A else sum f A + f a)"
unfolding sum_def using sum1 by (auto split: prod.splits)

(* Sum of a numeric function over a bag: *)
nonfreeiter bsum' :: "('a \<Rightarrow> nat) \<Rightarrow> 'a bag \<Rightarrow> nat"
where
  "bsum' f BEmp = 0"
| "bsum' f (BIns a B) = bsum' f B + f a"
by auto

(* More generally: Sum of a commutative-monoid-valed function over a bag: *)
nonfreeiter bsum :: "('a \<Rightarrow> 'b::comm_monoid_add) \<Rightarrow> 'a bag \<Rightarrow> 'b"
where
  "bsum f BEmp = 0"
| "bsum f (BIns a B) = bsum f B + f a"
by (auto simp: algebra_simps)

(* Embedding of finite sets as sets: *)
nonfreeiter asSet :: "'a fset \<Rightarrow> 'a set"
where
  "asSet Emp = {}"
| "asSet (Ins a A) = insert a (asSet A)"
by auto

lemma in_asSet[simp]: "a \<in> asSet F \<longleftrightarrow> mem a F"
by (induction F) auto

lemma mem_ex_Ins: "mem a F \<Longrightarrow> \<exists> F'. \<not> mem a F' \<and> F = Ins a F'"
by (induction F) (metis Ins2 mem.simps mem_Ins)+

lemma finite_asSet[simp, intro]: "finite (asSet A)"
by (induction rule: fset_induct) auto

lemma finite_imp_asSet: "finite A \<Longrightarrow> (\<exists> F. A = asSet F)"
by (induction rule: finite_induct) (metis asSet.simps)+

lemma asSet_eq_emp[simp]: "asSet F = {} \<Longrightarrow> Emp = F"
by (induction F) auto

lemma asSet_inj[simp]: "asSet F1 = asSet F2 \<longleftrightarrow> F1 = F2"
proof(safe, induction F1 arbitrary: F2)
  fix a F1 F2 assume IH: "\<And>F2. asSet F1 = asSet F2 \<Longrightarrow> F1 = F2"
  and e: "asSet (Ins a F1) = asSet F2"
  hence "mem a F2" by auto
  then obtain F2' where F2': "\<not> mem a F2'" and F2: "F2 = Ins a F2'" using mem_ex_Ins[of a F2] by blast
  show "Ins a F1 = F2"
  proof(cases "mem a F1")
    case False
    hence "asSet F1 = asSet F2'" using e F2' unfolding F2 by auto
    thus ?thesis unfolding F2 using IH by auto
  qed(insert e IH, auto)
qed auto

definition asFset :: "'a set \<Rightarrow> 'a fset" where
"asFset A \<equiv> SOME F. asSet F = A"

lemma asSet_asFset[simp]:
assumes "finite A"  shows "asSet (asFset A) = A"
unfolding asFset_def apply(rule someI_ex) using finite_imp_asSet[OF assms] by blast

lemma asFset_asSet[simp]: "asFset (asSet A) = A"
by (metis asSet_asFset asSet_inj finite_asSet)

lemma asFset_emp[simp]: "asFset {} = Emp"
by (metis asFset_asSet asSet.simps)

lemma asFset_insert[simp]: "finite A \<Longrightarrow> asFset (insert a A) = Ins a (asFset A)"
by (metis asFset_asSet asSet.simps finite_imp_asSet)

(* ACIU view: *)
definition "Singl a \<equiv> Ins a Emp"

nonfreeiter Uni :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
where
  "Uni Emp = (\<lambda> B. B)"
| "Uni (Ins a A) = (\<lambda> B. Ins a (Uni A B))"
by (auto simp: Ins2)

lemma Uni_Emp[simp]: "Uni Emp B = B"
and Uni_Ins[simp]: "Uni (Ins a A) B = Ins a (Uni A B)"
by auto

declare Uni.simps[simp del]

lemma Uni_Emp2[simp]: "Uni A Emp = A"
by(induction A) auto

lemma Uni_Ins2[simp]: "Uni A (Ins b B) = Ins b (Uni A B)"
by (induction A) (auto simp: Ins2)

lemma Uni_assoc: "Uni (Uni A B) C = Uni A (Uni B C)"
by (induction A) auto

lemma Uni_com: "Uni A B = Uni B A"
by (induction A) auto

lemma Uni_idem[simp]: "Uni A A = A"
by (induction A) auto

lemma Ins_not_Emp[simp]: "Ins a A \<noteq> Emp"
by (induct A) (metis mem.simps)+

lemma Singl_not_Emp[simp]: "Singl a \<noteq> Emp"
unfolding Singl_def by simp

lemma Uni_eq_Emp[simp]: "Uni A B = Emp \<longleftrightarrow> A = Emp \<and> B = Emp"
by (induct A) auto

lemma mem_Uni[simp]: "mem a (Uni A B) \<longleftrightarrow> mem a A \<or> mem a B"
by (induction A) auto

lemma asFset_Uni[simp]:
assumes "finite A" and "finite B"
shows "asFset (A \<union> B) = Uni (asFset A) (asFset B)"
using assms by (induct) auto

lemma asFset_eq_Emp[simp]: assumes "finite A"  shows "asFset A = Emp \<longleftrightarrow> A = {}"
using assms by (induction, auto)



end


