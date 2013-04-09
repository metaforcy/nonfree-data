theory FSets_Bags
imports NonFree
uses "input.ML"
begin

(* Andy:
1) Fixed name for the induction rules such as NonFreeInput.induction_rule722296?
Currently, each time I process the datatype I get a different name!
Also, we should declare them automatically as default induction rules for theoir types?

2) replace keyword "nonfreedata" with "alg_datatype"?
*)


(* Datatype of finite sets: *)
nonfreedata 'a fset = Emp | Ins 'a "'a fset"
where
  Ins1: "Ins a (Ins a s) = Ins a s"
| Ins2: "Ins a1 (Ins a2 s) = Ins a2 (Ins a1 s)"

declare Ins1[simp]

(* Datatype of bags: *)
nonfreedata 'a bag = BEmp | BIns 'a "'a bag"
where BIns: "BIns a1 (BIns a2 s) = BIns a2 (BIns a1 s)"


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
nonfreeiter mem :: "'a fset \<Rightarrow> 'a \<Rightarrow> bool"
where
  "mem Emp = (\<lambda> a. False)"
| "mem (Ins b B) = (\<lambda> a. a = b \<or> mem B a)"
by (auto intro!: ext)

lemma mem_Ins[simp]: "mem A a \<Longrightarrow> Ins a A = A"
by (induction arbitrary: a rule: fset_induct) (auto simp: Ins2)

(* Multiplicity of an item in bag *)
nonfreeiter mult :: "'a bag \<Rightarrow> 'a \<Rightarrow> nat"
where
  "mult BEmp = (\<lambda> a. 0)"
| "mult (BIns b B) = (\<lambda> a. if a = b then Suc (mult B a) else mult B a)"
by (auto simp: BIns)

(* Flattening operator from bags to finite sets *)
nonfreeiter flat :: "'a bag \<Rightarrow> 'a fset"
where
  "flat BEmp = Emp"
| "flat (BIns a B) = Ins a (flat B)"
by (auto simp: Ins1 Ins2)

lemma mem_flat_mult[simp]: "mem (flat A) a \<longleftrightarrow> mult A a \<noteq> 0"
by (induction rule: bag_induct) auto

(* Embedding of finite sets into bags *)
nonfreeiter embed :: "'a fset \<Rightarrow> 'a bag"
where
  "embed Emp = BEmp"
| "embed (Ins a A) = (if mult (embed A) a = 0 then BIns a (embed A) else embed A)"
by (auto simp: BIns)

lemma mult_embed_mem[simp]: "mult (embed A) a \<noteq> 0 \<longleftrightarrow> mem A a"
by (induction rule: fset_induct) auto

(* Cardinal of finite sets: *)
nonfreeiter card1 :: "'a fset \<Rightarrow> 'a fset * nat"
where
  "card1 Emp = (Emp, 0)"
| "card1 (Ins a A) = (case card1 A of (A,n) \<Rightarrow> (Ins a A, if mem A a then n else Suc n))"
by (auto simp: Ins2)

lemma card1: "card1 A = (A',n) \<Longrightarrow> A = A'"
by (induct arbitrary: A' n rule: fset_induct) (auto split: prod.splits)

definition card :: "'a fset \<Rightarrow> nat" where "card \<equiv> snd o card1"

lemma card_simps[simp]:
  "card Emp = 0"
  "card (Ins a A) = (if mem A a then card A else Suc (card A))"
unfolding card_def using card1 by (auto split: prod.splits)

(* Sum of a numeric function over a finite set: *)
nonfreeiter sum1 :: "'a fset \<Rightarrow> 'a fset \<times> (('a \<Rightarrow> nat) \<Rightarrow> nat)"
where
  "sum1 Emp = (Emp, (\<lambda> f. 0))"
| "sum1 (Ins a A) = (case sum1 A of (A,S) \<Rightarrow> (Ins a A, if mem A a then S else (\<lambda> f. S f  + f a)))"
by (auto simp: Ins2)

lemma sum1: "sum1 A = (A',n) \<Longrightarrow> A = A'"
by (induct arbitrary: A' n rule: fset_induct) (auto split: prod.splits)

definition sum :: "'a fset \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat" where "sum \<equiv> snd o sum1"

lemma sum_simps[simp]:
  "sum Emp f = 0"
  "sum (Ins a A) f = (if mem A a then sum A f else sum A f + f a)"
unfolding sum_def using sum1 by (auto split: prod.splits)

(* Sum of a numeric function over a bag: *)
nonfreeiter bsum :: "'a bag \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat"
where
  "bsum BEmp = (\<lambda> f. 0)"
| "bsum (BIns a B) = (\<lambda> f. bsum B f + f a)"
by auto

(* More generally: Sum of a commutative-monoid-valed function over a bag: *)
nonfreeiter bsum_gen :: "'a bag \<Rightarrow> ('a \<Rightarrow> ('b::comm_monoid_add)) \<Rightarrow> 'b"
where
  "bsum_gen BEmp = (\<lambda> f. 0)"
| "bsum_gen (BIns a B) = (\<lambda> f. bsum_gen B f + f a)"
by (auto simp: algebra_simps)


(* Embedding of finite sets as sets: *)
nonfreeiter asSet :: "'a fset \<Rightarrow> 'a set"
where
  "asSet Emp = {}"
| "asSet (Ins a A) = insert a (asSet A)"
by auto

lemma finite_asSet: "finite (asSet A)"
by (induction rule: fset_induct) auto

lemma finite_imp_asSet: "finite A \<Longrightarrow> (\<exists> F. A = asSet F)"
by (induction rule: finite_induct) (metis asSet.simps)+

(* Alternative description of finite sets, as initial semi-lattice: *)
nonfreedata 'a fsetS = SEmp | SSingl 'a | SUn "'a fsetS" "'a fsetS"
where
  Assoc: "SUn (SUn A1 A2) A3 = SUn A1 (SUn A2 A3)"
| Comm: "SUn A1 A2 = SUn A2 A1"
| Idem: "SUn A A = A"
| Id: "SUn A SEmp = A"


(* Embedding of finite sets as sets: *)
nonfreeiter asSetS :: "'a fsetS \<Rightarrow> 'a set"
where
  "asSetS SEmp = {}"
| "asSetS (SSingl a) = {a}"
| "asSetS (SUn A1 A2) = asSetS A1 \<union> asSetS A2"
by auto

lemma finite_asSetS: "finite (asSetS A)"
by (induction rule: fsetS_induct) auto

lemma insert_asSetsS: "insert a (asSetS S) = asSetS (SUn S (SSingl a))" by auto

lemma finite_imp_asSetS: "finite A \<Longrightarrow> (\<exists> F. A = asSetS F)"
by (induction rule: finite_induct) (metis asSetS.simps insert_asSetsS)+

(* Nonempty finite sets, ACI: *)
nonfreedata 'a fsetN = NSingl 'a | NUn "'a fsetN" "'a fsetN"
where
  AssocN: "NUn (NUn A1 A2) A3 = NUn A1 (NUn A2 A3)"
| CommN: "NUn A1 A2 = NUn A2 A1"
| IdemN: "NUn A A = A"


(* Embedding of finite sets as sets: *)
nonfreeiter asSetN :: "'a fsetN \<Rightarrow> 'a set"
where
  "asSetN (NSingl a) = {a}"
| "asSetN (NUn A1 A2) = asSetN A1 \<union> asSetN A2"
by auto

lemma finite_NE_asSetN: "finite (asSetN A) \<and> asSetN A \<noteq> {}"
by (induction rule: fsetN_induct) auto

lemmas finite_asAetN = finite_NE_asSetN[THEN conjunct1]
lemmas NE_asAetN = finite_NE_asSetN[THEN conjunct2]

lemma insert_asSetsN: "insert a (asSetN S) = asSetN (NUn S (NSingl a))" by auto

lemma finite_imp_asSetN: "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<exists> F. A = asSetN F)"
by (induction rule: finite_induct) (metis asSetN.simps insert_asSetsN)+

(* TODO: In a separate file: infer the desired recursors for native finite sets. *)


end
