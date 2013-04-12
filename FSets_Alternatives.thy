theory FSets_Alternatives
imports FSets_Bags
begin

(* Alternative descriptions of finite sets and the transport of the
recursors to the type of sets *)


section{* As initial semi-lattice with unit (ACIU): *}

nonfreedata 'a fsetS = SEmp | SSingl 'a | SUni "'a fsetS" "'a fsetS"
where
  Assoc: "SUni (SUni A1 A2) A3 = SUni A1 (SUni A2 A3)"
| Comm: "SUni A1 A2 = SUni A2 A1"
| Idem: "SUni A A = A"
| Id: "SUni SEmp A = A"

declare Idem[simp]  declare Id[simp]

lemma SUni_SEmp[simp]: "SUni A SEmp = A"
by (metis Comm Id)

nonfreeiter asFset :: "'a fsetS \<Rightarrow> 'a fset"
where
  "asFset SEmp = Emp"
| "asFset (SSingl a) = Singl a"
| "asFset (SUni A1 A2) = Uni (asFset A1) (asFset A2)"
apply auto using Uni_assoc Uni_com by metis+

nonfreeiter asFsetS :: "'a fset \<Rightarrow> 'a fsetS"
where
  "asFsetS Emp = SEmp"
| "asFsetS (Ins a A) = SUni (SSingl a) (asFsetS A)"
by (metis Assoc Idem Comm)+

lemma asFset_asFsetS[simp]: "asFset (asFsetS A) = A"
by (induct A) (auto simp: Singl_def)

lemma asFSetsS_Uni[simp]: "asFsetS (Uni A B) = SUni (asFsetS A) (asFsetS B)"
apply(induction A) apply auto using Assoc
apply metis done

lemma asFsetS_asFset[simp]: "asFsetS (asFset A) = A"
apply(induction A) by (auto simp: Singl_def)

(* TODO:
1) Fix associativity of Uni: the other way around.
2) Transport to finite sets the lattice recursor.
3) Do the same for nonempty finite sets below, without going through asSetN *)

(* Nonempty finite sets, as initial semilattice (ACI): *)
nonfreedata 'a fsetN = NSingl 'a | NUni "'a fsetN" "'a fsetN"
where
  AssocN: "NUni (NUni A1 A2) A3 = NUni A1 (NUni A2 A3)"
| CommN: "NUni A1 A2 = NUni A2 A1"
| IdemN: "NUni A A = A"

(*
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
*)


end
