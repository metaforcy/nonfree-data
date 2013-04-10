theory FSets_Alternatives
imports FSets_Bags
begin

(* Alternative descriptions of finite sets and the transport of the
recursors to the type of sets *)

(* As initial semi-lattice with unit (ACIU): *)
nonfreedata 'a fsetS = SEmp | SSingl 'a | SUn "'a fsetS" "'a fsetS"
where
  Assoc: "SUn (SUn A1 A2) A3 = SUn A1 (SUn A2 A3)"
| Comm: "SUn A1 A2 = SUn A2 A1"
| Idem: "SUn A A = A"
| Id: "SUn A SEmp = A"

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

(*  *)

term iter_fsetS
term iter_fset





term

(* Nonempty finite sets, as initial semilattice (ACI): *)
nonfreedata 'a fsetN = NSingl 'a | NUn "'a fsetN" "'a fsetN"
where
  AssocN: "NUn (NUn A1 A2) A3 = NUn A1 (NUn A2 A3)"
| CommN: "NUn A1 A2 = NUn A2 A1"
| IdemN: "NUn A A = A"

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


end
