(* The encoding of LF in Curry-style simply typed lambda calculus *)
theory LF_to_STLC
imports "../Examples/LF" "../Examples/Lambda"
begin

(* Simple types: *)
datatype 'tct stype = Tp 'tct | Omega | Arr "'tct stype" "'tct stype"


nonfree_primrec
  otau :: "('ct,'tct) obj \<Rightarrow> unit"
and
  ftau :: "('ct,'tct) tfam \<Rightarrow> 'tct stype"
and
  ktau :: "('ct,'tct) kind \<Rightarrow> 'tct stype"
where
  "otau (LF.Ct c) = ()"
| "otau (LF.Var x) = ()"
| "otau (LF.Lam A x M) = ()"
| "otau (LF.App M N) = ()"
| "otau (LF.subst M N x) = ()"
(*  *)
| "ftau (LF.Tct a) = Tp a"
| "ftau (LF.Tprod A x B) = Arr (ftau A) (ftau B)"
| "ftau (LF.Tapp A M) = ftau A"
| "ftau (LF.tsubst A N x) = ftau A"
(*  *)
| "ktau Type = Omega"
| "ktau (LF.Kprod A x K) = Arr (ftau A) (ktau K)"
| "ktau (LF.ksubst K N x) = ktau K"
(*  *)
| "(LF.fresh :: var \<Rightarrow> ('ct,'tct) obj \<Rightarrow> bool)
   interpretedas
   (\<lambda> (x::var) (u::unit). True)"
| "(LF.tfresh :: var \<Rightarrow> ('ct,'tct) tfam \<Rightarrow> bool)
   interpretedas
   (\<lambda> (x::var) (\<sigma>::'tct stype). True)"
| "(LF.kfresh :: var \<Rightarrow> ('ct,'tct) kind \<Rightarrow> bool)
   interpretedas
   (\<lambda> (x::var) (\<sigma>::'tct stype). True)"
by auto

datatype ('ct,'tct) const = Pi "'tct stype" | LFconst 'ct | LFtconst 'tct


lemma [simp]:
assumes "x' \<noteq> x" and "fresh x' X" and
y: "y = pickFresh [subst X (Var x') x] []" and z: "z = pickFresh [X] []"
shows "Lam y (Lam x X) = Lam z (Lam x X)"
by sorry2
(* Proof: By "Lam y" and "Lam z" being dummy abstractions.  That "Lam y" is so
follows from a property about fresh and subst.  *)

lemma [simp]:
assumes "x' \<noteq> x" and "fresh x' Y" and
y: "y = pickFresh [X] []" and z: "z = pickFresh [subst X Y x] []"
shows "subst (Lam y (Lam x' X)) Y x = Lam z (Lam x' (subst X Y x))"
by sorry2
(* Proof: Since above "Lam y" and "Lam z" are dummy abstractions, they can be replaced by some
totally fresh u.  Now,  "subst (Lam u (Lam x' X)) Y x = Lam u (Lam x' (subst X Y x))"
follows by appliying subst_lam twice.  *)


(* The "modulus" operator: Since the package does not support full recursion,
  I need to go through an auxiliary operator returning pairs (just like I did for the finite-set cardinal).
  The only culprit is "ftau A" from the "LF.Tprod A x B" case. *)
nonfree_primrec
  omod' :: "('ct,'tct) obj \<Rightarrow> ('ct,'tct) obj \<times> (var, ('ct,'tct) const) trm"
and
  fmod' :: "('ct,'tct) tfam \<Rightarrow> ('ct,'tct) tfam \<times> (var, ('ct,'tct) const) trm"
and
  kmod' :: "('ct,'tct) kind \<Rightarrow> unit"
where
  "omod' (LF.Ct c) = (LF.Ct c, Ct (LFconst c))"
| "omod' (LF.Var x) = (LF.Var x, Var x)"
| "omod' (LF.Lam A x M) =
   (
    case (fmod' A, omod' M) of ((A,X), (M,Y)) \<Rightarrow>
     (LF.Lam A x M, App (Lam (pickFresh [Y] []) (Lam x (Y))) X)
   )"
| "omod' (LF.App M N) =
   (case (omod' M, omod' N) of ((M,X), (N,Y)) \<Rightarrow>
     (LF.App M N, App X Y)
   )"
| "omod' (LF.subst M N x) =
   (case (omod' M, omod' N) of ((M,X), (N,Y)) \<Rightarrow>
     (LF.subst M N x, subst X Y x)
   )"
(*  *)
| "fmod' (LF.Tct a) = (LF.Tct a, Ct (LFtconst a))"
| "fmod' (LF.Tprod A x B) =
   (
    case (fmod' A, fmod' B) of ((A,X), (B,Y)) \<Rightarrow>
     (LF.Tprod A x B, App (App (Ct (Pi (ftau A))) X) (Lam x Y))
   )"
| "fmod' (LF.Tapp A M) =
   (
    case (fmod' A, omod' M) of ((A,X), (M,Y)) \<Rightarrow>
     (LF.Tapp A M, App X Y)
   )"
| "fmod' (LF.tsubst A N x) =
  (
   case (fmod' A, omod' N) of ((A,X), (N,Y)) \<Rightarrow>
    (LF.tsubst A N x, subst X Y x)
  )"
(*  *)
| "kmod' Type = ()"
| "kmod' (LF.Kprod A x K) = ()"
| "kmod' (LF.ksubst K N x) = ()"
(*  *)
| "(LF.fresh :: var \<Rightarrow> ('ct,'tct) obj \<Rightarrow> bool)
   interpretedas
   ((\<lambda> x (M,X). LF.fresh x M \<and> fresh x X) :: var \<Rightarrow> ('ct,'tct) obj \<times> (var, ('ct,'tct) const) trm \<Rightarrow> bool)"
| "(LF.tfresh :: var \<Rightarrow> ('ct,'tct) tfam \<Rightarrow> bool)
   interpretedas
   ((\<lambda> x (A,X). LF.tfresh x A \<and> fresh x X) :: var \<Rightarrow> ('ct,'tct) tfam \<times> (var, ('ct,'tct) const) trm \<Rightarrow> bool)"
| "(LF.kfresh :: var \<Rightarrow> ('ct,'tct) kind \<Rightarrow> bool)
   interpretedas
   (\<lambda> (x::var) (u::unit). True)"
by auto

lemma fst_omod'[simp]: "fst (omod' M) = M"
apply(induction rule: obj_induct[of "\<lambda> A. fst (fmod' A) = A" "\<lambda> M. fst (omod' M) = M"])
by (auto split: prod.splits)

lemma omod'_Pair: "omod' M = (M',X) \<Longrightarrow> M = M'"
using fst_omod' by (metis fst_conv)

lemma fst_fmod'[simp]: "fst (fmod' A) = A"
apply(induction rule: tfam_induct[of "\<lambda> A. fst (fmod' A) = A" "\<lambda> M. fst (omod' M) = M"]) apply auto
by (auto split: prod.splits dest: omod'_Pair)

lemma fmod'_Pair: "fmod' A = (A',X) \<Longrightarrow> A = A'"
using fst_fmod' by (metis fst_conv)

definition "omod \<equiv> snd o omod'"
definition "fmod \<equiv> snd o fmod'"

lemma mod_simps[simp]:
"omod (LF.Ct c) = Ct (LFconst c)"
"omod (LF.Var x) = Var x"
"omod (LF.Lam A x M) = App (Lam (pickFresh [omod M] [])
                           (Lam x (omod M))) (fmod A)"
"omod (LF.App M N) = App (omod M) (omod N)"
(*  *)
"fmod (LF.Tct a) = Ct (LFtconst a)"
"fmod (LF.Tprod A x B) = App (App (Ct (Pi (ftau A))) (fmod A)) (Lam x (fmod B))"
"fmod (LF.Tapp A M) = App (fmod A) (omod M)"
unfolding omod_def fmod_def by (auto split: prod.split dest: fmod'_Pair)

lemma mod_subst[simp]:
"omod (LF.subst M N x) = subst (omod M) (omod N) x"
"fmod (LF.tsubst A N x) = subst (fmod A) (omod N) x"
unfolding omod_def fmod_def by (auto split: prod.splits)

lemma mod_fresh[simp]:
"LF.fresh x M \<Longrightarrow> fresh x (omod M)"
"LF.tfresh x A \<Longrightarrow> fresh x (fmod A)"
unfolding omod_def fmod_def apply (auto split: prod.splits)
by (smt kmod'.simps split_conv surjective_pairing)+



end
