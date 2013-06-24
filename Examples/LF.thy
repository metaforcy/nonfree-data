(* LF terms and a HOAS representation of the FOL syntax in LF *)
theory LF
imports Prelim
begin

(* LF has three syntactic categories: objects, type families and kinds *)

nonfree_datatype
  ('ct, 'tct) obj =
  Ct 'ct | Var var | Lam "('ct, 'tct) tfam" var "('ct, 'tct) obj" | App "('ct, 'tct) obj" "('ct, 'tct) obj"
  | subst "('ct, 'tct) obj" "('ct, 'tct) obj" var
and
  ('ct, 'tct) tfam =
  Tct 'tct | Tprod "('ct, 'tct) tfam" var "('ct, 'tct) tfam" | Tapp "('ct, 'tct) tfam" "('ct, 'tct) obj"
  | tsubst "('ct, 'tct) tfam" "('ct, 'tct) obj" var
and
  ('ct, 'tct) kind = Type | Kprod "('ct, 'tct) tfam" var "('ct, 'tct) kind"
  | ksubst "('ct, 'tct) kind" "('ct, 'tct) obj" var
where
  subst_Ct: "subst (Ct c) M x = Ct c"
| subst_V1: "subst (Var x) M x = M"
| subst_V2: "neq x y \<Longrightarrow> subst (Var x) N y = Var x"
| subst_App: "subst (App M N) P x = App (subst M P x) (subst N P x)"
| subst_Lam: "\<lbrakk>neq x y ; fresh x N\<rbrakk> \<Longrightarrow> subst (Lam A x M) N y = Lam (tsubst A N y) x (subst M N y)"
| fresh_V: "neq x y \<Longrightarrow> fresh x (Var y)"
| fresh_Ct: "fresh x (Ct c)"
| fresh_App: "\<lbrakk>fresh x M; fresh x N\<rbrakk> \<Longrightarrow> fresh x (App M N)"
| fresh_Lam1: "tfresh x A \<Longrightarrow> fresh x (Lam A x M)"
| fresh_Lam2: "\<lbrakk>tfresh x A; fresh x M\<rbrakk> \<Longrightarrow> fresh x (Lam A y M)"
| Lam_subst:  "\<lbrakk>neq y x ; fresh y M\<rbrakk> \<Longrightarrow> Lam A y (subst M (Var y) x) = Lam A x M"
| fresh_subst: "\<lbrakk>fresh x M; fresh x N\<rbrakk> \<Longrightarrow>  fresh x (subst M N z)"
(*  *)
| tsubst_Tct: "tsubst (Tct a) M x = Tct a"
| tsubst_Tapp: "tsubst (Tapp A N) M x = Tapp (tsubst A M x) (subst N M x)"
| tsubst_Tprod: "\<lbrakk>neq x y ; fresh x N\<rbrakk> \<Longrightarrow> tsubst (Tprod A x B) N y = Tprod (tsubst A N y) x (tsubst B N y)"
| tfresh_Tct: "tfresh x (Tct a)"
| tfresh_Tapp: "\<lbrakk>tfresh x A; fresh x N\<rbrakk> \<Longrightarrow> tfresh x (Tapp A N)"
| tfresh_Tprod1: "tfresh x A \<Longrightarrow> tfresh x (Tprod A x B)"
| tfresh_Tprod2: "\<lbrakk>tfresh x A; tfresh x B\<rbrakk> \<Longrightarrow> tfresh x (Tprod A y B)"
| Tprod_tsubst:  "\<lbrakk>neq y x ; tfresh y B\<rbrakk> \<Longrightarrow> Tprod A y (tsubst B (Var y) x) = Tprod A x B"
| tfresh_tsubst: "\<lbrakk>tfresh x A; fresh x N\<rbrakk> \<Longrightarrow> tfresh x (tsubst A N z)"
(*  *)
| ksubst_Type: "ksubst Type M x = Type"
| ksubst_Kprod: "\<lbrakk>neq x y ; fresh x N\<rbrakk> \<Longrightarrow> ksubst (Kprod A x K) N y = Kprod (tsubst A N y) x (ksubst K N y)"
| kfresh_Type: "kfresh x Type"
| kfresh_Kprod1: "tfresh x A \<Longrightarrow> kfresh x (Kprod A x K)"
| kfresh_Kprod2: "\<lbrakk>tfresh x A; kfresh x K\<rbrakk> \<Longrightarrow> kfresh x (Kprod A y K)"
| kfresh_ksubst: "\<lbrakk>kfresh x K; fresh x N\<rbrakk> \<Longrightarrow> kfresh x (ksubst K N z)"
| Kprod_ksubst:  "\<lbrakk>neq y x ; kfresh y K\<rbrakk> \<Longrightarrow> Kprod A y (ksubst K (Var y) x) = Kprod A x K"

declare subst_Ct[simp] subst_V1[simp] subst_V2[simp] subst_App[simp] subst_Lam[simp]
fresh_Ct[simp] fresh_V[simp] fresh_App[simp] fresh_Lam1[simp] fresh_Lam2[simp]
Lam_subst[simp] fresh_subst[simp]
declare tsubst_Tct[simp] tsubst_Tapp[simp] tsubst_Tprod[simp]
tfresh_Tct[simp] tfresh_Tapp[simp] tfresh_Tprod1[simp] tfresh_Tprod2[simp]
Tprod_tsubst[simp] tfresh_tsubst[simp]

declare ksubst_Type[simp] ksubst_Kprod[simp]
kfresh_Type[simp] kfresh_Kprod1[simp] kfresh_Kprod2[simp]
Kprod_ksubst[simp] kfresh_ksubst[simp]

(* FOL terms: *)
datatype fterm = Fvar var | Sc fterm | Plus fterm fterm | Mult fterm fterm

fun ftsubst where
  "ftsubst (Fvar x) t y = (if x = y then t else Fvar x)"
| "ftsubst (Sc s) t y = Sc (ftsubst s t y)"
| "ftsubst (Plus s1 s2) t y = Plus (ftsubst s1 t y) (ftsubst s2 t y)"
| "ftsubst (Mult s1 s2) t y = Mult (ftsubst s1 t y) (ftsubst s2 t y)"

fun ftfresh where
  "ftfresh z (Fvar x) \<longleftrightarrow> x \<noteq> z"
| "ftfresh z (Sc s) \<longleftrightarrow> ftfresh z s"
| "ftfresh z (Plus s1 s2) \<longleftrightarrow> ftfresh z s1 \<and> ftfresh z s2"
| "ftfresh z (Mult s1 s2) \<longleftrightarrow> ftfresh z s1 \<and> ftfresh z s2"

fun is_ftsubst where "is_ftsubst s t y s' = (ftsubst s t y = s')"
fun is_Fvar where "is_Fvar t y = (t = Fvar y)"
fun ftfreshFor where "ftfreshFor x y t = (neq x y \<and> ftfresh x t)"
fun isFreshFvar where "isFreshFvar t y x = (is_Fvar t y \<and> neq y x)"

(* FOL formulas: *)
nonfree_datatype
  fmla = Eq fterm fterm | Leq fterm fterm | Neg fmla | Conj fmla fmla | All var fmla
         | fsubst fmla fterm var
where
  fsubst_Eq: "\<lbrakk>is_ftsubst s1 t x s1'; is_ftsubst s2 t x s2'\<rbrakk>  \<Longrightarrow> fsubst (Eq s1 s2) t x = Eq s1' s2'"
| fsubst_Leq: "\<lbrakk>is_ftsubst s1 t x s1'; is_ftsubst s2 t x s2'\<rbrakk>  \<Longrightarrow> fsubst (Leq s1 s2) t x = Leq s1' s2'"
| subst_Neg: "fsubst (Neg f) t x = Neg (fsubst f t x)"
| fsubst_Conj: "fsubst (Conj f1 f2) t x = Conj (fsubst f1 t x) (fsubst f2 t x)"
| fsubst_All: "ftfreshFor x y t \<Longrightarrow> fsubst (All x f) t y = All x (fsubst f t y)"
| ffresh_Eq: "\<lbrakk>ftfresh z s1; ftfresh z s2\<rbrakk> \<Longrightarrow> ffresh z (Eq s1 s2)"
| ffresh_Leq: "\<lbrakk>ftfresh z s1; ftfresh z s2\<rbrakk> \<Longrightarrow> ffresh z (Leq s1 s2)"
| ffresh_Neg: "ffresh x f \<Longrightarrow> ffresh x (Neg f)"
| ffresh_Conj: "\<lbrakk>ffresh x f1; ffresh x f2\<rbrakk> \<Longrightarrow> ffresh x (Conj f1 f2)"
| ffresh_All1: "ffresh x (All x f)"
| ffresh_All2: "ffresh x f \<Longrightarrow> ffresh x (All y f)"
| All_fsubst:  "\<lbrakk>isFreshFvar t y x  ; ffresh y f\<rbrakk> \<Longrightarrow> All y (fsubst f t x) = All x f"
| ffresh_fsubst: "\<lbrakk>ffresh x f; ftfresh x t\<rbrakk> \<Longrightarrow>  ffresh x (fsubst f t z)"


(* Representation: *)
datatype tct = tm | fm
datatype ct = sc | plus | times | eq | leq | neg | conj | all

fun tenc :: "fterm \<Rightarrow> (ct,tct) obj"
where
  "tenc (Fvar x) = Var x"
| "tenc (Sc t) = App (Ct sc) (tenc t)"
| "tenc (Plus s t) = App (App (Ct plus) (tenc s)) (tenc t)"
| "tenc (Mult s t) = App (App (Ct plus) (tenc s)) (tenc t)"

lemma tenc_ftsubst[simp]: "tenc (ftsubst s t y) = subst (tenc s) (tenc t) y"
by (induction s) auto

lemma tenc_ftfresh[simp]: "ftfresh x t \<Longrightarrow> fresh x (tenc t)"
by (induction t) auto

(* Substitution-compositional interpetation of FOL syntax in LF: *)
nonfree_primrec
  fenc :: "fmla \<Rightarrow> (ct,tct) obj"
where
  "fenc (Eq t1 t2) = App (App (Ct eq) (tenc t1)) (tenc t2)"
| "fenc (Leq t1 t2) = App (App (Ct leq) (tenc t1)) (tenc t2)"
| "fenc (Neg f) = App (Ct neg) (fenc f)"
| "fenc (Conj f1 f2) = App (App (Ct conj) (fenc f1)) (fenc f2)"
| "fenc (All x f) = App (Ct all) (Lam (Tct tm) x (fenc f))"
| "fenc (fsubst f t y) = subst (fenc f) (tenc t) y"
| "ffresh x f ==> fresh x (fenc f)"
by auto


(* TODO: Define kinds separately, since objects and type families do not depend on them. *)


end
