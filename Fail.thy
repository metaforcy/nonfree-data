theory Fail
imports NonFreeInput
begin







(* test for pseudo-iteration *)
 nonfreedata 'a blub = Blub "'a blub" | Bla "'a"
   where "Blub x = Blub x"

 nonfreeiter
   blubElim :: "'a blub \<Rightarrow> unit"
 where
   "blubElim (Blub x) = ()"
 | "blubElim (Bla z) = ()"
 by simp+   




type_synonym var = nat

fun neq where "neq x y = (x \<noteq> y)"

nonfreedata 'c lam =
    Ct 'c | V var | Ap "'c lam" "'c lam" | Lm var "'c lam"
  | Subst "'c lam" "'c lam" var (* Subst X Y z = X[Y/z] *)
where
  Subst_Ct: "Subst (Ct c) X x = Ct c"
| Subst_V1: "Subst (V x) X x = X"
| Subst_V2: "neq x y \<Longrightarrow> Subst (V x) Y y = V x"
| Subst_Ap: "Subst (Ap X Y) Z z = Ap (Subst X Z z) (Subst Y Z z)"
| Subst_Lm: "\<lbrakk>neq x y ; fresh x Y\<rbrakk> \<Longrightarrow> Subst (Lm x X) Y y = Lm x (Subst X Y y)"
| fresh_Ct: "fresh x (Ct c)"
| fresh_V: "neq x y \<Longrightarrow> fresh x (V y)"
| fresh_Ap: "\<lbrakk>fresh x Y ; fresh x Z\<rbrakk> \<Longrightarrow> fresh x (Ap Y Z)"
| fresh_Lm1: "fresh x (Lm x X)"
| fresh_Lm2: "fresh x Y \<Longrightarrow> fresh x (Lm y Y)"
| Lm_Subst:  "\<lbrakk>neq y x ; fresh y X\<rbrakk> \<Longrightarrow> Lm y (Subst X (V y) x) = Lm x X"

declare Subst_Ct[simp] Subst_V1[simp] Subst_V2[simp] Subst_Ap[simp] Subst_Lm[simp]
        fresh_Ct[simp] fresh_V[simp] fresh_Ap[simp] fresh_Lm1[simp] fresh_Lm2[simp]
        Lm_Subst[simp]

(* Count number of free occurrences of a variable in a term: *)
nonfreeiter
  numoccs :: "'c lam \<Rightarrow> (var \<Rightarrow> nat)"
where
  "numoccs (Ct c) = (\<lambda> z. 0)"
| "numoccs (V x) = (\<lambda> z. if x = z then 1 else 0)"
| "numoccs (Ap X Y)  = (\<lambda> z. numoccs X z + numoccs Y z)"
| "numoccs (Lm x X) = (\<lambda> z. if x = z then 0 else numoccs X z)"
| "numoccs (Subst X Y y) = (\<lambda> z.
     if y = z then numoccs X y * numoccs Y z
     else numoccs X z + numoccs X y * numoccs Y z)"
| "(fresh :: nat \<Rightarrow> 'c lam \<Rightarrow> bool) interpretedas (\<lambda> (x :: var) (occs :: var \<Rightarrow> nat). occs x = 0)"
by (auto simp: algebra_simps)







(* parameter conditions instead of parameter functions *)
definition
  plusis :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where "plusis a1 a2 a' = (a' = a1 + a2)"

nonfreedata ssum
   = Left nat | Right nat | Plus "ssum" "ssum"
where
  LeftPlus: "plusis a1 a2 a' \<Longrightarrow> Plus (Left a1) (Left a2) = Left a'"
| RightPlus: "plusis b1 b2 b' \<Longrightarrow> Plus (Right b1) (Right b2) = Right b'"
| Assoc: "Plus (Plus x1 x2) x3 = Plus x1 (Plus x2 x3)"

nonfreeiter
  sum :: "ssum \<Rightarrow> nat"
where
  "sum (Left x) = x"
| "sum (Right y) = y"
| "sum (Plus xs ys) = ((sum xs) + (sum ys))"
by (simp add: plusis_def)+

thm sum.simps





end
