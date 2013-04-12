theory Terms_with_Bindings
imports NonFree
uses "input.ML"
begin

type_synonym var = nat type_synonym const = nat

fun neq where "neq x y = (x \<noteq> y)"

nonfreedata lam =
    Ct const | V var | Ap lam lam | Lm var lam
  | Subst lam lam var (* Subst X Y z = X[Y/z] *)
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
  numoccs :: "lam \<Rightarrow> (var \<Rightarrow> nat)"
where
  "numoccs (Ct c) = (\<lambda> z. 0)"
| "numoccs (V x) = (\<lambda> z. if x = z then 1 else 0)"
| "numoccs (Ap X Y)  = (\<lambda> z. numoccs X z + numoccs Y z)"
| "numoccs (Lm x X) = (\<lambda> z. if x = z then 0 else numoccs X z)"
| "numoccs (Subst X Y y) = (\<lambda> z.
     if y = z then numoccs X y * numoccs Y z
     else numoccs X z + numoccs X y * numoccs Y z)"
| "fresh interpretedas (\<lambda> x (occs :: var \<Rightarrow> nat). occs x = 0)"
by (auto simp: algebra_simps)

definition lm :: const where "lm \<equiv> 0::nat"  definition ap :: const where "ap \<equiv> Suc 0"
definition enc_const :: "const \<Rightarrow> const" where "enc_const c = Suc (Suc c)"

(* HOAS encoding of lambda terms in themselves *)
nonfreeiter
  enc :: "lam \<Rightarrow> lam"
where
  "enc (Ct c) = Ct (enc_const c)"
| "enc (V x) = V x"
| "enc (Ap X Y) = Ap (Ap (Ct ap) (enc X)) (enc Y)"
| "enc (Lm x X) = Ap (Ct lm) (Lm x (enc X))"
| "enc (Subst X Y y) = Subst (enc X) (enc Y) y"
| "fresh interpretedas fresh"
by auto

(* Interpretation of terms in semantic domains: *)
typedecl dom
consts CT :: "'const \<Rightarrow> dom"
consts LM :: "(dom \<Rightarrow> dom) \<Rightarrow> dom"
consts AP :: "dom \<Rightarrow> dom \<Rightarrow> dom"

nonfreeiter
  sem :: "lam \<Rightarrow> (var \<Rightarrow> dom) \<Rightarrow> dom"
where
  "sem (Ct c) = (\<lambda> \<rho>. CT c)"
| "sem (V x) = (\<lambda> \<rho>. \<rho> x)"
| "sem (Ap X Y) = (\<lambda> \<rho>. AP (sem X \<rho>) (sem Y \<rho>))"
| "sem (Lm x X) = (\<lambda> \<rho>. LM (\<lambda> d. sem X (\<rho> (x := d))))"
| "sem (Subst X Y y) = (\<lambda> \<rho>. sem X (\<rho> (y := sem Y \<rho>)))"
| "fresh interpretedas (\<lambda> x (K::(var \<Rightarrow> dom) \<Rightarrow> dom). \<forall> \<rho>1 \<rho>2. (\<forall> y. y \<noteq> x \<longrightarrow> \<rho>1 y = \<rho>2 y) \<longrightarrow> K \<rho>1 = K \<rho>2)"
apply (auto intro!: ext arg_cong[of _ _ LM] arg_cong[of _ _ AP] arg_cong2[of _ _ _ _ AP])
apply (metis fun_upd_other fun_upd_twist)
proof- (* todo: clean up proof *)
  fix x' x'a \<rho>1 \<rho>2 d assume "\<forall>y. y \<noteq> x' \<longrightarrow> \<rho>1 y = \<rho>2 y"
  hence "\<rho>1(x' := d) = \<rho>2(x' := d)" by auto
  thus "x'a (\<rho>1(x' := d)) = x'a (\<rho>2(x' := d))" by simp
qed









end