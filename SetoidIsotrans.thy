theory SetoidIsotrans
imports "../metarec/HOLMetaRec"
begin


definition funS:: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set"
where 
"funS A B \<equiv> {f.  \<forall> x \<in> A.  f x \<in> B x}"

abbreviation
  funSS :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>" 60)
where
  "funSS A B \<equiv> funS A (\<lambda> x. B)"


 
record 'a setoid =
  carOf :: "'a set"
  eqOf :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

(* NB: no restriction R, i.e.  R x y =/\<Rightarrow> x \<in> A & y \<in> A  in general *)
definition
  equiv_rel :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "equiv_rel A R \<equiv> (\<forall> x\<in>A. R x x) &
              (\<forall> x\<in>A. \<forall> y \<in> A. R x y \<longrightarrow> R y x) \<and>
              (\<forall> x\<in>A. \<forall> y \<in> A. \<forall> z \<in> A. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

lemma equiv_rel_refl:
assumes "equiv_rel A R" and "x \<in> A"
shows "R x x"
using assms unfolding equiv_rel_def by auto

lemma equiv_rel_sym:
assumes "equiv_rel A R" and "x \<in> A" and "y \<in> A" and "R x y"
shows "R y x"
using assms unfolding equiv_rel_def by blast

lemma equiv_rel_trans:
assumes "equiv_rel A R" and "x \<in> A" and "y \<in> A" and "z \<in> A" 
and "R x y" and "R y z"
shows "R x z"
using assms unfolding equiv_rel_def by blast

definition
  [MRjud 1 0]: "setoid AA \<equiv> equiv_rel (carOf AA) (eqOf AA)"

lemma setoid_refl:
assumes "setoid AA" and "x \<in> carOf AA"
shows "eqOf AA x x"
using assms equiv_rel_refl unfolding setoid_def by metis

lemma setoid_sym:
assumes "setoid AA" and "x \<in> carOf AA" and "y \<in> carOf AA" and "eqOf AA x y"
shows "eqOf AA y x"
using assms equiv_rel_sym unfolding setoid_def by metis

lemma setoid_trans:
assumes "setoid AA" and "x \<in> carOf AA" and "y \<in> carOf AA" and "z \<in> carOf AA" 
and "eqOf AA x y" and "eqOf AA y z"
shows "eqOf AA x z"
using assms equiv_rel_trans[of "carOf AA" "eqOf AA"] unfolding setoid_def by metis

(* Sets as setoids: *)
definition
  sset :: "'a set \<Rightarrow> 'a setoid" where
  "sset A = (| carOf = A, eqOf = (op =) |)"

lemma carOf_sset[simp]: "carOf (sset A) = A"
and eqOf_sset[simp]: "eqOf (sset A) = (op =)"
unfolding sset_def by auto

abbreviation "UNIV_s == sset UNIV"

lemma carOf_UNIV_s[simp]: "carOf UNIV_s = UNIV" by (simp)
lemma eqOf_UNIV_s[simp]: "eqOf UNIV_s = (op =)" by (simp)

(* Setoid function space *)
definition
  sfun (infixr "~>" 60) where
  "sfun AA BB = { f \<in> carOf AA \<rightarrow> carOf BB .
     \<forall> x \<in> (carOf AA). \<forall> x2 \<in> (carOf AA).
       eqOf AA x x2 \<longrightarrow> eqOf BB (f x) (f x2) }"

definition sfun_eq where
"sfun_eq AA BB f g \<equiv> \<forall> a\<in>carOf AA. eqOf BB (f a) (g a)"

definition
  fun_setoid :: "'a setoid \<Rightarrow> 'b setoid \<Rightarrow> ('a \<Rightarrow> 'b) setoid" (infixr "~s~>" 60) where
  "fun_setoid AA BB \<equiv> \<lparr> carOf = sfun AA BB,  eqOf = sfun_eq AA BB \<rparr>"

lemma carOf_fun_setoid[simp]:
"carOf (fun_setoid AA BB) = sfun AA BB"
unfolding fun_setoid_def by auto

lemma eqOf_fun_setoid[simp]:
"eqOf (fun_setoid AA BB) = sfun_eq AA BB"
unfolding fun_setoid_def by auto

lemmas fun_setoid_simps = carOf_fun_setoid eqOf_fun_setoid

definition
  iso_s :: "'a setoid \<Rightarrow> 'b setoid \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "~=~>" 60) where
  "iso_s AA BB \<equiv> 
   {f. setoid AA \<and> setoid BB \<and>
       f \<in> AA ~> BB \<and>
       (\<forall> a1\<in>carOf AA. \<forall> a2\<in>carOf AA. eqOf AA a1 a2 \<longleftrightarrow> eqOf BB (f a1) (f a2)) \<and>
       (\<forall> b\<in>carOf BB. \<exists> a\<in>carOf AA. eqOf BB (f a) b)}" 

definition "s_inv_pred AA BB f b a \<equiv> a \<in> carOf AA \<and> eqOf BB (f a) b"
definition "s_inv AA BB f b \<equiv> SOME a. s_inv_pred AA BB f b a"

(*  
definition
   s_inv :: "'a setoid \<Rightarrow> 'b setoid \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "s_inv AA BB f \<equiv> (\<lambda> b. SOME a. a \<in> carOf AA \<and> eqOf BB (f a) b)"
*)

definition
  splice:: "('a \<Rightarrow> 'a2) \<Rightarrow> 'a setoid \<Rightarrow> 'a2 setoid \<Rightarrow> ('b \<Rightarrow> 'b2) \<Rightarrow> 'b setoid \<Rightarrow> 'b2 setoid 
     \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a2 \<Rightarrow> 'b2)" ("_ : _ -> _   ##>>   _ : _ -> _") where
  "splice f AA AA' g BB BB' = (\<lambda> h. g o h o s_inv AA AA' f)"


datatype isomark = isomark nat

definition
  isomapto_via :: "'a => isomark \<Rightarrow> 'a setoid \<Rightarrow> 'b \<Rightarrow> 'b setoid \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isomapto_via t phi AA t' AA' f \<equiv> (
     t \<in> carOf AA  \<and>  t' \<in> carOf AA'  \<and>
     setoid AA  \<and>  setoid AA'  \<and>
     f \<in> AA ~=~> AA'  \<and>
     eqOf AA' (f t) t' )"

abbreviation
  isomapto_via_abbrev     ("_: _ : _ isomapto _ : _ via _") where
  "isomapto_via_abbrev phi t AA t' AA' f == isomapto_via t phi AA t' AA' f"


lemma isomapto_carOf1:
assumes "phi: t : AA isomapto t' : AA' via f"
shows "t \<in> carOf AA"
using assms unfolding isomapto_via_def by auto

lemma isomapto_carOf2:
assumes "phi: t : AA isomapto t' : AA' via f"
shows "t' \<in> carOf AA'"
using assms unfolding isomapto_via_def by auto

lemma isomapto_iso_s:
assumes "phi: t : AA isomapto t' : AA' via f"
shows "f \<in> AA ~=~> AA'"
using assms unfolding isomapto_via_def by auto

lemma isomapto_eqOf:
assumes "phi: t : AA isomapto t' : AA' via f"
shows "eqOf AA' (f t) t'"
using assms unfolding isomapto_via_def by auto

definition
  setoid_lam :: "'a setoid \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where  "setoid_lam AA == (% f. f)"
definition
  setoid_all :: "'a setoid \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "setoid_all AA == (% P. \<forall> x\<in>carOf AA. P x)"

syntax
  "_slam" :: "[pttrn, 'a setoid, 'b] \<Rightarrow> ('a \<Rightarrow> 'b)"   ("(3slam _\<in>_./ _)" 10)
  "_S\<forall>" :: "[pttrn, 'a setoid, bool] \<Rightarrow> bool"   ("(3S\<forall> _\<in>_./ _)" 10)
  "_SALL" :: "[pttrn, 'a setoid, bool] \<Rightarrow> bool"   ("(3SALL _:_./ _)" 10)

translations
  "slam x\<in>AA. t" == "CONST setoid_lam AA (\<lambda> x. t)"
  "S\<forall> x\<in>AA. P" == "CONST setoid_all AA (\<lambda> x. P)"
  "SALL x:AA. P" == "CONST setoid_all AA (\<lambda> x. P)"


lemma SALL_on_sset: "(SALL x : sset A. P x) = (ALL x : A. P x)"
  unfolding setoid_all_def by simp

lemma funSI[intro!]: 
"\<forall> x \<in> A. f x \<in> B x \<Longrightarrow> f \<in> funS A B"
unfolding funS_def by simp

lemma srefl: "setoid AA \<Longrightarrow> x \<in> carOf AA \<Longrightarrow> eqOf AA x x"
  unfolding setoid_def equiv_rel_def by auto

lemma ssym: "setoid AA \<Longrightarrow> x \<in> carOf AA \<Longrightarrow> y \<in> carOf AA \<Longrightarrow>
    eqOf AA x y \<Longrightarrow> eqOf AA y x"
  unfolding setoid_def equiv_rel_def 
  apply (erule conjE)+ by fast

lemma strans: "setoid AA \<Longrightarrow> x \<in> carOf AA \<Longrightarrow> y \<in> carOf AA \<Longrightarrow> z \<in> carOf AA \<Longrightarrow>
   eqOf AA x y \<Longrightarrow> eqOf AA y z \<Longrightarrow> eqOf AA x z"
  unfolding setoid_def equiv_rel_def
  by fast


lemma set_setoid[MR,intro,simp]: "setoid (sset A)"
unfolding setoid_def sset_def equiv_rel_def
by simp

lemma UNIV_setoid[MR,intro,simp]: "setoid UNIV_s"
by (simp add: set_setoid)  

lemma elem_UNIV_sI[intro!]: "x : carOf UNIV_s" by (simp)
lemma eq_UNIV_sI[intro]: "x = x2 ==> eqOf UNIV_s x x2" by (simp)



lemma sfun_spaciI[intro!]:  
"\<lbrakk>\<And> x. x \<in> carOf AA \<Longrightarrow> f x \<in> carOf BB; 
  \<And> x x2. \<lbrakk>x \<in> carOf AA; x2 \<in> carOf AA; eqOf AA x x2\<rbrakk> \<Longrightarrow> eqOf BB (f x) (f x2)\<rbrakk> 
 \<Longrightarrow> f \<in> AA ~> BB"
  unfolding sfun_def
  by (simp add: funS_def)

lemma sfun_elim[elim!]: 
assumes "f: AA ~> BB" and 
"\<lbrakk>\<And> x. x \<in> carOf AA \<Longrightarrow> f x \<in> carOf BB; 
  \<And> x x2. \<lbrakk>x \<in> carOf AA; x2 \<in> carOf AA; eqOf AA x x2\<rbrakk> \<Longrightarrow> eqOf BB (f x) (f x2)\<rbrakk> 
 \<Longrightarrow> P"
shows P
  using assms unfolding sfun_def funS_def
  by simp

lemma sfunDeq: "f : AA ~> BB ==> x : carOf AA ==> x2 : carOf AA ==> eqOf AA x x2 ==> eqOf BB (f x) (f x2)"
  by auto

(* TODO: [simp] *)
lemma sfun_ty: "f \<in> AA ~> BB \<Longrightarrow> x \<in> carOf AA \<Longrightarrow> f x \<in> carOf BB"
  unfolding sfun_def funS_def by simp

lemma sfun_eq: "f \<in> AA ~> BB \<Longrightarrow> x \<in> carOf AA \<Longrightarrow> x2 \<in> carOf AA \<Longrightarrow>
   eqOf AA x x2 \<Longrightarrow> eqOf BB (f x) (f x2)"
  unfolding sfun_def by simp 

lemma sfun_eqI[intro!]: " (!! a. a : carOf AA ==> eqOf BB (f a) (g a)) ==> sfun_eq AA BB f g "
  unfolding sfun_eq_def
  by auto

lemma id_sfun[simp, intro]: "id \<in> AA ~> AA" by auto

lemma comp_sfun[simp]:
assumes "f \<in> AA ~> BB" and "g \<in> BB ~> CC"
shows "g o f \<in> AA ~> CC"
apply default by (metis assms o_apply sfun_elim)+ 

lemma sset_funSS[simp]: "sset A ~> sset B = (A \<rightarrow> B)"
  unfolding sfun_def sset_def
  by simp

lemma sfun_UNIV_s[simp]: "UNIV_s ~> UNIV_s = UNIV"
  unfolding sfun_def sset_def funS_def
  by simp

lemma fun_setoid_UNIV_s[simp]: "UNIV_s ~s~> UNIV_s = UNIV_s"
  unfolding sfun_def sset_def fun_setoid_def
  apply (simp add: funS_def sfun_eq_def[abs_def])
  apply (rule ext)+
  by (metis ext)

lemma id_in_sfun[simp,intro]: "id : AA ~> AA" by auto


lemma elem_setdom_funsetoid: assumes setoid: "setoid BB" shows "  (!! x. x : A ==> f x : carOf BB)
  ==>  f : carOf (sset A ~s~> BB)  "
  unfolding fun_setoid_def sset_def sfun_def
  apply (simp add: sfun_eq_def funS_def)
  apply rule
  by (simp add: setoid_refl[OF setoid])

lemma " f : A \<rightarrow> B ==> f : carOf (sset A ~s~> sset B) "
  unfolding fun_setoid_def sset_def sfun_def
  by (simp add: sfun_eq_def)

lemma "f : A  \<rightarrow> B  \<rightarrow> C ==> f : carOf (sset A ~s~> sset B ~s~> sset C)"
  unfolding fun_setoid_def sset_def sfun_def
  by (simp add: sfun_eq_def)



lemma sfun_eqD: "sfun_eq AA BB f g \<Longrightarrow>
  a \<in> carOf AA \<Longrightarrow> eqOf BB (f a) (g a)"
  unfolding sfun_eq_def by auto

lemma sfun_eqE[elim!]: "sfun_eq AA BB f g \<Longrightarrow>
  ((\<And> a. a \<in> carOf AA \<Longrightarrow> eqOf BB (f a) (g a)) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding sfun_eq_def by auto

lemma fun_setoid_carOf: "f \<in> carOf (AA ~s~> BB) \<Longrightarrow> f \<in> AA ~> BB"
  unfolding fun_setoid_def
  by simp

(* [simp]? *)
lemma fun_setoid_eqOf_eq: "eqOf (AA ~s~> BB) == sfun_eq AA BB"
  by (simp add: fun_setoid_def)
lemma fun_setoid_carOf_eq: "carOf (AA ~s~> BB) == (AA ~> BB)"
  by (simp add: fun_setoid_def)

lemma fun_setoid[MR, simp]: assumes AA_s: "setoid AA" and  BB_s: "setoid BB"
   shows "setoid (AA ~s~> BB)"
unfolding setoid_def equiv_rel_def
apply (intro conjI)
proof -
  show "\<forall> x\<in>carOf (AA ~s~> BB). eqOf (AA ~s~> BB) x x"
    apply(simp add: fun_setoid_def sfun_eq_def)
    by(blast intro: srefl[OF BB_s])
  show "\<forall> x\<in>carOf (AA ~s~> BB).
       \<forall> y\<in>carOf (AA ~s~> BB).
          eqOf (AA ~s~> BB) x y \<longrightarrow> eqOf (AA ~s~> BB) y x"
    apply(simp add: fun_setoid_def sfun_eq_def)
    by (blast intro: ssym[OF BB_s])
  show "\<forall> x\<in>carOf (AA ~s~> BB).
       \<forall> y\<in>carOf (AA ~s~> BB).
          \<forall> z\<in>carOf (AA ~s~> BB).
             eqOf (AA ~s~> BB) x y \<longrightarrow>
             eqOf (AA ~s~> BB) y z \<longrightarrow> eqOf (AA ~s~> BB) x z"
    apply(simp add: fun_setoid_def sfun_eq_def)
    by (blast intro: strans[OF BB_s])
qed


lemma sfun_eq_combr: assumes f_ty: "f \<in> AA ~> BB" and f2_ty: "f2 : AA ~> BB"
    and g_ty: "g : BB ~> CC"
    shows "sfun_eq AA BB f f2 \<Longrightarrow> sfun_eq AA CC (g o f) (g o f2)"
  unfolding sfun_eq_def apply simp apply rule
  apply (rule sfun_eq[OF g_ty])
  apply (rule sfun_ty[OF f_ty], assumption)
  apply (rule sfun_ty[OF f2_ty], assumption) by auto

lemma sfun_eq_combl: assumes g_ty: "g : BB ~> CC" and g2_ty: "g2 : AA ~> BB"
    and f_ty: "f \<in> AA ~> BB" and eq: "sfun_eq BB CC g g2"
    shows "sfun_eq AA CC (g o f) (g2 o f)"
  unfolding sfun_eq_def apply simp apply rule
  apply (rule sfun_eqD[OF eq])
  by (rule sfun_ty[OF f_ty])

lemma sfun_eq_app: 
assumes setoid: "setoid BB" and fty:"f \<in> AA ~> BB" and f2ty: "f2 : AA ~> BB"
  and aty: "a : carOf AA" and a2ty: "a2 : carOf AA"
  and feq: "sfun_eq AA BB f f2" and eq: "eqOf AA a a2" 
shows "eqOf BB (f a) (f2 a2)"
proof -
  have "eqOf BB (f a) (f2 a)"
   by (rule sfun_eqD[OF feq aty])
  moreover have "eqOf BB ... (f2 a2)"
   by (rule sfun_eq[OF f2ty aty a2ty eq])
  ultimately show "eqOf BB (f a) (f2 a2)"
   by (rule strans[OF setoid sfun_ty[OF fty aty] 
       sfun_ty[OF f2ty aty] sfun_ty[OF f2ty a2ty]])
qed

lemma slam_eq :
assumes "setoid AA"
and "\<And> x. \<lbrakk>x \<in> carOf AA;  eqOf AA x x\<rbrakk> \<Longrightarrow> eqOf BB (t x) (t2 x)"
shows "eqOf (AA ~s~> BB) (slam x\<in>AA. t x) (slam x\<in>AA. t2 x)"
  using assms unfolding fun_setoid_def apply (simp add: sfun_eq_def setoid_lam_def)
  by (blast intro: srefl)









(* input as a pair allows decomposition of non-patterns in primary object position
   synthesizes setoid *)
(* TODO:  easier if we also demand  setoid AA  ? *)
definition
  invariant :: "'a * 'a => 'a setoid => bool" where
  [MRjud 1 1]: "invariant xs AA == 
    ((fst xs) : carOf AA  &  (snd xs) : carOf AA  &  eqOf AA (fst xs) (snd xs) )"


lemma invariant_reflD: " invariant (t, t) AA ==> t : carOf AA"
  by (simp add: invariant_def)

lemma invariant_sset_reflD: " invariant (t, t) (sset A) ==> t : A "
  apply (drule invariant_reflD)
  by simp


lemma invariant_reflI: "[|  setoid AA  ;  x : carOf AA  |] ==>
   invariant (x, x) AA "
   apply (simp add: invariant_def) by (blast intro: setoid_refl)

lemma (*[impl_frule]*) "[|  x : carOf AA  &&&  setoid AA  |] ==>
   invariant (x, x) AA "
   apply (erule conjunctionE) by (rule invariant_reflI)

lemma invariant_app[MR]: "[|
    invariant (f, f2) (AA ~s~> BB)  ;  setoid BB  ;
    invariant (a, a2) AA  |] ==>
  invariant (f a, f2 a2) BB "
    unfolding invariant_def
    apply (simp add: fun_setoid_eqOf_eq fun_setoid_carOf_eq, (erule conjE)+, intro conjI)
    apply (blast, blast)
    by (rule sfun_eq_app[where f=f, where a=a])

lemma invariant_lam[MR]: "[|
    setoid AA  ;
    !! x .  invariant (x, x) AA  ==>
      invariant (t x, t2 x) BB  ;
    !! x x2 .  [|  invariant (x, x) AA  ;  invariant (x2, x2) AA  ;  invariant (x, x2) AA  |]  ==>
      invariant (t x, t x2) BB  ;
    !! x x2 .  [|  invariant (x, x) AA  ;  invariant (x2, x2) AA  ;  invariant (x, x2) AA  |]  ==>
      invariant (t2 x, t2 x2) BB  |] ==>
  invariant (setoid_lam AA t, setoid_lam AA t2) (AA ~s~> BB) "
  apply (simp add: invariant_def)
  apply (intro conjI) unfolding setoid_lam_def
  by (blast intro: setoid_refl)+


(* optimize for domain=set case; in general invariant is exponential in the number of lambdas *)
lemma invariant_lam_opt[MR]: "[|
    !! x. invariant (x, x) (sset A)  ==>  invariant (t x, t2 x) BB  ;
    setoid BB  |] ==>
  invariant (setoid_lam (sset A) t, setoid_lam (sset A) t2) (sset A ~s~> BB) "
  apply (simp add: invariant_def)
  apply (intro conjI) unfolding setoid_lam_def  
  by (auto intro: setoid_refl set_setoid)+


lemma invariant_all[MR]: " invariant (setoid_lam AA P, setoid_lam AA P2) (AA ~s~> UNIV_s)  ==>
  invariant (setoid_all AA P, setoid_all AA P2) UNIV_s "
  unfolding setoid_all_def invariant_def setoid_lam_def
  apply (simp add: carOf_sset)
  by auto

lemma invariant_eq[MR]: "  setoid AA ==>
  invariant (eqOf AA, eqOf AA) (AA ~s~> AA ~s~> UNIV_s)  "
    apply (rule invariant_reflI)
    apply simp+ apply rule apply simp+
    apply (safe, (simp add: fun_setoid_eqOf_eq)+)
    defer 1 apply (simp add: fun_setoid_eqOf_eq, rule, simp)
    by (blast intro: setoid_refl setoid_trans setoid_sym)+

lemma invariant_conj[MR]: "
  invariant ((op &), (op &)) (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)"
apply (rule invariant_reflI)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  by (metis carOf_UNIV_s fun_setoid_UNIV_s iso_tuple_UNIV_I)
   

lemma invariant_impl[MR]: "
  invariant ((op -->), (op -->)) (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)"
apply (rule invariant_reflI)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  by (metis elem_UNIV_sI fun_setoid_UNIV_s)




(* setoid rewriting engine *)

(* synth  t2  from  t1,   t1 is primary *)
definition
  ssimpto_const :: "'a => 'a => 'a setoid => bool" ("(_) ssimpto (_) in (_)" [10,10,10] 10) where
  [MRjud 1 2]: "ssimpto_const t1 t2 AA == (eqOf AA t1 t2  &  t1 : carOf AA   &  t2 : carOf AA  &  setoid AA)"
definition
  sirewto_const :: "'a => 'a => 'a setoid => bool" ("(_) sirewto (_) in (_)" [10,10,10] 10) where
  [MRjud 1 2]: "sirewto_const t1 t2 AA == (eqOf AA t1 t2  &  t1 : carOf AA   &  t2 : carOf AA  &  setoid AA)"
definition
  srewto_const :: "'a => 'a => 'a setoid => bool" ("(_) srewto (_) in (_)" [10,10,10] 10) where
  [MRjud 1 2]: "srewto_const t1 t2 AA == (eqOf AA t1 t2  &  t1 : carOf AA   &  t2 : carOf AA  &  setoid AA)"
definition
  ssubsimpto_const :: "'a => 'a => 'a setoid => bool" ("(_) ssubsimpto (_) in (_)" [10,10,10] 10) where
  [MRjud 1 2]: "ssubsimpto_const t1 t2 AA == (eqOf AA t1 t2  &  t1 : carOf AA   &  t2 : carOf AA  &  setoid AA)"

lemma [MRjud 1 1]: "(t : X) == (t : X)" by simp
  (* regarded as a purely factual judgement *)
lemma [MRjud 3 0]: "eqOf AA t1 t2 == eqOf AA t1 t2" by simp


definition
  checkbeta_const :: "('a => 'b) => 'a => 'b => 'b setoid => bool" ("checkbeta (_) (_) to (_) in (_)" [10,10,10,10] 10)
where
  [MRjud 2 2]: "checkbeta_const t1 t2 t' AA ==
     (eqOf AA (t1 t2) t'  &  (t1 t2) : carOf AA   &  t' : carOf AA  &  setoid AA)"




(* synth  t2  from  t1,   t1 is primary *)
(* rudimentary big-step simplification of propositions *)
definition
  psimpto_const :: "'a::{} => 'a => prop" ("(_) psimpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "psimpto_const t1 t2 == (t1 == t2)"



locale setoid_rewr =
  fixes dummy :: 'a
begin

(* low prior *)
lemma id_sub[MR]: "[|  t : carOf AA  ;  setoid AA  |] ==>
  t ssubsimpto t in AA  "
    unfolding ssubsimpto_const_def by (simp add: setoid_refl)

(* beachte: decompose matching auf primaere Objekte eta-expandiert diese nicht on-the-fly
     sichert hier Termination weil sonst auf t in t(x) in der Premisse wieder diese Regel
     passen wuerde *)
lemma lam_sub[MR]: "[|
    (% x. t(x)) : carOf (AA ~s~> BB)  ;
    setoid AA  ;  setoid BB ;
    (!! x.  x : carOf AA  ==>   t(x) ssimpto t'(x) in BB  )  |]  ==>
  (% x. t(x))  ssubsimpto  (% x. t'(x))  in  (AA ~s~> BB)  "
  unfolding ssubsimpto_const_def ssimpto_const_def
  apply simp
  apply (rule conjI) apply blast
  apply rule apply simp
  proof -
    fix x x2
    assume tty[intro]: "t : AA ~> BB"
       and AAs: "setoid AA" and BBs: "setoid BB"
       and H: "!!x. x : carOf AA ==> eqOf BB (t x) (t' x) & t x : carOf BB & t' x : carOf BB"
       and xty[simp, intro]: "x : carOf AA" and x2ty[simp, intro]: "x2 : carOf AA"
       and eq[simp, intro]: "eqOf AA x x2"
    from H have "t' x : carOf BB" by blast
    moreover from H have "t x : carOf BB" by blast
    moreover from H have "t x2 : carOf BB" by blast
    moreover from H have "t' x2 : carOf BB" by blast
    moreover from H have "eqOf BB (t' x) (t x)" by (blast intro: setoid_sym[OF BBs])
    moreover have "eqOf BB ... (t x2)" by (simp add: sfunDeq[OF tty])
    moreover from H have "eqOf BB ... (t' x2)" by blast
    ultimately show "eqOf BB (t' x) (t' x2)"
     by (blast intro: setoid_trans[OF BBs])
  qed

lemma app_sub[MR]: "[|
      t1 ssimpto t1' in (AA ~s~> BB)  ;  setoid BB  ;
      t2 ssimpto t2' in AA  ;
      checkbeta t1' t2' to t' in BB  |] ==>
    (t1 t2) ssubsimpto t' in BB "
  unfolding ssimpto_const_def checkbeta_const_def ssubsimpto_const_def
  proof (simp only: fun_setoid_eqOf_eq fun_setoid_carOf_eq, intro conjI, (erule conjE)+)
   assume AAs: "setoid AA" and BBs: "setoid BB" and AABBs: "setoid (AA ~s~> BB)"
    and t1ty: "t1 : AA ~> BB" and t2ty: "t2 : carOf AA" and t1'ty: "t1' : AA ~> BB"
    and t2'ty: "t2' : carOf AA" and t'ty: "t' : carOf BB"
    and t1eq: "sfun_eq AA BB t1 t1'" and t2eq: "eqOf AA t2 t2'"
    and t'eq: "eqOf BB (t1' t2') t'"
   have t'eq_rev: "eqOf BB t' (t1' t2')"
     by (metis BBs sfun_elim ssym t'eq t'ty t1'ty t2'ty)
   have e1: "eqOf BB (t1 t2) (t1' t2')"
    using assms apply (rule sfun_eq_app[where f=t1, where a=t2])
    apply (rule BBs t1ty t1'ty t2ty t2'ty t1eq t2eq)+ done
   show "eqOf BB (t1 t2) t'"
    by (metis BBs e1 sfun_elim strans t'eq t'ty t1'ty t1ty t2'ty t2ty)
  next
   show "[| sfun_eq AA BB t1 t1' & t1 : AA ~> BB & t1' : AA ~> BB & setoid (AA ~s~> BB);
       setoid BB;
       eqOf AA t2 t2' & t2 : carOf AA & t2' : carOf AA & setoid AA; eqOf BB (t1' t2') t' &
       t1' t2' : carOf BB & t' : carOf BB & setoid BB |]
    ==> t1 t2 : carOf BB" by blast
  qed auto

lemma ssimpto_rule[MR]:
 "[|  t ssubsimpto t' in AA  ;  t' sirewto t'' in AA  |]
 ==>  t ssimpto t'' in AA  "
 unfolding ssimpto_const_def sirewto_const_def ssubsimpto_const_def by (blast intro: setoid_trans)

(* low prior *)
lemma irewto_id[MR]: "[|  t : carOf AA  ;  setoid AA  |] ==>
  t sirewto t in AA"
    unfolding sirewto_const_def by (simp add: setoid_refl)

(* high prior *)
(* bottom-up *)
lemma irewto_rule[MR]: "[|
    try (t srewto t' in AA)  ;
    t' ssimpto t'' in AA  |] ==>
  t sirewto t'' in AA  "
    unfolding srewto_const_def sirewto_const_def try_const_def ssimpto_const_def
    by (blast intro: setoid_trans)

(* low prior *)
lemma checkbeta_id[MR]: "[|
    (t1 t2) : carOf AA  ;  setoid AA  |] ==>
  checkbeta t1 t2 to (t1 t2) in AA"
  unfolding checkbeta_const_def by (simp add: srefl)

(* high priority *)
lemma checkbeta_rew[MR]:
  "[|  try ( (t1(t2)) srewto t' in AA )  ;  (t1(t2)) ssimpto t'' in AA |]
  ==>  checkbeta (% x. t1(x)) t2 to t'' in AA   "
  unfolding try_const_def ssimpto_const_def srewto_const_def checkbeta_const_def
  by simp





(* rudimentary big-step rewriting of propositions *)
lemma [MR]: "[|
    t1 psimpto t1'  ;  t2 psimpto t2'  |]
  ==>  (t1 t2) psimpto (t1' t2')  "
  unfolding psimpto_const_def by simp

lemma [MR]: "[|
    !! x. P x psimpto P' x  |] ==>
  (% x. P x) psimpto (% x. P' x)  "
  unfolding psimpto_const_def 
  by (tactic {* rtac (Thm.axiom @{theory} "Pure.abstract_rule") 1*})

lemma [MR]: "[|
    !! x.  x : A ==> P x psimpto P' x  |] ==>
  (ALL x : A. P x) psimpto (ALL x : A. P' x)  "
  unfolding psimpto_const_def by simp

lemma [MR]:
  "[|  (PROP t1) psimpto (PROP t1')  ;  PROP t1' ==> (PROP t2) psimpto (PROP t2') |]
  ==> (PROP t1 ==> PROP t2) psimpto (PROP t1' ==> PROP t2')"
 unfolding psimpto_const_def by simp

lemma [MR]: "[|  tracing ''eqOf simplification rule'' (eqOf AA t1 t2) ;
    t1 ssimpto t' in AA  ;
    t2 ssimpto t' in AA   |] ==>
  (eqOf AA t1 t2) psimpto True  "
  unfolding ssimpto_const_def psimpto_const_def
  apply (rule eq_reflection, (erule conjE)+)
  apply rule+ by (blast intro: setoid_sym setoid_trans)




(* pick up eqOf assumptions implicitly if typing known *)
lemma [impl_frule]:  "
  eqOf AA t1 t2  &&&  t1 : carOf AA  &&&  t2 : carOf AA  &&&  setoid AA
  ==>  t1 srewto t2 in AA"
  unfolding srewto_const_def
  apply (erule conjunctionE)+ apply (intro conjI) by simp+





(* pick up eqOf assumptions while rewriting via special cong rule, synthesize types *)
lemma [MR 3]: "[|  t1 : carOf AA   ;  t2 : carOf AA   ;  setoid AA  ; tracing ''eqOf pickup rule'' (eqOf AA t1 t2) ;
    t1 srewto t2 in AA ==> (PROP P) psimpto (PROP P') |] ==>
  (eqOf AA t1 t2 ==> PROP P) psimpto (eqOf AA t1 t2 ==> PROP P')"
  unfolding psimpto_const_def  srewto_const_def
  by simp

(*lemma "[| setoid AA ; x srewto y in AA ; x : carOf AA  ; y : carOf AA |] ==> eqOf AA y x"
  by mrsimp


schematic_lemma "[| setoid AA  ;  x : carOf AA  ;  y : carOf AA  ;  eqOf AA x y |] ==> eqOf AA y x"
  apply mrsimp by  *)



end (* locale setoid_rewriting *)









lemma iso_sDsetoid[impl_frule]: 
"f : AA ~=~> BB  ==>  setoid AA" 
"f : AA ~=~> BB  ==>  setoid BB"
  unfolding iso_s_def by auto

lemma iso_sDfunsp: "f : AA ~=~> BB ==>  f : AA ~> BB"
  unfolding iso_s_def by auto

(* would induce fact inconsistencies on f : ?CC as an frule *)
(* lemma iso_sDfunsp_MR[MR]: "  try(  f : AA ~=~> BB  ) ==>
  f : AA ~> BB  " unfolding try_const_def by (rule iso_sDfunsp) *)


lemma iso_sDsurj: assumes fty:"f \<in> AA ~=~> BB" and bty: "b \<in> carOf BB"
    shows "\<exists> a \<in> carOf AA. eqOf BB (f a) b"
  apply (insert fty[simplified iso_s_def] bty) by auto

lemma iso_sDsurj2: assumes fty:"f \<in> AA ~=~> BB" and bty: "b \<in> carOf BB"
    shows "\<exists> a. a \<in> carOf AA \<and> eqOf BB (f a) b"
  by (rule iso_sDsurj[OF fty bty, simplified Bex_def])

lemma iso_sDinj: assumes fty: "f \<in> AA ~=~> BB" shows
   "a1 \<in> carOf AA \<Longrightarrow> a2 \<in> carOf AA \<Longrightarrow> eqOf BB (f a1) (f a2) \<Longrightarrow> eqOf AA a1 a2"
  apply(insert fty[simplified iso_s_def])
  by auto

lemma iso_sDwf: assumes fty: "f \<in> AA ~=~> BB" shows
   "a1 \<in> carOf AA \<Longrightarrow> a2 \<in> carOf AA \<Longrightarrow> eqOf AA a1 a2 \<Longrightarrow> eqOf BB (f a1) (f a2)"
  apply(insert fty[simplified iso_s_def])
  by auto

lemma iso_sI[intro!]: 
assumes "setoid AA" and "setoid BB" and "f \<in> AA ~> BB"
and "\<forall> a1 \<in> carOf AA. \<forall> a2 \<in> carOf AA.
         eqOf AA a1 a2 \<longleftrightarrow> eqOf BB (f a1) (f a2)"
and "\<forall> b \<in> carOf BB. \<exists> a \<in> carOf AA. eqOf BB (f a) b"
shows "f \<in> AA ~=~> BB"
  using assms unfolding iso_s_def by auto


lemma id_iso_s: assumes setoid: "setoid AA" shows "id : AA ~=~> AA"
  apply rule
  apply (rule setoid)+
  apply (rule id_in_sfun)
  apply simp+
  apply (rule+)
  by (rule srefl[OF setoid])

lemma id_set_iso_s: "id : sset A ~=~> sset A"
  apply (rule id_iso_s) by (rule set_setoid)

lemma id_UNIV_iso_s: "id : UNIV_s ~=~> UNIV_s"
  by (simp add: id_set_iso_s)

lemma bij_to_equi: 
assumes "bij_betw f A A'"
shows "f \<in> sset A ~=~> sset A'" 
using assms unfolding bij_betw_def inj_on_def by auto

(* definition "s_inv_pred AA BB f b a \<equiv> a \<in> carOf AA \<and> eqOf BB (f a) b"
   definition "s_inv AA BB f b \<equiv> SOME a. s_inv_pred AA BB f b a"  *)

lemma s_inv_pred: 
assumes "f \<in> AA ~=~> BB" and "b \<in> carOf BB"
shows "\<exists> a. s_inv_pred AA BB f b a"
unfolding s_inv_pred_def using iso_sDsurj[OF assms] by auto

lemma s_inv_pred_s_inv:
assumes "f \<in> AA ~=~> BB" and "b \<in> carOf BB"
shows "s_inv_pred AA BB f b (s_inv AA BB f b)"
unfolding s_inv_def apply(rule someI_ex) using s_inv_pred[OF assms] .

lemma s_inv_carOf[simp]:
assumes "f \<in> AA ~=~> BB" and "b \<in> carOf BB"
shows "s_inv AA BB f b \<in> carOf AA"
using s_inv_pred_s_inv[OF assms] unfolding s_inv_pred_def by auto

lemma s_inv_eqOf:
assumes "f \<in> AA ~=~> BB" and "b \<in> carOf BB"
shows "eqOf BB (f (s_inv AA BB f b)) b"
using s_inv_pred_s_inv[OF assms] unfolding s_inv_pred_def by auto

lemma s_inv_iso_s: 
assumes "f \<in> AA ~=~> BB" 
shows "s_inv AA BB f \<in> BB ~=~> AA"
apply(rule iso_sI)
  apply (metis assms iso_sDsetoid(2))
  apply (metis assms iso_sDsetoid(1))
  apply(rule sfun_spaciI) 
    using assms apply fastforce
    using setoid_refl[OF iso_sDsetoid(1)[OF assms]]
    apply (smt assms iso_sDfunsp iso_sDinj iso_sDsetoid(2) 
               s_inv_carOf s_inv_eqOf sfun_elim ssym strans)
  apply (smt assms equiv_rel_sym iso_sDfunsp iso_sDinj iso_sDsetoid(2) 
             s_inv_carOf s_inv_eqOf setoid_def sfun_elim strans)
  by (smt assms iso_sDfunsp iso_sDinj s_inv_carOf s_inv_eqOf sfun_elim)

   
lemma s_inv_eqOf_rev:
assumes "f \<in> AA ~=~> BB" and "a \<in> carOf AA"
shows "eqOf AA (s_inv AA BB f (f a)) a"
by (smt assms iso_sDfunsp iso_sDinj s_inv_carOf s_inv_eqOf sfun_elim)

lemma sfun_eq_s_inv: 
assumes "f \<in> AA ~=~> BB"
shows "sfun_eq AA BB (s_inv BB AA (s_inv AA BB f)) f"
(* Z3 only then, E also now: *)
(* sledgehammer messages 20
by (smt assms iso_sDfunsp iso_sDsetoid(1) s_inv_carOf s_inv_eqOf s_inv_iso_s sfun_elim sfun_eq_def ssym strans)
*) 
by (smt assms equiv_rel_trans iso_sDfunsp iso_sDsetoid(2) s_inv_eqOf s_inv_iso_s 
         setoid_def sfun_elim sfun_eq_def ssym)

lemma iso_s_intro2:
assumes AA: "setoid AA" and BB: "setoid BB"
and f: "f \<in> AA ~> BB" and g: "g \<in> BB ~> AA" and 
eqBB: "sfun_eq BB BB (f o g) id" and eqAA: "sfun_eq AA AA (g o f) id"
shows "f \<in> AA ~=~> BB"
apply default
  using AA BB f apply (fastforce, fastforce, fastforce)
  apply safe
    apply (metis f sfun_eq)
    (* Z3 only: *)
    apply (smt AA eqAA equiv_rel_trans f g id_apply o_eq_dest_lhs 
            setoid_def sfun_elim sfun_eqE ssym) 
    by (metis eqBB g id_apply o_apply sfun_elim sfun_eqE)
 
lemma sfun_eq_comp_id:
fixes AA :: "'a setoid" and BB :: "'b setoid"
assumes AA: "setoid AA" and BB: "setoid BB"
and f: "f \<in> AA ~> BB" and g: "g \<in> BB ~> AA" and 
eq: "sfun_eq BB BB (f o g) id" and "sfun_eq AA AA (g o f) id" 
shows "sfun_eq BB AA (s_inv AA BB f) g" 
unfolding sfun_eq_def proof clarify
  fix b assume b: "b \<in> carOf BB"
  have ff: "f \<in> AA ~=~> BB" using iso_s_intro2[OF assms] .
  have gb: "g b \<in> carOf AA" by (metis b g sfun_ty)
  hence fgb: "f (g b) \<in> carOf BB" by (metis f sfun_ty)
  have "eqOf BB (f (s_inv AA BB f b)) b" by (metis b ff s_inv_eqOf) 
  moreover 
  {have "eqOf BB (f (g b)) b" by (metis b eq id_apply o_apply sfun_eqE)
   hence "eqOf BB b (f (g b))" by (metis BB b fgb ssym)
  }
  ultimately have "eqOf BB (f (s_inv AA BB f b)) (f (g b))"
  by (metis BB b f ff fgb s_inv_carOf sfun_elim strans)
  thus "eqOf AA (s_inv AA BB f b) (g b)" using ff
  by (metis b gb iso_sDinj s_inv_carOf)
qed












theorem splice_iso_s: 
assumes f: "f \<in> AA ~=~> AA'" and g: "g : BB ~=~> BB'"
shows "(f : AA -> AA'  ##>>  g : BB -> BB') \<in> (AA ~s~> BB) ~=~> (AA' ~s~> BB')"
proof-
  have ff: "f \<in> AA ~> AA'" and gg: "g : BB ~> BB'"
  by (metis f g iso_sDfunsp)+
  have AA: "setoid AA" and BB: "setoid BB" 
  and AA': "setoid AA'" and BB': "setoid BB'" by (metis f g iso_sDsetoid)+ 
  show ?thesis unfolding splice_def iso_s_def proof (safe, unfold fun_setoid_simps)
    fix h h2
    assume h: "h \<in> AA ~> BB" and h2: "h2 \<in> AA ~> BB" and eq: "sfun_eq AA BB h h2"
    show "sfun_eq AA' BB' (g \<circ> h \<circ> s_inv AA AA' f) (g \<circ> h2 \<circ> s_inv AA AA' f)"
    unfolding sfun_eq_def comp_def proof safe
      fix a assume a: "a \<in> carOf AA'"
      hence "eqOf AA (s_inv AA AA' f a) (s_inv AA AA' f a)" 
      by (metis AA f s_inv_carOf srefl)
      hence "eqOf BB (h (s_inv AA AA' f a)) (h2 (s_inv AA AA' f a))"
      by (metis a eq f s_inv_carOf sfun_eqD) 
      thus "eqOf BB' (g (h (s_inv AA AA' f a))) (g (h2 (s_inv AA AA' f a)))"
      by (metis a f g h h2 iso_sDwf s_inv_carOf sfun_elim)
    qed
    thus "sfun_eq AA' BB' (g \<circ> h \<circ> s_inv AA AA' f) (g \<circ> h2 \<circ> s_inv AA AA' f)" .
  next
    fix h1 h2
    assume h1: "h1 \<in> AA ~> BB" and h2: "h2 \<in> AA ~> BB"
    and eq: "sfun_eq AA' BB' (g \<circ> h1 \<circ> s_inv AA AA' f) (g \<circ> h2 \<circ> s_inv AA AA' f)"
    show "sfun_eq AA BB h1 h2"
    unfolding sfun_eq_def comp_def proof safe
      fix a assume a: "a \<in> carOf AA"
      then obtain a' where a': "a' \<in> carOf AA'" and a_eq: "eqOf AA a (s_inv AA AA' f a')"
      by (metis AA f iso_sDfunsp s_inv_carOf s_inv_eqOf_rev sfun_ty ssym) 
      have s_inv_a': "s_inv AA AA' f a' \<in> carOf AA" by (metis a' f s_inv_carOf) 
      have "eqOf BB (h1 a) (h1 (s_inv AA AA' f a'))"
      using h1 a s_inv_a' by (smt a_eq h1 sfun_eq)
      moreover 
      {have "eqOf BB' (g (h1 (s_inv AA AA' f a'))) (g (h2 (s_inv AA AA' f a')))"
       by (metis a' eq o_def sfun_eqE)
       hence "eqOf BB (h1 (s_inv AA AA' f a')) (h2 (s_inv AA AA' f a'))"
       by (metis g h1 h2 iso_sDinj s_inv_a' sfun_elim)
      }
      ultimately have "eqOf BB (h1 a) (h2 (s_inv AA AA' f a'))"
      by (smt BB a h1 h2 s_inv_a' sfun_elim strans)
      moreover have "eqOf BB (h2 (s_inv AA AA' f a')) (h2 a)"
      using h2 a s_inv_a' by (metis AA a_eq sfun_eq ssym) 
      ultimately show "eqOf BB (h1 a) (h2 a)"
      by (metis BB a h1 h2 s_inv_a' sfun_elim strans)
    qed
  next
    fix h' assume h': "h' \<in> AA' ~> BB'"     
    show "\<exists>h\<in>AA ~> BB. sfun_eq AA' BB' (g \<circ> h \<circ> s_inv AA AA' f) h'"
    proof (rule bexI[of _ "(s_inv BB BB' g) o h' o f"])
      show "sfun_eq AA' BB' (g \<circ> (s_inv BB BB' g \<circ> h' \<circ> f) \<circ> s_inv AA AA' f) h'"
      unfolding sfun_eq_def comp_def proof safe
        fix a' assume a': "a' \<in> carOf AA'"
        have s_inv_a': "s_inv AA AA' f a' \<in> carOf AA" by (metis a' f s_inv_carOf)
        have 0: "h' (f (s_inv AA AA' f a')) \<in> carOf BB'"
        by (metis f h' iso_sDfunsp s_inv_a' sfun_elim)
        have "eqOf AA' (f (s_inv AA AA' f a')) a'" by (metis a' f s_inv_eqOf)
        hence "eqOf BB' (h' (f (s_inv AA AA' f a'))) (h' a')"
        by (metis a' f h' iso_sDfunsp s_inv_a' sfun_elim) 
        moreover have "eqOf BB' (g (s_inv BB BB' g (h' (f (s_inv AA AA' f a'))))) 
                                (h' (f (s_inv AA AA' f a')))"
        by (metis 0 g s_inv_eqOf)
        ultimately show 
        "eqOf BB' (g (s_inv BB BB' g (h' (f (s_inv AA AA' f a'))))) (h' a')"
        by (metis 0 BB' a' g h' iso_sDfunsp s_inv_carOf sfun_ty strans)
      qed
    next
      show "s_inv BB BB' g \<circ> h' \<circ> f \<in> AA ~> BB"
      apply(rule comp_sfun[OF ff], rule comp_sfun[OF h'])
      by (metis g iso_sDfunsp s_inv_iso_s)
    qed     
  next
    fix h assume h: "h \<in> AA ~> BB"
    show "g \<circ> h \<circ> s_inv AA AA' f \<in> AA' ~> BB'"
    apply(rule comp_sfun[of _ _ AA])
      apply (metis f iso_sDfunsp s_inv_iso_s)
      by (rule comp_sfun[OF h gg])     
  qed (auto simp add: AA BB AA' BB' f g)
qed


lemma isomap_funS1:
assumes f: "f \<in> AA ~=~> AA'"
and iso: 
"\<And> x x'. (phi:  x : AA  isomapto  x' : AA'  via f)  \<Longrightarrow>   
         (phi:  (t x) : BB  isomapto  (t' x') : BB'  via g)"
shows "t \<in> carOf AA \<rightarrow> carOf BB"
apply rule by (metis f iso iso_sDfunsp iso_sDsetoid isomapto_via_def sfun_elim srefl)

lemma isomap_funS2:
assumes f: "f \<in> AA ~=~> AA'"
and iso: 
"\<And> x x'. (phi:  x : AA  isomapto  x' : AA'  via f)  \<Longrightarrow>   
         (phi:  (t x) : BB  isomapto  (t' x') : BB'  via g)"
shows "t' \<in> carOf AA' \<rightarrow> carOf BB'"
apply rule by (metis f iso iso_sDsetoid iso_sDsurj isomapto_via_def)

lemma isomapto_sfun: 
assumes t: "t \<in> AA ~> BB"
and f: "f \<in> AA ~=~> AA'" and g: "g \<in> BB ~=~> BB'"
and iso: 
"\<And> x x'. (phi:  x : AA  isomapto  x' : AA'  via f)  \<Longrightarrow>   
         (phi:  (t x) : BB  isomapto  (t' x') : BB'  via g)"
shows "t' \<in> AA' ~> BB'"
proof
  have ff: "f \<in> AA ~> AA'" and gg: "g : BB ~> BB'"
  by (metis f g iso_sDfunsp)+
  have AA: "setoid AA" and BB: "setoid BB" 
  and AA': "setoid AA'" and BB': "setoid BB'" by (metis f g iso_sDsetoid)+ 
  fix a' a2'
  assume a': "a' \<in> carOf AA'" and a2': "a2' \<in> carOf AA'" and eq: "eqOf AA' a' a2'"
  obtain a where a: "a \<in> carOf AA" and eq_fa_a': "eqOf AA' (f a) a'" 
  by (metis a' f iso_sDsurj2)
  hence "phi:  a : AA  isomapto  a' : AA'  via f" by (metis AA AA' a' f isomapto_via_def)
  hence 0: "phi:  (t a) : BB  isomapto  (t' a') : BB'  via g" using iso by simp
  hence 1: "eqOf BB' (t' a') (g (t a))"
  by (metis gg isomapto_via_def sfun_elim ssym) 
  (*  *)
  obtain a2 where a2: "a2 \<in> carOf AA" and eq_fa2_a2': "eqOf AA' (f a2) a2'" 
  by (metis a2' f iso_sDsurj2)
  hence "phi:  a2 : AA  isomapto  a2' : AA'  via f" by (metis AA AA' a2' f isomapto_via_def)
  hence 02: "phi:  (t a2) : BB  isomapto  (t' a2') : BB'  via g" using iso by simp
  hence 2: "eqOf BB' (g (t a2)) (t' a2')" by (metis isomapto_eqOf)
  (*  *)
  have "eqOf AA' (f a) (f a2)"
  by (metis AA' a a' a2 a2' eq eq_fa2_a2' eq_fa_a' ff sfun_ty ssym strans) 
  hence "eqOf AA a a2" by (metis a a2 f iso_sDinj) 
  hence 3: "eqOf BB (t a) (t a2)" by (metis a a2 sfun_eq t) 
  (*  *)
  show "eqOf BB' (t' a') (t' a2')"
  by (smt "0" "3" BB' 02 gg isomapto_carOf1 isomapto_carOf2 
            isomapto_eqOf sfun_elim ssym strans)
qed(metis f iso iso_sDsetoid iso_sDsurj2 isomapto_via_def)


lemma slam_isomapto: 
assumes 
eq: "\<And> x x2. \<lbrakk>x \<in> carOf AA; x2 \<in> carOf AA; eqOf AA x x2\<rbrakk> \<Longrightarrow> eqOf BB (t x) (t x2)"
and f: "f \<in> AA ~=~> AA'" and g: "g \<in> BB ~=~> BB'"
and iso: 
"\<And> x x'. (phi:  x : AA  isomapto  x' : AA'  via f)  \<Longrightarrow>   
         (phi:  (t x) : BB  isomapto  (t' x') : BB'  via g)"
shows "phi:  (slam x\<in>AA. t x) : AA ~s~> BB  isomapto  
         (slam x'\<in>AA'. t' x') : (AA' ~s~> BB')
         via (f : AA -> AA'  ##>>  g : BB -> BB')"
proof-
  have ff: "f \<in> AA ~> AA'" and gg: "g : BB ~> BB'"
  by (metis f g iso_sDfunsp)+
  have AA: "setoid AA" and BB: "setoid BB" 
  and AA': "setoid AA'" and BB': "setoid BB'" by (metis f g iso_sDsetoid)+ 
  have t: "t \<in> AA ~> BB" 
  apply(subst sfun_def) using isomap_funS1[OF f iso] eq by force
  have t': "t' \<in> AA' ~> BB'" using isomapto_sfun[OF t f g iso] by simp
  show ?thesis
  unfolding isomapto_via_def apply (safe, unfold fun_setoid_simps setoid_lam_def)
    apply (rule t, rule t')
    apply (rule fun_setoid[OF AA BB], rule fun_setoid[OF AA' BB'], 
           rule fun_setoid[OF AA BB], rule fun_setoid[OF AA' BB'])
    using splice_iso_s[OF f g] apply (metis carOf_fun_setoid iso_sDfunsp sfun_ty) 
    using splice_iso_s[OF f g] 
    apply (metis carOf_fun_setoid eqOf_fun_setoid iso_sDwf) 
    using splice_iso_s[OF f g] 
    apply (metis carOf_fun_setoid eqOf_fun_setoid iso_sDwf)
    using splice_iso_s[OF f g]
    apply (metis carOf_fun_setoid eqOf_fun_setoid iso_sDinj) 
    using splice_iso_s[OF f g]
    apply (metis carOf_fun_setoid eqOf_fun_setoid iso_sDsurj2)
    unfolding sfun_eq_def splice_def comp_def apply safe
    by (metis f iso iso_sDsetoid isomapto_via_def s_inv_carOf s_inv_eqOf)
qed

lemma isomapto_app: 
assumes 
 BB: "setoid BB" and BB': "setoid BB'" and 
 g: "g \<in> BB ~=~> BB'" and 
T1: "phi:  t1 : (AA ~s~> BB)  isomapto  t1' : (AA' ~s~> BB') 
     via (f : AA -> AA'  ##>>  g : BB -> BB')" and 
T2: "phi:  t2 : AA  isomapto  t2' : AA'  via f"
shows "phi:  (t1 t2) : BB  isomapto  (t1' t2') : BB' via g"
proof-
  have AA: "setoid AA" and AA': "setoid AA'" by (metis isomapto_via_def T2)+
  have t1: "t1 \<in> AA ~> BB" by (metis fun_setoid_carOf isomapto_via_def T1) 
  have t1': "t1' \<in> AA' ~> BB'" by (metis T1 fun_setoid_carOf isomapto_via_def)
  have t2: "t2 \<in> carOf AA" by (metis isomapto_via_def T2)
  have t2': "t2' \<in> carOf AA'" by (metis T2 isomapto_via_def)
  have f: "f \<in> AA ~=~> AA'" by (metis T2 isomapto_via_def)
  have ff: "f \<in> AA ~> AA'" by (metis f iso_sDfunsp)
  have gg: "g \<in> BB ~> BB'" by (metis g iso_sDfunsp)
  show ?thesis unfolding isomapto_via_def apply safe
    apply (rule sfun_ty[OF t1 t2])
    apply (rule sfun_ty[OF t1' t2'])
    apply(rule BB, rule BB', rule BB, rule BB')
    apply (metis gg sfun_ty)
    apply (metis gg sfun_eq)
    apply (metis g iso_sDwf)
    apply (metis g iso_sDinj)
    apply (metis g iso_sDsurj2)
  proof-
    have sf: "sfun_eq AA' BB' (g \<circ> t1 \<circ> s_inv AA AA' f) t1'"
    using T1 unfolding splice_def by (metis eqOf_fun_setoid isomapto_eqOf) 
    have t: "eqOf AA' (f t2) t2'" by (metis T2 isomapto_via_def)
    have "eqOf BB' ((g \<circ> t1 \<circ> s_inv AA AA' f) (f t2)) (t1' t2')"
    (* Z3 only: *)
    using sf unfolding sfun_eq_def t   
    by (smt BB' f ff gg o_apply s_inv_carOf sfun_elim strans surjective 
             t t1 t1' t2 t2')
    hence 1: "eqOf BB' (g (t1 ( s_inv AA AA' f (f t2)))) (t1' t2')" by simp
    have "eqOf AA t2 (s_inv AA AA' f (f t2))"
    by (metis AA f ff s_inv_carOf s_inv_eqOf_rev sfun_elim ssym t2)
    hence "eqOf BB (t1 t2) (t1 (s_inv AA AA' f (f t2)))"
    by (metis f ff s_inv_carOf sfun_elim t1 t2)
    hence "eqOf BB' (g (t1 t2)) (g (t1 (s_inv AA AA' f (f t2))))"
    by (metis f ff gg s_inv_carOf sfun_elim t1 t2)
    thus "eqOf BB' (g (t1 t2)) (t1' t2')" using 1
    by (metis BB' f ff gg s_inv_carOf sfun_elim strans t1 t1' t2 t2')
  qed
qed


(* we don't decompose at application position in order to communicate the setoid AA
   to the isomorphic transfer of P *)
lemma isomapto_setoid_all:
assumes 
    f: "f \<in> AA ~=~> AA'"
and phi: 
"phi:  (setoid_lam AA P) : (AA ~s~> UNIV_s)  isomapto  
       (setoid_lam AA' P') : (AA' ~s~> UNIV_s)
 via (f : AA -> AA'  ##>>  id : UNIV_s -> UNIV_s)"
shows "phi:  (setoid_all AA P) : UNIV_s  isomapto  (setoid_all AA' P') : UNIV_s via id"
unfolding isomapto_via_def id_def setoid_all_def proof(intro conjI)
  let ?A = "carOf AA"   let ?A' = "carOf AA'"
  have AA: "setoid AA" and AA': "setoid AA'"
  using f by (metis iso_sDsetoid)+
  let ?ff = "s_inv AA AA' f"   let ?G = "\<lambda>h\<Colon>'a \<Rightarrow> bool. h \<circ> ?ff"
  have ff: "?ff \<in> AA' ~=~> AA" using f by (metis s_inv_iso_s)
  have G: "?G \<in> (AA ~s~> UNIV_s) ~=~> (AA' ~s~> UNIV_s)" and 
  eq: "eqOf (AA' ~s~> UNIV_s) (P \<circ> ?ff) P'" and 
  P: "P \<in> carOf (AA ~s~> UNIV_s)"
  using phi unfolding isomapto_via_def splice_def id_o setoid_lam_def by auto
  have eqP: "eqOf (AA ~s~> UNIV_s) P P"
  using phi unfolding isomapto_via_def splice_def id_o setoid_lam_def by (metis srefl)
  show "eqOf UNIV_s (Ball ?A P) (Ball ?A' P')"
  unfolding eqOf_UNIV_s proof safe
    fix a' assume P: "\<forall> a \<in> ?A. P a" and a': "a' \<in> ?A'"
    obtain a where a: "a \<in> ?A" and faa': "eqOf AA' (f a) a'"
    by (metis (no_types) f a' iso_sDfunsp iso_sDsetoid(2) iso_sDsurj2 sfun_ty)
    have Pa: "P a" using P a by simp
    have fa: "f a \<in> ?A'" using f by (metis a iso_sDfunsp sfun_elim)
    have ffa': "?ff a' \<in> ?A" using ff by (metis a' f s_inv_carOf)
    have "P (?ff a') = P' a'" using eq a' 
    unfolding eqOf_fun_setoid sfun_eq_def eqOf_UNIV_s by simp
    thus "P' a'" using P ffa' by auto
  next
    fix a assume P': "\<forall> a' \<in> ?A'. P' a'" and a: "a \<in> ?A"
    def a' \<equiv> "f a"
    have a': "a' \<in> ?A'" by (metis a a'_def f iso_sDfunsp sfun_elim)
    have ffa': "?ff a' \<in> ?A" by (metis a' f s_inv_carOf)
    have "eqOf AA (?ff a') a" by (metis a a'_def f s_inv_eqOf_rev)
    hence "P a = P (?ff a')" using P a ffa' 
    unfolding carOf_fun_setoid iso_s_def sfun_def carOf_UNIV_s by auto
    also have "P (?ff a') = P' a'" using eq a' 
    unfolding eqOf_fun_setoid sfun_eq_def eqOf_UNIV_s by simp   
    finally show "P a" using P' a' by auto
  qed
qed (unfold id_def[symmetric], (metis elem_UNIV_sI UNIV_setoid id_UNIV_iso_s)+)

lemma setoid_eqOf_carOf: 
assumes "setoid AA"
shows "eqOf AA \<in> carOf (AA ~s~> AA ~s~> UNIV_s)"
unfolding carOf_fun_setoid sfun_def mem_Collect_eq carOf_UNIV_s apply safe
  apply force
  apply (smt assms eqOf_UNIV_s ssym strans)
  by (smt assms eqOf_fun_setoid eq_UNIV_sI sfun_eq_def ssym strans)


lemma isomapto_eqOf_UNIV_s: 
assumes "f \<in> AA ~=~> AA'"
shows 
"phi:  (eqOf AA) : (AA ~s~> AA ~s~> UNIV_s) isomapto  (eqOf AA') : (AA' ~s~> AA' ~s~> UNIV_s)
  via  
  (f : AA -> AA'  ##>>  (f : AA -> AA'  ##>>  id : UNIV_s -> UNIV_s) : 
  (AA ~s~> UNIV_s) -> (AA' ~s~> UNIV_s))"
unfolding isomapto_via_def apply(intro conjI)
  apply (metis assms iso_sDsetoid(1) setoid_eqOf_carOf)
  apply (metis assms iso_sDsetoid(2) setoid_eqOf_carOf)
  apply (metis UNIV_setoid assms fun_setoid iso_sDsetoid(1))
  apply (metis UNIV_setoid assms fun_setoid iso_sDsetoid(2))
  apply (metis assms id_UNIV_iso_s splice_iso_s)
  unfolding splice_def id_o eqOf_fun_setoid sfun_eq_def eqOf_UNIV_s comp_def id_def
  apply(intro ballI) by (metis assms iso_sDinj iso_sDwf s_inv_iso_s)

lemma isomapto_imp: 
"phi:  (op \<longrightarrow>) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)   
 isomapto   
 (op \<longrightarrow>) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)  
 via id"
unfolding isomapto_via_def carOf_fun_setoid apply(intro conjI)
  apply (metis fun_setoid_UNIV_s iso_tuple_UNIV_I sfun_UNIV_s)
  apply (metis fun_setoid_UNIV_s iso_tuple_UNIV_I sfun_UNIV_s)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  apply (metis fun_setoid_UNIV_s id_UNIV_iso_s)
  unfolding eqOf_fun_setoid sfun_eq_def eqOf_UNIV_s id_def by safe

lemma isomap_or: 
"phi:  (op \<and>) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)   
 isomapto   
 (op \<and>) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s) via id"
unfolding isomapto_via_def carOf_fun_setoid apply(intro conjI)
  apply (metis fun_setoid_UNIV_s iso_tuple_UNIV_I sfun_UNIV_s)
  apply (metis fun_setoid_UNIV_s iso_tuple_UNIV_I sfun_UNIV_s)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  apply (metis UNIV_setoid fun_setoid_UNIV_s)
  apply (metis fun_setoid_UNIV_s id_UNIV_iso_s)
  unfolding eqOf_fun_setoid sfun_eq_def eqOf_UNIV_s id_def by safe


(* products and currying *)

definition
  prod_setoid :: "'a setoid \<Rightarrow> 'b setoid \<Rightarrow> ('a * 'b) setoid" (infixl "*s" 65) where
  "prod_setoid AA BB \<equiv> 
   \<lparr> carOf = carOf AA <*> carOf BB,  
     eqOf = \<lambda> ab ab'. eqOf AA (fst ab) (fst ab') \<and> eqOf BB (snd ab) (snd ab') \<rparr>"

lemma carOf_prod_setoid[simp]:
"carOf (prod_setoid AA BB) = carOf AA <*> carOf BB"
unfolding prod_setoid_def by auto

lemma eqOf_prod_setoid[simp]:
"eqOf (prod_setoid AA BB) (a,b) (a',b') = 
 (eqOf AA a a' \<and> eqOf BB b b')"
unfolding prod_setoid_def by auto

lemmas prod_setoid_simps = carOf_prod_setoid eqOf_prod_setoid

lemma setoid_prod_setoid:
assumes AA: "setoid AA" and BB: "setoid BB"
shows "setoid (AA *s BB)"
unfolding setoid_def equiv_rel_def apply(safe, simp_all)
  apply (metis assms srefl)
  apply (metis AA BB ssym)
  by (metis AA BB strans)

lemma split_setoid:
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC"
shows "split \<in> (AA ~s~> BB ~s~> CC) ~>
               (AA *s BB ~s~> CC)"
apply safe unfolding carOf_fun_setoid apply safe
unfolding eqOf_fun_setoid
  apply (simp, metis sfun_ty)
  apply (simp, metis CC sfun_eq_app)
  by (safe, simp, metis sfun_eq_def)

lemma curry_setoid:
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC"
shows "curry \<in> (AA *s BB ~s~> CC) ~>
               (AA ~s~> BB ~s~> CC)"
apply safe unfolding carOf_fun_setoid apply safe
unfolding eqOf_fun_setoid
  apply (simp, metis AA curry_conv sfun_spaciI srefl)
  apply (simp, metis BB curry_def sfun_eqI srefl)
  by (safe, simp, metis curry_def sfun_eqI)


lemma split_setoid_iso_s:
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC"
shows "split \<in> (AA ~s~> BB ~s~> CC) ~=~>
               (AA *s BB ~s~> CC)"
apply(intro iso_s_intro2[of _ _ _ curry]) 
  apply (metis AA BB CC fun_setoid)
  apply (metis AA BB CC fun_setoid setoid_prod_setoid)
  apply(rule split_setoid[OF assms])
  apply(rule curry_setoid[OF assms])
  unfolding comp_def curry_split split_curry id_def[symmetric]
  apply (metis AA BB CC fun_setoid fun_setoid_carOf_eq 
               fun_setoid_eqOf_eq id_sfun setoid_prod_setoid srefl)
  by (metis AA BB CC fun_setoid fun_setoid_carOf_eq fun_setoid_eqOf_eq id_sfun srefl)

lemma curry_setoid_iso_s:
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC"
shows "curry \<in> (AA *s BB ~s~> CC) ~=~>
               (AA ~s~> BB ~s~> CC)"
apply(intro iso_s_intro2[of _ _ _ split]) 
  apply (metis AA BB CC fun_setoid setoid_prod_setoid)
  apply (metis AA BB CC fun_setoid) 
  apply(rule curry_setoid[OF assms])
  apply(rule split_setoid[OF assms])  
  unfolding comp_def curry_split split_curry id_def[symmetric]
  apply (metis AA BB CC fun_setoid fun_setoid_carOf_eq 
               fun_setoid_eqOf_eq id_sfun setoid_prod_setoid srefl)
  by (safe, simp, metis CC sfun_elim sfun_eqI srefl)

(* list fold and unfold:*) 
definition "lfld \<equiv> \<lambda> (x,xs). Cons x xs"
definition "lunf \<equiv> \<lambda> xs. (hd xs, tl xs)"

lemma lfld_lunf[simp]: "xs \<noteq> [] \<Longrightarrow> lfld (lunf xs) = xs" 
unfolding lfld_def lunf_def by simp

lemma lunf_lfld[simp]: "lunf (lfld x_xs) = x_xs" 
unfolding lfld_def lunf_def by (cases x_xs, simp)

lemma lunf_o_lfld[simp]: "lunf o lfld = id"
by (rule ext) simp

fun product where
  product_nil: "product [] = {[]}"
| product_cons: "product (Cons A As) = { Cons x xs | x xs. x \<in> A \<and> xs \<in> product As }"

lemma lfld_setoid: 
"lfld \<in> sset A *s sset (product As) ~> sset (product (Cons A As))"
unfolding carOf_sset carOf_prod_setoid lfld_def by auto 

lemma lunf_setoid: 
"lunf \<in> sset (product (Cons A As)) ~> sset A *s sset (product As)"
unfolding carOf_sset carOf_prod_setoid lunf_def by auto

lemma lfld_setoid_iso_s:
"lfld \<in> sset A *s sset (product As) ~=~> sset (product (Cons A As))"
apply(intro iso_s_intro2[of _ _ _ lunf])
  apply (metis set_setoid setoid_prod_setoid)
  apply (rule set_setoid) 
  apply(rule lfld_setoid)
  apply(rule lunf_setoid)
  unfolding lfld_def lunf_def by auto

lemma lunf_setoid_iso_s:
"lunf \<in> sset (product (Cons A As)) ~=~> sset A *s sset (product As)"
apply(intro iso_s_intro2[of _ _ _ lfld])
  apply (rule set_setoid)
  apply (metis set_setoid setoid_prod_setoid) 
  apply(rule lunf_setoid)
  apply(rule lfld_setoid)
  unfolding lfld_def lunf_def by auto

definition
  prod_nil_iso :: "('a \<Rightarrow> 'a2) \<Rightarrow> ('b list \<Rightarrow> 'a) \<Rightarrow> 'a2" where
  "prod_nil_iso f \<equiv> (\<lambda> h. f (h []))"


definition
  prod_cons_iso :: "('a => 'a2) => 'a setoid => 'a2 setoid => (('a list => 'b) => 'c2)
     => ('a list => 'b) => ('a2 => 'c2)" where
  "prod_cons_iso f AA AA' g \<equiv> 
   (\<lambda> h. g o h o s_inv AA AA' f) o 
   curry \<circ>
   (\<lambda> h. h o lfld)"

(* used to be: 
definition
  prod_cons_iso :: "('a => 'a2) => 'a setoid => 'a2 setoid => (('a list => 'b) => 'c2)
     => ('a list => 'b) => ('a2 => 'c2)" where
  "prod_cons_iso f AA AA' g \<equiv> (\<lambda> h x. g (\<lambda> as. h (Cons (s_inv AA AA' f x) as)))"
*)

definition
  arg_swap_iso :: "(('a => 'b => 'c) => 'd) => (('b => 'a => 'c) => 'd)" where
  "arg_swap_iso f = (% h. f (% a b. h b a))"


lemma prod_nil_iso_id:
assumes AA: "setoid AA"
shows "prod_nil_iso id \<in> (sset {[]} ~s~> AA)  ~=~>  AA"
unfolding prod_nil_iso_def id_def iso_s_def apply safe
  apply (metis AA fun_setoid set_setoid)
  apply (rule AA)
  apply (metis carOf_fun_setoid carOf_sset insertI1 sfun_ty)
  apply (metis carOf_sset eqOf_fun_setoid insertI1 sfun_eqD)
  apply (metis carOf_sset eqOf_fun_setoid insertI1 sfun_eqD)
  unfolding carOf_fun_setoid eqOf_fun_setoid sfun_eq_def apply force
proof-
  fix a assume "a \<in> carOf AA"
  thus "\<exists>f\<in>sset {[]} ~> AA. eqOf AA (f []) a"
  apply(intro bexI[of _ "\<lambda> _. a"])
    apply (metis AA srefl)
    by (metis AA sfun_spaciI srefl)
qed


lemma iso_s_comp:
assumes f: "f \<in> AA ~=~> AA'" and f': "f' \<in> AA' ~=~> AA''"
shows "f' o f \<in> AA ~=~> AA''"
proof-
  have AA: "setoid AA" and AA': "setoid AA'" and AA'': "setoid AA''"
  using f f' by (metis iso_sDsetoid)+
  have ff: "f \<in> AA ~> AA'" and ff': "f' \<in> AA' ~> AA''"
  using f f' by (metis iso_sDfunsp)+
  show ?thesis unfolding iso_s_def mem_Collect_eq apply (intro conjI)
    apply (rule AA)
    apply (rule AA'')
    apply(rule comp_sfun[OF ff ff'])
    unfolding comp_def apply(intro ballI)
    apply (metis f f' ff ff' iso_sDinj sfun_elim)
    apply(intro ballI)
    by (smt AA'' f f' ff ff' iso_sDsurj2 sfun_elim strans)
qed
  
lemma comp_prod_nil_iso: "f o prod_nil_iso g = prod_nil_iso (f o g)"
unfolding prod_nil_iso_def by auto

lemma prod_nil_iso_iso:
assumes [MRassm]: "f \<in> AA  ~=~> AA'"
shows "prod_nil_iso f \<in> (sset (product []) ~s~> AA)  ~=~>  AA'"
proof-
  have "prod_nil_iso id \<in> (sset {[]} ~s~> AA)  ~=~>  AA"
  by (metis assms iso_sDsetoid(1) prod_nil_iso_id)
  hence "f o prod_nil_iso id \<in> (sset (product []) ~s~> AA)  ~=~>  AA'"
  by (metis SetoidIsotrans.product_nil assms iso_s_comp)
  thus ?thesis unfolding comp_prod_nil_iso by simp
qed  


lemma comp_iso_s:
assumes BB: "setoid BB" and f: "f \<in> AA ~=~> AA'"
shows "(\<lambda> h. h o f) \<in> (AA' ~s~> BB) ~=~> (AA ~s~> BB)"
apply safe unfolding carOf_fun_setoid eqOf_fun_setoid apply safe
  apply (metis BB f fun_setoid iso_sDsetoid(2))
  apply (metis BB f fun_setoid iso_sDsetoid(1))
  apply (metis f iso_sDfunsp o_def sfun_ty)
  apply (metis f iso_sDfunsp iso_sDwf o_def sfun_ty)
  apply (metis f iso_sDfunsp o_def sfun_ty)
  apply (metis f iso_sDfunsp o_def sfun_ty)
  apply (smt BB f iso_sDfunsp iso_sDsurj2 o_apply sfun_elim ssym strans)
proof-
  fix h assume h1: "\<forall>a. a \<in> carOf AA \<longrightarrow> h a \<in> carOf BB"
  and hs: "\<forall>a a2. a \<in> carOf AA \<longrightarrow> a2 \<in> carOf AA \<longrightarrow> eqOf AA a a2 \<longrightarrow> eqOf BB (h a) (h a2)"
  let ?ff = "s_inv AA AA' f"
  def u \<equiv> "h o ?ff" 
  show "\<exists>u\<in>AA' ~> BB. sfun_eq AA BB (u \<circ> f) h"
  proof(intro bexI[of _ u])
    show "sfun_eq AA BB (u \<circ> f) h"
    unfolding sfun_eq_def u_def comp_def apply safe
    by (metis f hs iso_sDfunsp s_inv_carOf s_inv_eqOf_rev sfun_ty)
  next
    show "u \<in> AA' ~> BB"
    by (smt f h1 hs iso_sDfunsp o_apply s_inv_iso_s sfun_elim sfun_spaciI u_def) 
  qed
qed 

lemma  prod_cons_iso_iso:
assumes 
    f: "f \<in> sset A ~=~> sset A'"
and g: "g : (sset (product As) ~s~> BB) ~=~> CC'"
and BB: "setoid BB"
shows 
"prod_cons_iso f (sset A) (sset A') g : (sset (product (Cons A As)) ~s~> BB)  
                                        ~=~>  
                                        (sset A' ~s~> CC')"
proof-
  let ?AA = "sset A"   let ?AA' = "sset A'"
  let ?PAs = "product As"  let ?PPAs = "sset ?PAs"
  let ?PAAs = "product (Cons A As)" let ?PPAAs = "sset ?PAAs"
  let ?F = "\<lambda> h. h o lfld"
  let ?G = "f : ?AA -> ?AA'   ##>>  g : (?PPAs ~s~> BB) -> CC'" 
  have 0: "prod_cons_iso f (sset A) (sset A') g = ?G o curry o ?F"
  unfolding prod_cons_iso_def splice_def ..
  show ?thesis unfolding 0 apply(intro iso_s_comp)
    apply(rule comp_iso_s[OF BB], rule lfld_setoid_iso_s)
    apply(rule curry_setoid_iso_s, (metis set_setoid BB)+)
    by (metis f g splice_iso_s)
qed

definition "flip xy \<equiv> (snd xy, fst xy)"

lemma flip[simp]: "flip (x,y) \<equiv> (y,x)"
unfolding flip_def by simp

lemma flip_flip[simp]: "flip (flip f) = f" 
unfolding flip_def by simp

lemma flip_o_flip[simp]: "flip o flip = id"
by (rule ext) simp 

lemma flip_setoid: 
"flip \<in> (AA *s BB) ~> (BB *s AA)"
unfolding sfun_def mem_Collect_eq carOf_prod_setoid eqOf_prod_setoid by auto

lemma flip_setoid_iso_s: 
assumes AA: "setoid AA" and BB: "setoid BB"
shows "flip \<in> (AA *s BB) ~=~> (BB *s AA)"
apply(intro iso_s_intro2[of _ _ _ flip])
  apply (metis AA BB setoid_prod_setoid)
  apply (metis AA BB setoid_prod_setoid)
  apply(rule flip_setoid)
  apply(rule flip_setoid)
  unfolding flip_o_flip
  apply (metis AA BB id_def setoid_prod_setoid sfun_eq_def srefl) 
  by (metis AA BB id_def setoid_prod_setoid sfun_eq_def srefl) 

definition "swap f \<equiv> \<lambda> x y. f y x"

lemma swap_flip:
"swap f = curry (split f o flip)"
unfolding swap_def curry_def split_def flip_def by simp

lemma swap_swap[simp]: "swap (swap f) = f" 
unfolding swap_def ..

lemma swap_o_swap[simp]: "swap o swap = id"
by (rule ext) simp 

lemma swap_setoid: 
"swap \<in> (AA ~s~> BB ~s~> CC) ~> (BB ~s~> AA ~s~> CC)"
unfolding sfun_def proof safe
  fix f assume f: "f \<in> carOf (AA ~s~> BB ~s~> CC)"
  show "swap f \<in> carOf (BB ~s~> AA ~s~> CC)"
  unfolding carOf_fun_setoid proof safe
    fix b assume b: "b \<in> carOf BB"
    show "swap f b \<in> carOf (AA ~s~> CC)"
    unfolding carOf_fun_setoid swap_def proof safe
      fix a assume a: "a \<in> carOf AA"
      show "f a b \<in> carOf CC" using f a b by (metis fun_setoid_carOf sfun_elim)
    next
      fix a a2 assume a: "a \<in> carOf AA" and a2: "a2 \<in> carOf AA" and aa2: "eqOf AA a a2"
      hence "eqOf (BB ~s~> CC) (f a) (f a2)" using f
      by (metis fun_setoid_carOf sfun_elim)
      thus "eqOf CC (f a b) (f a2 b)"
      by (metis b fun_setoid_eqOf_eq sfun_eqE)
    qed
  next
    fix b b2 assume b: "b \<in> carOf BB" and b2: "b2 \<in> carOf BB" and b_b2: "eqOf BB b b2"
    thus "eqOf (AA ~s~> CC) (swap f b) (swap f b2)"
    unfolding eqOf_fun_setoid swap_def[abs_def] apply safe
    using f by (metis fun_setoid_carOf sfun_elim)
  qed
next
  fix f f2 assume f: "f \<in> carOf (AA ~s~> BB ~s~> CC)"
  and f2: "f2 \<in> carOf (AA ~s~> BB ~s~> CC)"
  and eq: "eqOf (AA ~s~> BB ~s~> CC) f f2"
  show "eqOf (BB ~s~> AA ~s~> CC) (swap f) (swap f2)"
  unfolding eqOf_fun_setoid apply safe
  unfolding eqOf_fun_setoid swap_def[abs_def] apply safe
  using f by (metis eq eqOf_fun_setoid sfun_eqE) 
qed

lemma swap_setoid_iso_s: 
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC" 
shows "swap \<in> (AA ~s~> BB ~s~> CC) ~=~> (BB ~s~> AA ~s~> CC)"
apply(intro iso_s_intro2[of _ _ _ swap])
  apply (metis AA BB CC fun_setoid)
  apply (metis AA BB CC fun_setoid) 
  apply(rule swap_setoid)
  apply(rule swap_setoid)
  unfolding swap_o_swap  apply safe unfolding id_def
  apply (metis AA BB CC fun_setoid srefl) 
  by  (metis AA BB CC fun_setoid srefl)

lemma arg_swap_iso_swap_o:
"arg_swap_iso f = f o swap"
unfolding swap_def[abs_def] arg_swap_iso_def by auto


lemma arg_swap_iso_swap:
"arg_swap_iso f h = f (swap h)"
unfolding arg_swap_iso_swap_o comp_def ..


lemma arg_swap_sfun: 
assumes f: "f : (AA ~s~> BB ~s~> CC) ~> DD"
shows "arg_swap_iso f : (BB ~s~> AA ~s~> CC) ~> DD"
proof safe
  fix h assume "h \<in> carOf (BB ~s~> AA ~s~> CC)"
  hence "swap h \<in> carOf (AA ~s~> BB ~s~> CC)" by (metis sfun_ty swap_setoid) 
  thus "arg_swap_iso f h \<in> carOf DD"
  unfolding arg_swap_iso_swap using f by (metis sfun_ty) 
next
  fix h h2 assume h: "h \<in> carOf (BB ~s~> AA ~s~> CC)"
  and h2: "h2 \<in> carOf (BB ~s~> AA ~s~> CC)"
  and eq: "eqOf (BB ~s~> AA ~s~> CC) h h2"
  hence "eqOf (AA ~s~> BB ~s~> CC) (swap h) (swap h2)"
  by (metis (no_types) sfun_elim swap_setoid)
  thus "eqOf DD (arg_swap_iso f h) (arg_swap_iso f h2)"
  unfolding arg_swap_iso_swap using f
  by (metis (no_types) eq h h2 sfunDeq sfun_ty swap_setoid)
qed  

lemma arg_swap_iso2[simp]: "arg_swap_iso (arg_swap_iso f) = f" 
unfolding arg_swap_iso_def ..

lemma arg_swap_iso_o[simp]: "arg_swap_iso o arg_swap_iso = id"
by (rule ext) simp 
  

lemma arg_swap_iso:
assumes AA: "setoid AA" and BB: "setoid BB" and CC: "setoid CC"
and f: "f : (AA ~s~> BB ~s~> CC) ~=~> DD"
shows "arg_swap_iso f : (BB ~s~> AA ~s~> CC) ~=~> DD"
unfolding arg_swap_iso_swap_o
by (metis AA BB CC f iso_s_comp swap_setoid_iso_s)


lemma empty_prodapp_isomap:
assumes phi: "phi:  t1 : (sset (product []) ~s~> BB) isomapto t1' : BB'  via prod_nil_iso f"
   and f: "f : BB ~=~> BB' "
shows "phi:  (t1 []) : BB  isomapto  t1' : BB'  via f"
proof-
  have BB: "setoid BB" and BB': "setoid BB'" using f by (metis iso_sDsetoid)+
  show ?thesis
  unfolding isomapto_via_def apply(intro conjI)
    apply (metis SetoidIsotrans.product_nil carOf_fun_setoid carOf_sset 
               isomapto_carOf1 lists.simps lists_empty phi sfun_ty surjective)
    apply (metis isomapto_via_def phi)
    apply(rule BB, rule BB', rule f)
    by (metis isomapto_eqOf phi prod_nil_iso_def)
qed

lemma empty_prodapp2_isomap:
assumes phi: 
"phi:  t1 : (sset (product []) ~s~> sset (product []) ~s~> BB) isomapto t1' : BB'  via prod_nil_iso (prod_nil_iso f)"
   and f: " f : BB ~=~> BB' "
shows "phi:  (t1 [] []) : BB  isomapto  t1' : BB'  via f"
proof-
  have BB: "setoid BB" and BB': "setoid BB'" using f by (metis iso_sDsetoid)+
  show ?thesis
  unfolding isomapto_via_def apply(intro conjI)
    apply (metis SetoidIsotrans.product_nil carOf_fun_setoid carOf_sset 
               isomapto_carOf1 lists.simps lists_empty phi sfun_ty surjective)
    apply (metis isomapto_via_def phi)
    apply(rule BB, rule BB', rule f)
    by (metis isomapto_eqOf phi prod_nil_iso_def)
qed


lemma cons_prodapp_isomap:
assumes
 BB: "setoid BB" and
 BB': "setoid BB'" and 
 raw_t2s: "invariant (t2s, t2s) (sset (product As))"
and phi: 
"phi:  t1 : (sset (product (Cons A As)) ~s~> BB) isomapto t1' : (sset A' ~s~> CC')
      via (prod_cons_iso f (sset A) (sset A') h)" 
and h: "h : (sset (product As) ~s~> BB) ~=~> CC'"
and phi1: 
"phi:  t2 : (sset A)  isomapto  t2' : (sset A')  via f" 
and phi2:
"phi:  ((s_inv (sset (product As) ~s~> BB) CC' h) (t1' t2')) : (sset (product As) ~s~> BB)
        isomapto (t1' t2') : CC'  via h
      \<Longrightarrow> 
 phi:  (s_inv (sset (product As) ~s~> BB) CC' h) (t1' t2') t2s : BB  
        isomapto t' : BB' via g"
shows "phi:  (t1 (Cons t2 t2s)) : BB  isomapto  t' : BB'  via g"
unfolding isomapto_via_def proof(intro conjI)
  let ?AA = "sset A"  let ?PAs = "product As"  let ?PPAs = "sset ?PAs"
  let ?AA' = "sset A'" let ?PAAs = "product (Cons A As)"  let ?PPAAs = "sset ?PAAs"
  let ?hh = "s_inv (?PPAs ~s~> BB) CC' h"
  have t2s: "t2s : product As" by (rule invariant_sset_reflD[OF raw_t2s])
  have CC': "setoid CC'" using h by (metis iso_sDsetoid(2))
  have PPAs: "setoid ?PPAs" using h by (metis set_setoid) 
  have PPAs_BB: "setoid (?PPAs ~s~> BB)" using PPAs BB by (metis fun_setoid) 
  have hh: "?hh \<in> CC' ~=~> (?PPAs ~s~> BB)"
  using h PPAs_BB CC' by (metis s_inv_iso_s) 
  hence hh': "?hh \<in> CC' ~> (?PPAs ~s~> BB)" by (metis iso_sDfunsp)
  have t2: "t2 \<in> A" using phi1 by (metis carOf_sset isomapto_carOf1)
  have t2': "t2' \<in> A'" using phi1 by (metis carOf_sset isomapto_carOf2)
  have t1't2': "t1' t2' \<in> carOf CC'"
  by (metis fun_setoid_carOf_eq isomapto_via_def phi phi1 sfun_elim)
  hence hht1't2': "?hh (t1' t2') \<in> carOf (?PPAs ~s~> BB)"
  unfolding carOf_fun_setoid using hh by (metis fun_setoid_carOf h s_inv_carOf)
  hence hht1't2't2s: "?hh (t1' t2') t2s \<in> carOf BB" using t2s
  by (metis CC' PPAs_BB h isomapto_via_def phi2 s_inv_eqOf t1't2')
  have phi_h: "phi: (?hh (t1' t2')) : (?PPAs ~s~> BB) isomapto (t1' t2') : CC'  via h"
  unfolding isomapto_via_def proof(intro conjI)
    show "eqOf CC' (h (?hh (t1' t2'))) (t1' t2')" by (metis h s_inv_eqOf t1't2')
  qed(insert t1't2' hht1't2' PPAs_BB CC' h, auto)
  hence g: "phi:  ?hh (t1' t2') t2s : BB isomapto t' : BB' via g"
  using phi2 by simp
  thus g_in: "g \<in> BB ~=~> BB'" by (metis isomapto_via_def) 
  hence ghht1't2't2s: "g (?hh (t1' t2') t2s) \<in> carOf BB'"
  using hht1't2't2s by (metis iso_sDfunsp sfun_ty) 
  have t': "t' \<in> carOf BB'" using g unfolding isomapto_via_def by simp
  have "t2 # t2s \<in> product (Cons A As)"  using t2 t2s by simp
  thus t1t2t2s: "t1 (t2 # t2s) \<in> carOf BB"
  by (metis fun_setoid_carOf_eq isomapto_via_def phi sfun_elim simps(1) sset_def)
  hence gt1t2t2s: "g (t1 (t2 # t2s)) \<in> carOf BB'"
  using g_in unfolding isomapto_via_def by (metis iso_sDfunsp sfun_ty)
  show "t' \<in> carOf BB'" by (metis g isomapto_via_def)
  let ?pr = "prod_cons_iso f ?AA ?AA' h"
  have t2'eq: "t2' = f t2" by (metis (full_types) eqOf_sset isomapto_eqOf phi1)
  have t1: "t1 \<in> carOf (?PPAAs ~s~> BB)" using phi unfolding isomapto_via_def by simp
  have "pr": "?pr \<in> (?PPAAs ~s~> BB) ~=~> (?AA' ~s~> CC')"
  using phi unfolding isomapto_via_def by simp
  have "pr": "?pr \<in> (?PPAAs ~s~> BB) ~> (?AA' ~s~> CC')" by (metis "pr" iso_sDfunsp)
  hence pr_t1: "?pr t1 \<in> carOf (?AA' ~s~> CC')"
  using t1 by (metis sfun_ty)
  have t1': "t1' \<in> carOf (?AA' ~s~> CC')" by (metis isomapto_via_def phi)
  have 3: "t1 (t2 # t2s) = curry (t1 o lfld) t2 t2s"  
  unfolding curry_def lfld_def by simp
  have hhprt1t2': "?hh ((?pr t1) t2') \<in> carOf (?PPAs ~s~> BB)"
  using hh' t2' by (metis carOf_sset fun_setoid_carOf_eq pr_t1 sfun_ty)
  have "t1 o lfld \<in> (?AA *s ?PPAs ~> BB)"
  using t1 by (metis carOf_fun_setoid comp_sfun lfld_setoid)
  hence "curry (t1 o lfld) \<in> ?AA ~> (?PPAs ~s~> BB)"
  using curry_setoid by (metis BB fun_setoid_carOf_eq set_setoid sfun_ty) 
  hence curryt1lfldt2: "curry (t1 o lfld) t2 \<in> carOf (?PPAs ~s~> BB)" 
  using t2 by (metis isomapto_carOf1 phi1 sfun_ty)  
  have 0: "eqOf (?AA' ~s~> CC') (?pr t1) t1'"
  using phi unfolding isomapto_via_def by simp
  hence "eqOf (?AA' ~s~> CC') t1' (?pr t1)" using t1' pr_t1
  by (metis CC' fun_setoid set_setoid ssym)
  hence "eqOf CC' (t1' t2') ((?pr t1) t2')"
  by (metis carOf_sset fun_setoid_eqOf_eq sfun_eqD t2')
  hence "eqOf (?PPAs ~s~> BB) (?hh (t1' t2')) (?hh ((?pr t1) t2'))"
  using hh'
  by (metis (no_types) carOf_sset fun_setoid_carOf_eq hh iso_sDwf pr_t1 
            sfun_elim t1't2' t2')
  moreover 
  {def hh \<equiv> ?hh
   def ff \<equiv> "s_inv ?AA ?AA' f"
   have "eqOf ?AA (ff (f t2)) t2" using t2 unfolding ff_def
   by (metis carOf_sset isomapto_iso_s phi1 s_inv_eqOf_rev)
   hence ffft2: "ff (f t2) = t2" by (metis (full_types) eqOf_sset)
   have "eqOf (?PPAs ~s~> BB) (?hh (?pr t1 t2')) (curry (t1 o lfld) t2)"
   unfolding prod_cons_iso_def
   unfolding hh_def[symmetric] ff_def[symmetric] t2'eq curry_def comp_def
   unfolding eqOf_fun_setoid ffft2 proof safe
     fix as assume as: "as \<in> carOf ?PPAs"    
     let ?g = "\<lambda>as. t1 (lfld (t2, as))"
     have g: "?g \<in> carOf (?PPAs ~s~> BB)"
     unfolding carOf_fun_setoid lfld_def  apply safe
     unfolding carOf_sset  using t1 t2 apply force
     unfolding eqOf_sset using t1 t2 by force
     hence "eqOf (?PPAs ~s~> BB) (hh (h ?g)) ?g"
     using h unfolding hh_def by (metis s_inv_eqOf_rev)
     thus "eqOf BB (hh (h ?g) as) (?g as)" 
     using as unfolding eqOf_fun_setoid by auto
   qed
  }    
  ultimately have "eqOf (?PPAs ~s~> BB) (?hh (t1' t2')) (curry (t1 o lfld) t2)"
  using strans[OF PPAs_BB hht1't2' hhprt1t2' curryt1lfldt2] by auto
  hence "eqOf BB (?hh (t1' t2') t2s) (t1 (t2 # t2s))" 
  unfolding 3 eqOf_fun_setoid using t2s by auto
  hence "eqOf BB' (g (t1 (t2 # t2s))) (g (?hh (t1' t2') t2s))"
  using g unfolding isomapto_via_def by (metis t1t2t2s iso_sDwf ssym)
  moreover have "eqOf BB' (g (?hh (t1' t2') t2s)) t'"
  using g unfolding isomapto_via_def by simp
  ultimately show "eqOf BB' (g (t1 (t2 # t2s))) t'" 
  using BB' using strans[OF BB' gt1t2t2s ghht1't2't2s t'] by auto
qed(insert BB BB', auto)





(* setoid isotrans animation *)

definition 
  isotovia_const :: "'a setoid => isomark => 'b setoid => ('a => 'b) => bool"  where
  [MRjud 2 2]: "isotovia_const AA phi AA' f == (f : AA ~=~> AA')"

abbreviation
  isotovia_abbrev ("_: _ isoto _ via _") where
  "(phi: AA isoto AA' via f) == isotovia_const AA phi AA' f"

lemma [MRjud 2 4]: "isomapto_via t phi AA t' AA' f == isomapto_via t phi AA t' AA' f" by simp

lemma isotoE[elim]: "phi: BB isoto BB' via g ==> (setoid BB ==> setoid BB' ==> g : BB ~=~> BB' ==> P) ==> P "
  apply (simp add: isotovia_const_def) by (blast intro: iso_sDsetoid)



(* already declared as MR rules *)
lemma "
  setoid UNIV_s  " by (rule UNIV_setoid)

lemma "[|  setoid AA  ;  setoid BB  |] ==>
  setoid (AA ~s~> BB)  " by (rule fun_setoid)




lemma isoto_funsetoid[MR]: "[|
    phi: AA isoto AA' via f  ;
    phi: BB isoto BB' via g  |] ==>
  phi: (AA ~s~> BB) isoto (AA' ~s~> BB') via (f : AA -> AA'  ##>>  g : BB -> BB') "
    unfolding isotovia_const_def by(rule splice_iso_s)

lemma isoto_UNIV_s[MR]: "
  phi: (UNIV_s :: bool setoid) isoto UNIV_s via id  "
     by (simp add: isotovia_const_def id_UNIV_iso_s)





lemma [MR]: "[|
    phi:  t1 : (AA ~s~> BB)  isomapto  t1' : (AA' ~s~> BB') 
      via (f : AA -> AA'  ##>>  g : BB -> BB')  ;
    phi:  BB  isoto  BB'  via g  ;
    phi:  t2 : AA  isomapto  t2' : AA'  via f  |] ==>
  phi:  (t1 t2) : BB  isomapto  (t1' t2') : BB'  via g  "
   apply (erule isotoE)
   by (rule isomapto_app)

(* TODO: premise   BB isoto BB' via g   is not necessary:
    * if AA is nonempty, use the assumption that transforms (t x)
    * if AA is empty, so is AA' and (f ##>> g) : (AA ~> BB) ~=~> (AA' ~> BB') is trivial
     because the equivalence relations on  AA ~s~> BB  and  AA' ~s~> BB'  are trivial
       (and  AA' ~s~> BB'  is always a setoid if AA' is empty) *)
lemma [MR]: "[|
    phi:  AA isoto AA' via f  ;
    !! x x2.  [|  invariant (x, x) AA  ; invariant (x2, x2) AA  ;  invariant (x, x2) AA  |] ==>
      invariant (t x, t x2) BB ;
    !! x x'.  [|  phi:  x : AA  isomapto  x' : AA'  via f  ;  invariant (x, x) AA  |]   ==>
         phi:  (t x) : BB  isomapto  (t' x') : BB'  via g  ;
    phi:  BB isoto BB' via g  |] ==>
  phi:  (slam x \<in> AA. t x) : AA ~s~> BB  isomapto  
        (slam x' \<in> AA'. t' x') : (AA' ~s~> BB')
        via (f : AA -> AA'  ##>>  g : BB -> BB') "
   unfolding isotovia_const_def invariant_def 
   apply (rule slam_isomapto) apply simp apply auto
   apply (drule iso_sDsetoid(1))
   apply (blast intro: setoid_refl)
   unfolding isomapto_via_def by (blast intro: setoid_refl)





lemma [MR]: " [|
   phi:  (setoid_lam AA P) : (AA ~s~> UNIV_s)  isomapto  (setoid_lam AA' P') : (AA' ~s~> UNIV_s)
     via (f : AA -> AA'  ##>>  id : UNIV_s -> UNIV_s)  ;
   phi: AA isoto AA' via f  |] ==>
  phi:  (setoid_all AA P) : UNIV_s  isomapto  (setoid_all AA' P') : UNIV_s  via id  "
unfolding isomapto_via_def carOf_UNIV_s apply(intro conjI)
  apply (metis UNIV_I)
  apply (metis UNIV_I)
  apply (metis UNIV_setoid)
  apply (metis UNIV_setoid)
  apply (metis id_UNIV_iso_s)
  unfolding eqOf_sset id_def setoid_all_def
by sorry2


lemma [MR]:  "  phi:  AA isoto AA' via f ==>
  phi:  (eqOf AA) : (AA ~s~> AA ~s~> UNIV_s) isomapto  (eqOf AA') : (AA' ~s~> AA' ~s~> UNIV_s)
    via (f : AA -> AA'  ##>>  (f : AA -> AA'  ##>>  id : UNIV_s -> UNIV_s)
                                : (AA ~s~> UNIV_s) -> (AA' ~s~> UNIV_s))  "
by sorry2


lemma [MR]: "
  phi:  (op -->) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)   isomapto   
   (op -->) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)
   via (id : UNIV_s -> UNIV_s  ##>>  (id : UNIV_s -> UNIV_s ##>> id : UNIV_s -> UNIV_s)
           : (UNIV_s ~s~> UNIV_s) -> (UNIV_s ~s~> UNIV_s))  "
by sorry2

lemma [MR]: "
  phi:  (op &) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)   isomapto   
   (op &) : (UNIV_s ~s~> UNIV_s ~s~> UNIV_s)
   via (id : UNIV_s -> UNIV_s  ##>>  (id : UNIV_s -> UNIV_s ##>> id : UNIV_s -> UNIV_s)
           : (UNIV_s ~s~> UNIV_s) -> (UNIV_s ~s~> UNIV_s))  "  
by sorry2



definition
  pNil :: "'a list" where
  "pNil = Nil"

(* "pair" cons inhabits products given by the annotation  A, As  *)
definition
  pCons :: "'a set => ('a set) list => 'a => 'a list => 'a list" where
  "pCons A As x xs = Cons x xs"

lemma [MR]: "
  invariant (pCons A As, pCons A As) (sset A ~s~> sset (product As) ~s~> sset (product (Cons A As)))  "
  apply (rule invariant_reflI)  apply simp+ by (auto simp add: pCons_def)
lemma [MR]: "
  invariant ((pNil :: 'a list), (pNil :: 'a list)) (sset (product ([] :: ('a set) list)))  "
  apply (rule invariant_reflI) by (simp add: pNil_def)+



 (* userar is used to communicate the argument permutation for each operation to the isoto judgement *)
 (* if uar = None we use the default rules for curry_iso above *)
datatype arity_choice = Param | Intern
type_synonym userar = "arity_choice list"
definition
  curry_iso :: "userar option => isomark => isomark" where
  "curry_iso uar base_iso = isomark 0"

definition
  userar_decl :: "'a => userar => bool" where
  [MRjud 1 1]: "userar_decl t uar == True"

(* needed to identify applications of binary operators on products,
   which are curried specially, with possible argument permutations *)
definition
  is_ptuple :: "'a => bool" where
  [MRjud 1 0]: "is_ptuple t == True"
lemma is_ptupleI[intro]: "is_ptuple t" by (simp add: is_ptuple_def)

lemma [MR]: "
  is_ptuple pNil  " ..
lemma [MR]: "
  is_ptuple (pCons A As t ts)   " ..


lemma [MR -1]: "
    base_iso:  AA  isoto  AA'  via f  ==>
  (curry_iso None base_iso):  AA  isoto  AA'  via f  "
  unfolding isotovia_const_def . 

lemma isoto_prod_nil[MR]: "(curry_iso None base_iso):  BB isoto (BB' :: 'b2 setoid) via g  ==>
  (curry_iso None base_iso):  (sset (product ([] :: 'a set list)) ~s~> (BB :: 'b setoid))  isoto BB'
    via ((prod_nil_iso g) :: ('a list => 'b) => 'b2)  "
  unfolding isotovia_const_def by (rule prod_nil_iso_iso)


lemma isoto_prod_cons[MR]: "[|
    base_iso:  (sset A) isoto (sset A') via f  ;
    (curry_iso None base_iso):  (sset (product As) ~s~> BB)  isoto  CC' via g  ;
    setoid BB  |] ==>
  (curry_iso None base_iso):  (sset (product (Cons A As)) ~s~> BB)  isoto  (sset A' ~s~> CC')
    via (prod_cons_iso f (sset A) (sset A') g)  "
  unfolding isotovia_const_def using prod_cons_iso_iso by simp


lemma [MR -1]: "
    base_iso:  x : AA  isomapto  x' : AA'  via f  ==>
  (curry_iso None base_iso):  x : AA  isomapto  x' :  AA'  via f  "
  unfolding isomapto_via_def . 

lemma [MR]: "[|  
    (curry_iso None base_iso):  t1 : (sset (product []) ~s~> BB) isomapto t1' : BB'  via prod_nil_iso f  ;
    base_iso:  BB isoto BB' via f  |] ==>
  (curry_iso None base_iso):  (t1 pNil) : BB  isomapto  t1' : BB'  via f  "
    unfolding isotovia_const_def pNil_def by (rule empty_prodapp_isomap)

lemma [MR]: "[|
    invariant (t2s, t2s) (sset (product As))  ;
    (curry_iso None base_iso):  t1 : (sset (product (Cons A As)) ~s~> BB)  isomapto
      t1' : (sset A' ~s~> CC')  via (prod_cons_iso f (sset A) (sset A') h)  ;
    setoid BB  ;
    (curry_iso None base_iso):  (sset (product As) ~s~> BB)  isoto  CC'  via h  ;
    (curry_iso None base_iso):  t2 : (sset A)  isomapto  t2' : (sset A')  via f  ;
    (curry_iso None base_iso):  ((s_inv (sset (product As) ~s~> BB) CC' h) (t1' t2')) : (sset (product As) ~s~> BB)
          isomapto  (t1' t2') : CC'  via h ==>
      (curry_iso None base_iso):  (s_inv (sset (product As) ~s~> BB) CC' h) (t1' t2') t2s : BB  
            isomapto  t' : BB'  via g;
    setoid BB'  |] ==>
  (curry_iso None base_iso):  (t1 (pCons A As t2 t2s)) : BB  isomapto  t' : BB'  via g  "
unfolding isotovia_const_def pCons_def
using cons_prodapp_isomap
by metis



lemma isoto_prod_nil1[MR]: "base_iso:  BB isoto BB' via g  ==>
  (curry_iso (Some []) base_iso):  (sset (product []) ~s~> sset (product []) ~s~> BB)  isoto BB'
    via (prod_nil_iso (prod_nil_iso g)) "
  by sorry2

lemma isoto_prod_param_cons[MR]: "[|
    base_iso:  (sset A) isoto (sset A') via f  ;
    (curry_iso (Some uar) base_iso):  (sset (product As) ~s~> BB ~s~> CC)  isoto  DD' via g;
    setoid BB  ;  setoid CC  |] ==>
  (curry_iso (Some (Param # uar)) base_iso):  (sset (product (Cons A As)) ~s~> BB ~s~> CC)  isoto  (sset A' ~s~> DD')
    via (prod_cons_iso f (sset A) (sset A') g)  "
  unfolding isotovia_const_def using prod_cons_iso_iso by (metis fun_setoid) 

lemma isoto_prod_intern_cons[MR]: "[|
    base_iso:  (sset B) isoto (sset B') via f  ;
    (curry_iso (Some uar) base_iso):  (AA ~s~> sset (product Bs) ~s~> CC)  isoto  DD' via g  ;
    setoid AA  ;  setoid CC  |] ==>
  (curry_iso (Some (Intern # uar)) base_iso):  (AA ~s~> sset (product (Cons B Bs)) ~s~> CC)  isoto  (sset B' ~s~> DD')
    via (arg_swap_iso (prod_cons_iso f (sset B) (sset B') (arg_swap_iso g)))  "
  by sorry2



lemma [MR]: "[|  
     (curry_iso uar_opt base_iso):  t1 : (sset (product []) ~s~> sset (product []) ~s~> CC)
       isomapto t1' : CC'  via prod_nil_iso (prod_nil_iso f)  ;
     base_iso: CC isoto CC' via f  ;
     (curry_iso None base_iso):  CC isoto CC' via f  |] ==>
  (curry_iso uar_opt base_iso):  (t1 pNil pNil) : CC  isomapto  t1' : CC'  via f  "
    unfolding isotovia_const_def pNil_def by (rule empty_prodapp2_isomap)

lemma [MR]: "[|
    try(  is_ptuple t2  )  ;
    invariant (t3s, t3s) (sset (product Bs))  ;
    userar_decl t1 (Intern # uar') ;
    (curry_iso None base_iso):  t1 : (AA ~s~> sset (product (Cons B Bs)) ~s~> CC)  isomapto
      t1' : (sset B' ~s~> DD')  via (arg_swap_iso (prod_cons_iso f (sset B) (sset B') (arg_swap_iso h)))  ;
    setoid AA  ;  setoid CC  ;
    (curry_iso (Some uar') base_iso):  (AA ~s~> sset (product Bs) ~s~> CC)  isoto  DD'  via h  ;
    (curry_iso None base_iso):  t3 : (sset B)  isomapto  t3' : (sset B')  via f  ;
    [|  (curry_iso None base_iso):
          ((s_inv (AA ~s~> sset (product Bs) ~s~> CC) DD' h) (t1' t3')) : (AA ~s~> sset (product Bs) ~s~> CC)
          isomapto  (t1' t3') : DD'  via h  ;
        userar_decl ((s_inv (AA ~s~> sset (product Bs) ~s~> CC) DD' h) (t1' t3')) uar' |] ==>
      (curry_iso None base_iso):  (s_inv (AA ~s~> sset (product Bs) ~s~> CC) DD' h) (t1' t3') t2 t3s : CC  
            isomapto  t' : CC'  via g  |] ==>
  (curry_iso None base_iso):  (t1 t2 (pCons B Bs t3 t3s)) : CC  isomapto  t' : CC'  via g  "
unfolding isotovia_const_def pCons_def
by sorry2

lemma [MR]: "[|
    try(  is_ptuple t3  )  ;
    invariant (t2s, t2s) (sset (product As))  ;
    try(  userar_decl t1 (Param # uar')  )  ;
    (curry_iso None base_iso):  t1 : (sset (product (Cons A As)) ~s~> BB ~s~> CC)  isomapto
      t1' : (sset A' ~s~> DD')  via (prod_cons_iso f (sset A) (sset A') h)  ;
    setoid BB  ;  setoid CC  ;
    (curry_iso (Some uar') base_iso):  (sset (product As) ~s~> BB ~s~> CC)  isoto  DD'  via h  ;
    (curry_iso None base_iso):  t2 : (sset A)  isomapto  t2' : (sset A')  via f  ;
    [|  (curry_iso None base_iso):
          ((s_inv (sset (product As) ~s~> BB ~s~> CC) DD' h) (t1' t2')) : (sset (product As) ~s~> BB ~s~> CC)
          isomapto  (t1' t2') : DD'  via h  ;
        userar_decl ((s_inv (sset (product As) ~s~> BB ~s~> CC) DD' h) (t1' t2')) uar' |] ==>
      (curry_iso None base_iso):  (s_inv (sset (product As) ~s~> BB ~s~> CC) DD' h) (t1' t2') t2s t3 : CC 
            isomapto  t' : CC'  via g  |] ==>
  (curry_iso None base_iso):  (t1 (pCons A As t2 t2s) t3) : CC  isomapto  t' : CC'  via g  "
unfolding isotovia_const_def pCons_def try_const_def
apply (simp add: userar_decl_def del: product.simps)
by sorry2







(* tests *)


schematic_lemma
  assumes [MRassm]: "base_iso:  (sset (A :: 'a set)) isoto (sset (A' :: 'a2 set)) via f"
  and [MRassm]: "base_iso:  (sset B) isoto (sset B') via g"
  shows "(curry_iso None base_iso):  (sset (product [(A :: 'a set)]) ~s~> sset (B :: 'b set)) isoto
    (?AA' :: ('a2 => ?'c2) setoid)  via (?h :: ('a list => 'b) => ('a2 => ?'c2))"
  by (tactic {*  MetaRec.metarec_tac_debug @{context} 1 *})


definition
  "myiso = isomark 0"

schematic_lemma
  assumes [MRassm]: "setoid EE" and [MRassm]: "setoid EE'"
  and [MRassm]: "myiso:  (sset A) isoto (sset A') via fA"
  and [MRassm]: "myiso: (sset B) isoto (sset B') via fB"
  and [MRassm]: "myiso: (sset C) isoto (sset C') via fC"
  and [MRassm]: "myiso: (sset D) isoto (sset D') via fD"
  and [MRassm]: "myiso: EE isoto EE' via fE"
  and [MRassm]: "invariant (i, i)  (sset (product [A,B,C,D]) ~s~> EE)"
  and [MRassm]: "(curry_iso None myiso):  i : (sset (product [A,B,C,D]) ~s~> EE) isomapto
    i' : (sset A' ~s~> sset B' ~s~> sset C' ~s~> sset D' ~s~> EE')
    via (prod_cons_iso fA (sset A) (sset A') (prod_cons_iso fB (sset B) (sset B')
     (prod_cons_iso fC (sset C) (sset C')
       (prod_cons_iso fD (sset D) (sset D') (prod_nil_iso fE)))))"
  and [MRassm]: "invariant (a, a) (sset A)"
  and [MRassm]: "invariant (a', a') (sset A')"
  and [MRassm]: "myiso:  a : (sset A)  isomapto  a' : (sset A')  via fA"
  shows "(curry_iso None myiso):  (SALL xA : sset A. SALL xB : sset B. SALL xC : sset C. SALL xD : sset D.
       eqOf (sset A) a a -->
       eqOf EE (i (pCons A [B,C,D] xA (pCons B [C,D] xB (pCons C [D] xC (pCons D [] xD pNil)))))
               (i (pCons A [B,C,D] xA (pCons B [C,D] xB (pCons C [D] xC (pCons D [] xD pNil))))))
       : UNIV_s
     isomapto ?P' : UNIV_s via id "
  by (tactic {*  MetaRec.metarec_tac_debug @{context} 1 *})



schematic_lemma
  assumes [MRassm]: "setoid EE" and [MRassm]: "setoid EE'"
  and [MRassm]: "myiso:  (sset A) isoto (sset A') via fA"
  and [MRassm]: "myiso: (sset B) isoto (sset B') via fB"
  and [MRassm]: "myiso: (sset C) isoto (sset C') via fC"
  and [MRassm]: "myiso: (sset D) isoto (sset D') via fD"
  and [MRassm]: "myiso: EE isoto EE' via fE"
  shows "(curry_iso (Some [Param, Intern, Param, Param]) myiso): (sset (product [A,B,C]) ~s~> sset (product [D]) ~s~> EE)
     isoto (?FF :: ?'a setoid) via ?h "
  by (tactic {*  MetaRec.metarec_tac_debug @{context} 1 *})
  

schematic_lemma
  assumes [MRassm]: "setoid EE" and [MRassm]: "setoid EE'"
  and [MRassm]: "myiso:  (sset A) isoto (sset A') via fA"
  and [MRassm]: "myiso: (sset B) isoto (sset B') via fB"
  and [MRassm]: "myiso: (sset C) isoto (sset C') via fC"
  and [MRassm]: "myiso: (sset D) isoto (sset D') via fD"
  and [MRassm]: "myiso: EE isoto EE' via fE"
  and [MRassm]: "invariant (i, i)  (sset (product [A,B,C]) ~s~> sset (product [D]) ~s~> EE)"
  and [MRassm]: "userar_decl i [Param, Intern, Param, Param]"
  and [MRassm]: "(curry_iso None myiso):  i : (sset (product [A,B,C]) ~s~> sset (product [D]) ~s~> EE) isomapto
    i' : (sset A' ~s~> sset D' ~s~> sset B' ~s~> sset C' ~s~> EE')
    via (prod_cons_iso fA (sset A) (sset A') (arg_swap_iso (prod_cons_iso fD (sset D) (sset D') (arg_swap_iso (
      prod_cons_iso fB (sset B) (sset B') (prod_cons_iso fC (sset C) (sset C') (prod_nil_iso (prod_nil_iso fE))))))))"
  and [MRassm]: "invariant (a, a) (sset A)"
  and [MRassm]: "invariant (a', a') (sset A')"
  and [MRassm]: "myiso:  a : (sset A)  isomapto  a' : (sset A')  via fA"
  shows "(curry_iso None myiso):  (SALL xA : sset A. SALL xB : sset B. SALL xC : sset C. SALL xD : sset D.
       eqOf (sset A) a a -->
       eqOf EE (i (pCons A [B,C] xA (pCons B [C] xB (pCons C [] xC pNil))) (pCons D [] xD pNil))
               (i (pCons A [B,C] xA (pCons B [C] xB (pCons C [] xC pNil))) (pCons D [] xD pNil)))
       : UNIV_s
     isomapto ?P' : UNIV_s via id "
  by (tactic {*  MetaRec.metarec_tac_debug @{context} 1 *})



end

