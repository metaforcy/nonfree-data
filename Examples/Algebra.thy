theory Algebra
imports Prelim
begin

fun is_times where "is_times a1 a2 a \<longleftrightarrow> a1 * a2 = a"
fun is_times1 where "is_times1 a1 a2 a \<longleftrightarrow> a1 * a2 = a"
fun is_plus where "is_plus a1 a2 a \<longleftrightarrow> a1 + a2 = a"
fun is_uminus where "is_uminus a b \<longleftrightarrow> - a = b"
fun is_zero where "is_zero a \<longleftrightarrow> a = 0"

lemmas is_defs = is_times.simps is_times1.simps is_plus.simps is_uminus.simps is_zero.simps


(* Sum of semigroups *)
nonfree_datatype ('a::semigroup_mult, 'b::semigroup_mult) ssum
  = Left 'a | Right 'b | Mult "('a, 'b) ssum" "('a, 'b) ssum"
where
  LeftPlus: "is_times a1 a2 a \<Longrightarrow> Mult (Left a1) (Left a2) = Left a"
 |RightPlus: "is_times1 b1 b2 b \<Longrightarrow> Mult (Right b1) (Right b2) = Right b"
 |Mult: "Mult (Mult x y) z = Mult x (Mult y z)"

instantiation ssum :: (semigroup_mult, semigroup_mult) semigroup_mult
begin
definition times_ssum where "x * y \<equiv> Mult x y"
instance apply default using Mult unfolding times_ssum_def by auto
end

(* Universal function for sums: *)
context
  fixes f :: "'a::semigroup_mult \<Rightarrow> 'c::semigroup_mult"
    and g :: "'b::semigroup_mult \<Rightarrow> 'c"
  assumes (* f and g are morphisms of semigroups *)
   f_times: "f (a1 * a2) = f a1 * f a2" and
   g_times: "g (b1 * b2) = g b1 * g b2"
begin

nonfree_primrec
suniv :: "('a, 'b) ssum \<Rightarrow> 'c"
where
  "suniv (Left a) = f a"
| "suniv (Right b) = g b"
| "suniv (Mult x y) = suniv x * suniv y"
by (auto simp: algebra_simps  f_times g_times)

end (* context *)


(* The ring of polynomials *)
nonfree_datatype ('a::comm_ring, 'b) poly
  = Sc 'a | Var 'b | Uminus "('a,'b) poly" | 
    Plus "('a,'b) poly" "('a,'b) poly" | Times "('a,'b) poly" "('a,'b) poly"
where
  ScUminus: "is_uminus a b \<Longrightarrow> Uminus (Sc a) = Sc b"
 |ScPlus: "is_plus a1 a2 a \<Longrightarrow> Plus (Sc a1) (Sc a2) = Sc a"
 |ScTimes: "is_times a1 a2 a \<Longrightarrow> Times (Sc a1) (Sc a2) = Sc a"
 |PlusAssoc: "Plus (Plus P1 P2) P3 = Plus P1 (Plus P2 P3)"
 |PlusComm: "Plus P1 P2 = Plus P2 P1"
 |ZeroPlus: "is_zero a \<Longrightarrow> Plus (Sc a) P = P"
 |UminusPlus: "is_zero a \<Longrightarrow> Plus (Uminus P) P = Sc a"
 |TimesAssoc: "Times (Times P1 P2) P3 = Times P1 (Times P2 P3)"
 |TimesComm: "Times P1 P2 = Times P2 P1"
 |Distr: "Times (Plus P Q) R = Plus (Times P R) (Times Q R)"

lemmas poly_facts = ScUminus ScPlus ScTimes PlusAssoc PlusComm ZeroPlus UminusPlus TimesAssoc TimesComm Distr

(* Polynomials in the commutative-ring type class: *)
instantiation poly :: (comm_ring, type) comm_ring
begin
definition minus_poly where "P - Q = Plus P (Uminus Q)"
definition uminus_poly where "- P = Uminus P"
definition plus_poly where "P + Q = Plus P Q"
definition times_poly where "P * Q = Times P Q"
definition zero_poly where "0 = Sc 0"
instance apply default
unfolding minus_poly_def uminus_poly_def plus_poly_def times_poly_def zero_poly_def
by (metis poly_facts is_defs)+
end


(* Universal function for polynomials: *)
context
  fixes f :: "'a::comm_ring_1 \<Rightarrow>'c::comm_ring_1"
  and g :: "'b => 'c"
  assumes 
   f_zero: "f 0 = 0" and
   f_one: "f 1 = 1" and
   f_uminus: "f (- a) = - f a" and
   f_plus: "f (a1 + a2) = f a1 + f a2" and
   f_times: "f (a1 * a2) = f a1 * f a2"
begin

nonfree_primrec
ext :: "('a,'b) poly \<Rightarrow> 'c"
where
  "ext (Sc a) = f a"
| "ext (Var b) = g b"
| "ext (Uminus P) = - ext P"
| "ext (Plus P Q) = ext P + ext Q"
| "ext (Times P Q) = ext P * ext Q"
by (auto simp: algebra_simps f_zero f_one f_uminus f_plus f_times)

end (* context *)

(* Polynomial valuation: *)
definition "pval \<equiv> ext id"

lemma pval_simps[simp]:
  "pval g (Sc a) = a"
  "pval g (Var b) = g b"
  "pval g (Uminus P) = - pval g P"
  "pval g (Plus P Q) = pval g P + pval g Q"
  "pval g (Times P Q) = pval g P * pval g Q"
unfolding pval_def by auto


end
