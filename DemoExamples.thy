theory DemoExamples
imports NonFreeInput
begin


(* trees with a finite set of subtrees *)
nonfreedata   'a tree = Tree "'a" "'a tfset"
        and  'a tfset = Emp | Ins "'a tree" "'a tfset"
where
  Ins1: "Ins a (Ins a s) = Ins a s"
| Ins2: "Ins a1 (Ins a2 s) = Ins a2 (Ins a1 s)"

nonfreeiter treemap tfsetmap
where
  "treemap f (Tree a s) = Tree (f a) (tfsetmap f s)"
| "tfsetmap f Emp = Emp"
| "tfsetmap f (Ins t s) = Ins (treemap f t) (tfsetmap f s)"
by (simp add: Ins1 Ins2)+  (* discharging well-definedness *)
  (*  [| Tree |] := (% a s'. Tree (f a) s'),  [| Emp |] := Emp,  [| Ins |] := Ins *)

lemma "treemap g (treemap f t) = treemap (g o f) t"
      "tfsetmap g (tfsetmap f s) = tfsetmap (g o f) s"
apply (induct t and s)
by simp+

lemma "treemap f (Tree a (Ins t1 (Ins t2 s))) = treemap f (Tree a (Ins t2 (Ins t1 s)))"
by (simp add: Ins2)

lemma "treemap f (Tree a (Ins t (Ins t s))) = treemap f (Tree a (Ins t s))"
by (simp add: Ins1)








type_synonym var = nat

(* neq is used as a "parameter condition" on variables.
   Not defined inductively by Horn theory, but with fixed semantics. *)
definition
  neq where
  "neq x y == x ~= y"

(* lambda terms modulo alpha, with explicit substitution *)
nonfreedata lamterms =
    V "var" | Ap "lamterms" "lamterms" | Lm "var" "lamterms"
  | Subst "lamterms" "lamterms" "var" (* Subst X Y z = X[Y/z] *)
where
  Subst1: "Subst (V x) X x = X"
| Subst2: "neq x y ==> Subst (V x) Y y = V x"
| Subst3: "Subst (Ap X Y) Z z = Ap (Subst X Z z) (Subst Y Z z)"
| Subst4: "[| neq x y ; fresh x Y  |] ==> Subst (Lm x X) Y y = Lm x (Subst X Y y)" (* "lazily defined" *)
| fresh1: "neq x y ==> fresh x (V y)"
| fresh2: "[| fresh x Y ; fresh x Z |] ==> fresh x (Ap Y Z)"
| fresh3: "fresh x (Lm x X)"
| fresh4: "fresh x Y ==> fresh x (Lm y Y)"
| alpha:  "[| neq y x ; fresh y X |] ==> Lm x X = Lm y (Subst X (V y) x)"


(* Count number of occurrences of a variable in a lamterm.
   More precisely: construct occurence counter for given lamterm.
   Note: variable to be counted changes in rec. calls!
   Not a parameter of iter definition. *)
nonfreeiter
  numoccs :: "lamterms => (var => nat)"
where
  "numoccs (V x) = (% z.      if x = z then 1 else 0)"
| "numoccs (Ap X Y)  = (% z.  numoccs X z + numoccs Y z)"
| "numoccs (Lm x X) = (% z.   if x = z then 0 else numoccs X z)"
| "numoccs (Subst X Y y) = (% z.
     if y = z then numoccs X y * numoccs Y z
     else numoccs X z + numoccs X y * numoccs Y z)"
| "fresh interpretedas (% x (occs :: var => nat). occs x = 0)"
  apply (rule ext, simp add: neq_def Nat.add_mult_distrib)+
  apply auto
  apply (rule ext, simp add: neq_def)+
  by (auto simp add: neq_def Nat.add_mult_distrib)

lemma "neq y x ==> fresh y X ==> numoccs (Lm x X) z = numoccs (Lm y (Subst X (V y) x)) z"
  by (simp add: alpha)

lemma "fresh x X ==> numoccs X x = 0"
  by simp



end
