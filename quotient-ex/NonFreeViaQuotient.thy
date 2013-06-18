theory NonFreeViaQuotient
imports Main
begin

(* interpretation for 
    nonfreedatatype 'a set := Empty | Insert 'a ('a set)
    where  Insert i (Insert j s) = Insert j (Insert i s)
*)


(* quotienting von einem Free datatype um den non-free datatype
   zu erhalten geht gerade noch so *)
datatype 'a pset = pEmpty | pInsert 'a "'a pset"

inductive
  pset_equi :: "'a pset => 'a pset => bool"
where
  equi_refl: "pset_equi x x"
| equi_base: "pset_equi (pInsert i (pInsert j s)) (pInsert j (pInsert i s))"
| equi_cong: "pset_equi x y ==> pset_equi (pInsert i x) (pInsert i y)"
| equi_trans: "pset_equi x y ==> pset_equi y z ==> pset_equi x z"
| equi_symm: "pset_equi x y ==> pset_equi y x"

quotient_type 'a set = "'a pset" / pset_equi
  unfolding equivp_def sorry (* pset_equi is an equivalence relation *)

primrec
  psetrec :: "'b => ('a => 'b => 'b) => 'a pset => 'b"
where
  psetrec_base:  "psetrec b f pEmpty = b"
| psetrec_step: "psetrec b f (pInsert a s) = f a (psetrec b f s)"

(* die invarianzbedingung an f ist hier wesentlich schwaecher (aber extensional gleichstark)
   wie die Definition von pset_equi und entspricht nur dem equi_base Fall *)
lemma psetrec_inv: assumes H: "pset_equi s s2" and finv: "(ALL i j. f i (f j s) = f j (f i s))"
  shows "psetrec b f s = psetrec b f s2"
apply (rule pset_equi.induct[OF H])
apply (auto intro: finv)
sorry


quotient_definition
  "Empty :: 'a set"
is "pEmpty :: 'a pset"
quotient_definition
  "Insert :: 'a => 'a set => 'a set"
is "pInsert :: 'a => 'a pset => 'a pset"

thm pset.induct
lemma set_induct: "[| P Empty; !!a s. P s ==> P (Insert a s) |] ==> P s"
apply (lifting pset.induct)
unfolding fun_rel_def
by (auto intro: equi_cong)

quotient_definition
  "setrec :: 'b => ('a => 'b => 'b) => 'a set => 'b"
is "psetrec :: 'b => ('a => 'b => 'b) => 'a pset => 'b"

(* type annotation on f needed to get exactly the corresponding types of psetrec_base *)
lemma setrec_base: "setrec b (f :: 'a => 'b => 'b) Empty = b"
apply (lifting psetrec_base)
unfolding fun_rel_def
apply (auto intro: equi_cong equi_refl)
sorry (* apply (rule psetrec_inv) *)

lemma setrec_step: "setrec b (f :: 'a => 'b => 'b) (Insert x s) = f x (setrec b f s)"
apply (lifting psetrec_step)
unfolding fun_rel_def
apply (auto intro: equi_cong equi_refl)
sorry (* apply (rule psetrec_inv) *)






(* more involved example *)
(* etwas kuenstlich weil man 'a swap_pair einfach inlinen koennte *)
datatype 'a pswap_set = psEmpty | psNode 'a | psInsert "'a pswap_pair" "'a pswap_set"
 and 'a pswap_pair = pSwapPair "'a pswap_set" "'a pswap_set"

inductive
  psset_equi :: "'a pswap_set => 'a pswap_set => bool" and
  pspair_equi :: "'a pswap_pair => 'a pswap_pair => bool"
where
    sequi_refl: "psset_equi x x"
  | sequi_subst: "psset_equi (psInsert i (psInsert j s)) (psInsert j (psInsert i s))"
  | sequi_cong: "psset_equi x y ==> psset_equi (psInsert i x) (psInsert i y)" (* in sequi_subst inlinen? *)
  | sequi_trans: "psset_equi x y ==> psset_equi y z ==> psset_equi x z"
  | sequi_symm: "psset_equi x y ==> psset_equi y x"

  | pequi_refl: "pspair_equi x x"
  | pequi_base: "pspair_equi (pSwapPair x x2) (pSwapPair x2 x)"
  | pequi_cong: "psset_equi x y ==> psset_equi x2 y2 ==> pspair_equi (pSwapPair x x2) (pSwapPair y y2)"  
  | pequi_trans: "pspair_equi x y ==> pspair_equi y z ==> pspair_equi x z"
  | pequi_symm: "pspair_equi x y ==> pspair_equi y x"

    
quotient_type 'a swap_set = "'a pswap_set" / psset_equi
and 'a swap_pair = "'a pswap_pair" / pspair_equi
  unfolding equivp_def sorry (* they are equivalence relations *)

quotient_definition
  "sEmpty :: 'a swap_set"
is "psEmpty :: 'a pswap_set"
quotient_definition
  "sNode :: 'a => 'a swap_set"
is "psNode :: 'a => 'a pswap_set"
quotient_definition
  "sInsert :: 'a swap_pair => 'a swap_set => 'a swap_set"
is "psInsert :: 'a pswap_pair => 'a pswap_set => 'a pswap_set"
quotient_definition
  "SwapPair :: 'a swap_set => 'a swap_set => 'a swap_pair"
is "pSwapPair :: 'a pswap_set => 'a pswap_set => 'a pswap_pair"




end
