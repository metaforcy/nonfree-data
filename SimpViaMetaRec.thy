theory SimpViaMetaRec
imports HOLMetaRec
begin

(* synth  t2  from  t1,   t1 is primary *)
definition
  simpto_const :: "'a::{} => 'a => prop" ("(_) simpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "simpto_const t1 t2 == (t1 == t2)"
(* synth  t2  from  t1,   t1 is primary *)
definition
  irewto_const :: "'a::{} => 'a => prop" ("(_) irewto (_)" [10,10] 10)
where
  [MRjud 1 1]: "irewto_const t1 t2 == (t1 == t2)"
(* synth  t2  from  t1,   t1 is primary *)
definition
  rewto_const :: "'a::{} => 'a => prop" ("(_) rewto (_)" [10,10] 10)
where
  [MRjud 1 1]: "rewto_const t1 t2 == (t1 == t2)"

(* synth  t2  from  t1,   t1 is primary *)
definition
  subsimpto_const :: "'a::{} => 'a => prop" ("(_) subsimpto (_)" [10,10] 10)
where
  [MRjud 1 1]: "subsimpto_const t1 t2 == (t1 == t2)"

(* synth  t'  from  t1,t2   t1 is primary *)
definition
  checkbeta_const :: "('a::{} => 'b::{}) => 'a => 'b => prop" ("checkbeta (_) (_) to (_)" [10,10,10] 10)
where
  [MRjud 2 1]: "checkbeta_const t1 t2 t' == ((t1 t2) == t')"


(* low prior *)
lemma id_sub[MR]:
  "  t subsimpto t  "
  unfolding subsimpto_const_def by simp

(* beachte: decompose matching auf primaere Objekte eta-expandiert diese nicht on-the-fly
     sichert hier Termination weil sonst auf t in t(x) in der Premisse wieder diese Regel
     passen wuerde *)
lemma lam_sub[MR]:
  "(!! x. t(x) simpto t'(x))
  ==>  (% x. t(x)) subsimpto (% x. t'(x))"
  unfolding simpto_const_def subsimpto_const_def
  ML_prf {* Thm.axiom @{theory} "Pure.abstract_rule"  *}
  by (tactic {* rtac (Thm.axiom @{theory} "Pure.abstract_rule") 1 *})

lemma app_sub[MR]:
  "[|  t1 simpto t1'  ;  t2 simpto t2'  ;  checkbeta t1' t2' to t' |]
  ==>  (t1 t2) subsimpto t'"
  unfolding simpto_const_def checkbeta_const_def subsimpto_const_def by simp

(* congruence rule for meta implication *)
lemma imp_sub[MR]:
  "[|  (PROP t1) simpto (PROP t1')  ;  PROP t1' ==> (PROP t2) simpto (PROP t2') |]
  ==> (PROP t1 ==> PROP t2) subsimpto (PROP t1' ==> PROP t2')"
 unfolding subsimpto_const_def simpto_const_def by simp


(* low prior *)
lemma checkbeta_id[MR]:
  "checkbeta t1 t2 to (t1 t2)"
  unfolding checkbeta_const_def by simp

(* high priority *)
(* TODO: checks perfectly fine, but we want simpto to depend implicitly on rewto,
   using what is there ATM, to avoid what is interpreted as cyclic dependencies *)
lemma checkbeta_rew[MR_unchecked]:
  "[|  try ( (t1(t2)) rewto t' )  ;  t' simpto t'' |]
  ==>  checkbeta (% x. t1(x)) t2 to t''   "
  unfolding try_const_def simpto_const_def rewto_const_def checkbeta_const_def by simp

lemma simpto_rule[MR]:
 "[|  t subsimpto t'  ;  t' irewto t''  |]
 ==>  t simpto t''  "
 unfolding simpto_const_def irewto_const_def subsimpto_const_def by simp

(* not always what is wanted in automation! *)
lemma simpto_eq:  "[|  t simpto t'  ;  t2 simpto t'  |] ==>
  (t = t2) simpto True "
  by(simp add: simpto_const_def)
  


(* low prior *)
lemma irewto_id[MR]:
  "t irewto t"
  unfolding irewto_const_def by simp

(* high prior *)
(* bottom-up *)
(* TODO: checks perfectly fine, but we want simpto to depend implicitly on rewto,
   using what is there ATM, to avoid what is interpreted as cyclic dependencies *)
lemma irewto_rule[MR_unchecked]:
  "[|  try (t rewto t')  ;  t' simpto t'' |]
  ==>  t irewto t''"
 unfolding rewto_const_def irewto_const_def try_const_def simpto_const_def subsimpto_const_def
 by simp




lemma simpto_prop_fconv: "  P simpto P' ==> PROP P' ==> PROP P  "
  by (simp add: simpto_const_def)


ML {*
  MetaRec.fconv_metarec
*}

method_setup mrsimp = {*
  let fun solver ths =
    FIRST' [resolve_tac (reflexive_thm :: @{thm TrueI} :: @{thm refl} :: ths),
      atac, etac @{thm FalseE}, K all_tac]
  in
    Attrib.thms >> (fn thms => fn ctxt => METHOD (fn facts =>
      let
        val ths = facts @ thms
        val ctxt2 = ctxt
          |> Context.proof_map (MetaRec.add_rule 0 @{thm simpto_eq})
          |> fold (MetaRec.add_assm true) ths
      in
        MetaRec.fconv_metarec @{thm simpto_prop_fconv} (solver ths) ctxt2 1
      end))
  end
*} ""

(* "competing" animation methods: ares_tac tries the rules in the list, priorized from left to right *)
method_setup dfs_solve = {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
  (DEPTH_SOLVE (HEADGOAL (ares_tac (facts @ thms)))))))
*} ""
method_setup bfs_solve = {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
  (BREADTH_FIRST (has_fewer_prems 1) (HEADGOAL (ares_tac (facts @ thms)))))))
*} ""
method_setup iterdeep_solve = {*
  Attrib.thms >> (fn thms => K (METHOD (fn facts =>
  (ITER_DEEPEN 20 (has_fewer_prems 1) (ares_tac (facts @ thms))))))
*} ""





locale tests = 
  fixes dummy :: 'dummy
begin

(* lets have some stupid examples *)

definition
  A ::nat
where "A = 0"
definition
  B ::nat
where "B = 0"

lemma Asimp: "A == B" by (simp add: A_def B_def)

(* some trivial fact to rewrite with *)
lemma userrewdecl[MR]:
  "A rewto B"
by (simp add: rewto_const_def A_def B_def)



schematic_lemma test: "A simpto ?C"
(* doesnt terminate? *)
  (* by (dfs_solve tryI app_sub id_sub checkbeta_rew checkbeta_id simpto_rule irewto_rule irewto_id userrewdecl) *)
(* manually: *)
(*  apply (rule simpto_rule)
  apply (rule id_sub)
  apply (rule irewto_rule)
  apply (rule tryI)
  apply (rule userrewdecl)
  apply (rule simpto_rule)
  apply (rule id_sub)
  by (rule irewto_id)  *)
by (tactic {* MetaRec.metarec_tac @{context} 1 *})

schematic_lemma test2: "((!! P. A = A ==> P ==> True) ==> True) simpto ?C"
(* doesnt terminate?
   lam_sub Regel muss man rausnehmen sonst triviale nicht-Term wg Unif modulo eta *)
(* by (dfs_solve tryI app_sub id_sub checkbeta_rew checkbeta_id simpto_rule irewto_rule irewto_id userrewdecl) *)
(* bfs_solve, iterdeep_solve use wrong execution model: don't rewrite at all *)
  (* by (bfs_solve tryI app_sub id_sub checkbeta_rew checkbeta_id simpto_rule irewto_rule irewto_id userrewdecl) *)
  (* by (iterdeep_solve  tryI app_sub id_sub checkbeta_rew checkbeta_id simpto_rule irewto_rule irewto_id userrewdecl) *)
(* 38ms without optimizations, 25 ms with no_comp_rules Optimization *)
by (tactic {* MetaRec.metarec_tac @{context} 1 *})

(* 3ms *)
lemma test2': "((!! P. A = A ==> P ==> True) ==> True)"
by (simp add: userrewdecl[simplified rewto_const_def])

ML {*
  val ct = @{term "((!! P. A = A ==> P ==> True) ==> True)"}
    |> cterm_of @{theory}
  val simpth = @{thm Asimp}
  fun runsimp () =
    let val _ = Raw_Simplifier.rewrite true [simpth] ct in () end
*}
(* 1 ms! *)
ML {*
  val _ = runsimp ()
*}


schematic_lemma test3: assumes [MRassm]: "(0::nat) rewto 1" shows "(0::nat) simpto ?C"
by (tactic {* MetaRec.metarec_tac @{context} 1 *})


schematic_lemma test4: assumes [MRassm]: "(0::nat) rewto 1" shows "Suc (0::nat) = Suc 1"
by mrsimp



definition
  foo :: "'a => 'a => bool"
where
  [MRjud 1 1]: "foo x y == True"

(* test local frules *)
schematic_lemma test5:
  assumes [MRassm]: "foo (0::nat) (1::nat)"
  and [MRassm]: "!! (x::nat) y. frule(foo x y ==> x rewto y)"
  shows "(0::nat) simpto ?C"
by (tactic {* MetaRec.metarec_tac @{context} 1 *})

(* test local brules *)
schematic_lemma test6:
  assumes [MRassm]: "foo (0::nat) (1::nat)"
  and [MRassm]: "!! (x::nat) y. foo x y ==> x rewto y"
  shows "(0::nat) rewto ?C"
by (tactic {* MetaRec.metarec_tac @{context} 1 *})


schematic_lemma
  assumes [MRassm]: "!! P1 P2. Trueprop (P1 --> P2) rewto  (P1 ==> P2)"
  shows "Trueprop (P1 --> P2 --> P3)  simpto ?Q"
  by (tactic {* MetaRec.metarec_tac @{context} 1 *})


end


end
