theory InstanceTrees
imports NonFreeAnimation
begin 


datatype 'a tree2 = Tree2 "'a" "('a treelist)"
  and 'a treelist = Emp2 | Cons2 "('a tree2)" "('a treelist)"

thm tree2_treelist.induct tree2_treelist.inducts


(* these don't work, mutually rec datatypes must have exact same type parameters *)
(* datatype 'a bla = Emp3 | One "'a blub"
   and  'b blub = Blub *)
(* datatype 'a bla = Emp3 | One3 'a | Blub1 "blub"
  and blub = Blub *)



(*
Finitely branching unordered trees

datatype  'a tree = Tree 'a ('a tfset) 
and      'a tfset = Emp | Ins ('a tree) ('a tfset) 
where 
  Ins a (Ins a s) = Ins a s

  Ins a1 (Ins a2 s) = Ins a2 (Ins a1 s)
*)



locale results =
  fixes alpha :: tyvar
    and tree_name :: tyco
    and tfset_name :: tyco
    and Empty_name :: oper
    and Ins_name :: oper
    and Tree_name :: oper
    and dummy :: 'a
begin

lemma [ffact]: "decl_tyvars () [alpha]" ..
lemma [ffact]: "alpha tyinterpr TYPE('a)" ..

lemma [ffact]: "tree_name tycohaskind (ExtType =K=> IntType)" ..
lemma [ffact]: "tfset_name tycohaskind (ExtType =K=> IntType)" ..

lemma [ffact]: "Empty_name operhasty (tfset_name ** alpha)" ..
lemma [ffact]: "Ins_name operhasty (tree_name ** alpha =T=> tfset_name ** alpha =T=> tfset_name ** alpha)" ..
lemma [ffact]: "Tree_name operhasty (alpha =T=> tfset_name ** alpha =T=> tree_name ** alpha)" ..

definition "ins_clause1_name = (0::nat)"
definition "ins_clause2_name = (0::nat)"


lemma [ffact]: "decl_hcl ins_clause1_name (QUANT t: tree_name ** alpha. QUANT S: tfset_name ** alpha.
  Ins_name $ t $ (Ins_name $ t $ S) === Ins_name $ t $ S)" ..
lemma [ffact]: "decl_hcl ins_clause2_name (QUANT t: tree_name ** alpha. QUANT t2: tree_name ** alpha. QUANT S: tfset_name ** alpha.
  Ins_name $ t $ (Ins_name $ t2 $ S) === Ins_name $ t2 $ (Ins_name $ t $ S))" ..




(*
local_setup {*  MetaRec.add_non_pervasive_declaration (fn _ => MetaRec.set_trace_depth (10, 10))  *}
declare [[show_hyps]]
*)

local_setup {* MetaRec.run_expl_frules *}

end


thm results.ins_clause2

term "TYPE('b results.tree)"


(*type_synonym 'a tree = "'a results.sorts_enum_Constr0_reified"
type_synonym 'a tfset = "'a results.sorts_enum_Constr1_reified" *)

locale map_fun =
  results alpha tree_name tfset_name Empty_name Ins_name Tree_name dummy
     for alpha :: tyvar and tree_name :: tyco and tfset_name :: tyco and Empty_name :: oper
     and Ins_name :: oper and Tree_name :: oper  and dummy :: 'a +
  fixes f :: "'a => 'b"
begin


lemma tree_ty_interpr[ffact]: "(tree_name ** alpha) alginterpr TYPE('b tree)" ..
lemma tfset_ty_interpr[ffact]: "(tfset_name ** alpha) alginterpr TYPE('b tfset)" ..

lemma empty_interpr[ffact]: "Empty_name operalginterpr (results.Empty :: 'b tfset)" ..
lemma ins_interpr[ffact]: "Ins_name operalginterpr (results.Ins :: 'b tree => 'b tfset => 'b tfset)" ..
lemma tree_interpr[ffact]: "Tree_name operalginterpr (% (x::'a) (ts :: 'b tfset). results.Tree (f x) ts)" ..

lemma [ffact]: "proven_hcl (ALL t :: 'b tree. ALL S :: 'b tfset.
  results.Ins t (results.Ins t S) = results.Ins t S)" sorry
lemma [ffact]: "proven_hcl (ALL t :: 'b tree. ALL t2 :: 'b tree. ALL S :: 'b tfset.
  results.Ins t (results.Ins t2 S) = results.Ins t2 (results.Ins t S))" sorry

ML {*
  MetaRec.print_depgraph (Context.Proof @{context})
*}

local_setup {*
  (* MetaRec.set_running_expl_frules true
  #> MetaRec.add_facts_decl [@{thm tree_ty_interpr}, @{thm tfset_ty_interpr},
    @{thm empty_interpr}, @{thm ins_interpr}, @{thm tree_interpr}]
  #> *)
  MetaRec.run_expl_frules
*}

end

thm map_fun.iter_op_clauses0



end
