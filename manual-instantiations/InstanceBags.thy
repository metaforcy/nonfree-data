theory InstanceBags
imports NonFreeAnimation
begin 

(*
datatype 'a bag = Emp | Ins 'a ('a bag) 
where 
  Ins a1 (Ins a2 s) = Ins a2 (Ins a1 s)
*)


locale results =
  fixes alpha :: tyvar
    and bag_name :: tyco
    and ins_name :: oper
    and emp_name :: oper
    and dummy :: 'a
begin

lemma [ffact]: "decl_tyvars () [alpha]" ..
lemma [ffact]: "alpha tyinterpr TYPE('a)" ..

lemma [ffact]: "bag_name tycohaskind (ExtType =K=> IntType)" ..

lemma [ffact]: "ins_name operhasty (alpha =T=> bag_name ** alpha =T=> bag_name ** alpha)" ..
lemma [ffact]: "emp_name operhasty (bag_name ** alpha)" ..

definition "ins_clause_name = (0::nat)"

lemma [ffact]: "decl_hcl ins_clause_name (QUANT a:alpha. QUANT a2:alpha. QUANT S: bag_name**alpha.
  ins_name $ a $ (ins_name $ a2 $ S) === ins_name $ a2 $ (ins_name $ a $ S))" ..

local_setup {* MetaRec.run_expl_frules *}

end


thm results.ins_clause




locale algebra_results = results  alpha bag_name ins_name emp_name dummy
    for alpha :: tyvar
    and bag_name :: tyco
    and emp_name :: oper
    and ins_name :: oper
    and dummy :: 'a
begin


lemma [ffact]: "(bag_name ** alpha) alginterpr TYPE('a set)" ..
lemma [ffact]: "ins_name operalginterpr (% (x::'a) (xs :: 'a set). {x} Un xs)" ..
lemma [ffact]: "emp_name operalginterpr ({} :: 'a set)" ..

lemma [ffact]: "proven_hcl (ALL (x::'a) (x2::'a) (S::'a set). {x} Un ({x2} Un S) = {x2} Un ({x} Un S))"
  unfolding proven_hcl_def by blast

local_setup {* MetaRec.run_expl_frules *}

end

thm algebra_results.iter_op_clauses0



end
