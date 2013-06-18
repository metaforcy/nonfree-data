theory InstanceFsetalt
imports NonFreeAnimation
begin 

(*
datatype 'a fset2 = Emp | Ins 'a ('a fset2) 
where 
  Ins a (Ins a s) = Ins a s
  Ins a1 (Ins a2 s) = Ins a2 (Ins a1 s)
*)

locale results =
  fixes alpha :: tyvar
    and finset_name :: tyco
    and ins_name :: oper
    and emp_name :: oper
    and dummy :: 'a
begin

lemma [ffact]: "decl_tyvars () [alpha]" ..
lemma [ffact]: "alpha tyinterpr TYPE('a)" ..

lemma [ffact]: "finset_name tycohaskind (ExtType =K=> IntType)" ..

lemma [ffact]: "ins_name operhasty (alpha =T=> finset_name ** alpha =T=> finset_name ** alpha)" ..
lemma [ffact]: "emp_name operhasty (finset_name ** alpha)" ..

definition "ins_clause1_name = (0::nat)"
definition "ins_clause2_name = (0::nat)"

lemma [ffact]: "decl_hcl ins_clause1_name (QUANT a:alpha. QUANT S: finset_name**alpha.
  ins_name $ a $ (ins_name $ a $ S) === ins_name $ a $ S)" ..
lemma [ffact]: "decl_hcl ins_clause2_name (QUANT a:alpha. QUANT a2:alpha. QUANT S: finset_name**alpha.
  ins_name $ a $ (ins_name $ a2 $ S) === ins_name $ a2 $ (ins_name $ a $ S))" ..

local_setup {* MetaRec.run_expl_frules *}

end


thm results.ins_clause1
thm results.ins_clause2




locale algebra_results = results  alpha finset_name ins_name emp_name dummy
    for alpha :: tyvar
    and finset_name :: tyco
    and emp_name :: oper
    and ins_name :: oper
    and dummy :: 'a
begin


lemma [ffact]: "(finset_name ** alpha) alginterpr TYPE('a set)" ..
lemma [ffact]: "ins_name operalginterpr (% (x::'a) (xs :: 'a set). {x} Un xs)" ..
lemma [ffact]: "emp_name operalginterpr ({} :: 'a set)" ..

lemma [ffact]: "proven_hcl (ALL (x::'a) (S::'a set). {x} Un ({x} Un S) = {x} Un S)"
  unfolding proven_hcl_def by blast
lemma [ffact]: "proven_hcl (ALL (x::'a) (x2::'a) (S::'a set). {x} Un ({x2} Un S) = {x2} Un ({x} Un S))"
  unfolding proven_hcl_def by blast

local_setup {* MetaRec.run_expl_frules *}

end

thm algebra_results.iter_op_clauses0



end
