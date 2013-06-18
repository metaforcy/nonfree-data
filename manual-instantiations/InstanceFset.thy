theory InstanceFset
imports NonFreeAnimation
begin 



locale results =
  fixes alpha :: tyvar
    and finset_name :: tyco
    and empty_name :: oper
    and single_name :: oper
    and union_name :: oper
    and fresh_name :: rel
    and neq :: pcond
    and dummy :: 'a
begin

lemma [ffact]: "decl_tyvars () [alpha]" ..
lemma [ffact]: "alpha tyinterpr TYPE('a)" ..

lemma [ffact]: "finset_name tycohaskind (ExtType =K=> IntType)" ..

lemma [ffact]: "empty_name operhasty (finset_name ** alpha)" ..
lemma [ffact]: "single_name operhasty (alpha =T=> finset_name ** alpha)" ..
lemma [ffact]: "union_name operhasty (finset_name ** alpha =T=> finset_name ** alpha =T=> finset_name ** alpha)" ..

lemma [ffact]: "fresh_name relhasty (alpha =T=> finset_name ** alpha =T=> bool)" ..
lemma [ffact]: "neq pcondhasty (alpha =T=> alpha =T=> bool)" ..
lemma [ffact]: "neq pcondinterpr (% (x :: 'a) y. x ~= y)" ..



definition "fresh_clause1_name = (0::nat)"
definition "fresh_clause2_name = (0::nat)"
definition "union_clause1_name = (0::nat)"
definition "union_clause2_name = (0::nat)"
definition "union_clause3_name = (0::nat)"
definition "union_clause4_name = (0::nat)"


lemma [ffact]: "decl_hcl fresh_clause1_name (QUANT a:alpha. fresh_name $ a $ empty_name)" ..
lemma [ffact]: "decl_hcl fresh_clause2_name (QUANT a1:alpha. QUANT a2:alpha. QUANT s : finset_name ** alpha.
  neq $ a1 $ a2 ---> fresh_name $ a1 $ s ---> fresh_name $ a1 $ (union_name $ (single_name $ a2) $ s))" ..

lemma [ffact]: "decl_hcl union_clause1_name (QUANT S: finset_name**alpha.
  union_name $ empty_name $ S === S)" ..
lemma [ffact]: "decl_hcl union_clause2_name (QUANT S: finset_name**alpha. QUANT S2: (finset_name**alpha).
  union_name $ S $ S2 === union_name $ S2 $ S)" ..
lemma [ffact]: "decl_hcl union_clause3_name (QUANT a:alpha.
  union_name $ (single_name $ a) $ (single_name $ a) === single_name $ a)" ..
lemma [ffact]: "decl_hcl union_clause4_name (QUANT S: finset_name**alpha. QUANT S2: finset_name**alpha. QUANT S3: finset_name**alpha.
  union_name $ (union_name $ S $ S2) $ S3 === union_name $ S $ (union_name $ S2 $ S3))" ..



local_setup {* MetaRec.run_expl_frules *}

end


thm results.fresh_clause2
thm results.union_clause4



locale algebra_results = results  alpha finset_name empty_name single_name union_name fresh_name neq dummy
    for alpha :: tyvar
    and finset_name :: tyco
    and empty_name :: oper
    and single_name :: oper
    and union_name :: oper
    and fresh_name :: rel
    and neq :: pcond
    and dummy :: 'a
begin


definition freshint where
  "freshint == (% (x :: 'a) (y :: 'a set). x \<notin> y)"

lemma [ffact]: "(finset_name ** alpha) alginterpr TYPE('a set)" ..
lemma [ffact]: "union_name operalginterpr (op Un :: 'a set => 'a set => 'a set)" ..
lemma [ffact]: "single_name operalginterpr (% x :: 'a. {x})" ..
lemma [ffact]: "empty_name operalginterpr ({} :: 'a set)" ..
lemma [ffact]: "fresh_name relalginterpr (freshint :: 'a => 'a set => bool)" ..

lemma [ffact]: "proven_hcl (ALL S::'a set. {} Un S = S)" by auto
lemma [ffact]: "proven_hcl (ALL (S::'a set) S2. S Un S2 = S2 Un S)" by auto
lemma [ffact]: "proven_hcl (ALL a::'a. {a} Un {a} = {a})" by auto
lemma [ffact]: "proven_hcl (ALL (S::'a set) S2 S3. (S Un S2) Un S3 = S Un (S2 Un S3))" 
by auto

lemma [ffact]: "proven_hcl (ALL a::'a. freshint a {})" unfolding freshint_def by auto
lemma [ffact]: "proven_hcl (ALL (a1::'a) (a2::'a)  (S :: 'a set).
  a1 ~= a2 --> freshint a1 S --> freshint a1 ({a2} Un S))" unfolding freshint_def by auto

local_setup {* MetaRec.run_expl_frules *}

end

thm algebra_results.iter_op_clauses0
thm algebra_results.iter_rel_clauses0



end
