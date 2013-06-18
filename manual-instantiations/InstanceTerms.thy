theory InstanceTerms
imports NonFreeAnimation
begin 

(*Binding terms with freshness and substitution (another "must" since it further tests parameter conditions): *)



type_synonym var = nat 

(*
datatype terms = Var "var" | App "terms" "terms" | Lm "var" "terms" | Subst ""terms" "terms" "var"

Note: changed Subst argument order to get order  external inputs -> internal inputs -> output
notation X[ Y / y] for Subst X Y y  or  (subst y := Y in X)

with fresh : var => term => bool
where
   (Var x) [X / x] = X

  x ~= y ==>  (Var x) [Y / y] = Var x

  (App X Y) [Z / z] = App (X [Z / z]) (Y [Z / z])

 [|x ~= y; fresh x Y|] ==>  (Lm  x X) [Y / y] = Lm x (X [Y / y])

  x ~= y ==> fresh x (Var y)

  [|fresh x Y; fresh x Z|] ==> fresh x (App Y Z)

  fresh x (Lm x X)

  fresh x Y ==> fresh x (Lm y Y)

  [|y ~= x; fresh y X|] ==> Lm x X = Lm y (X [(Var y) / x])
*)


locale results =
  fixes var :: tyco
    and terms_name :: tyco
    and Var_name :: oper
    and App_name :: oper
    and Lam_name :: oper
    and Subst_name :: oper
    and fresh_name :: rel
    and neq :: pcond
begin

lemma [ffact]: "terms_name tycohaskind IntType" ..
lemma [ffact]: "var tycohaskind ExtType" ..
lemma [ffact]: "var tyinterpr TYPE(var)" ..
lemma [ffact]: "decl_tyvars () []" ..


lemma [ffact]: "Var_name operhasty (var =T=> terms_name)" ..
lemma [ffact]: "App_name operhasty (terms_name =T=> terms_name =T=> terms_name)" ..
lemma [ffact]: "Lam_name operhasty (var =T=> terms_name =T=> terms_name)" ..
  (* we need to switch the argument order to adhere to  external inputs -> internal inputs -> output *)
lemma [ffact]: "Subst_name operhasty (terms_name =T=> terms_name =T=> var =T=> terms_name)" ..

abbreviation
  subst_abbrev ("subst _ := _ in _" [100,100,100] 60)
where
  "(subst x := t2 in t1) == Subst_name $ t1 $ t2 $ x"


lemma [ffact]: "fresh_name relhasty (var =T=> terms_name =T=> bool)" ..
lemma [ffact]: "neq pcondhasty (var =T=> var =T=> bool)" ..
lemma [ffact]: "neq pcondinterpr (% (x :: var) y. x ~= y)" ..



definition "subst_clause1_name = (0::nat)"
definition "subst_clause2_name = (0::nat)"
definition "subst_clause3_name = (0::nat)"
definition "subst_clause4_name = (0::nat)"
definition "subst_clause5_name = (0::nat)"
definition "fresh_clause1_name = (0::nat)"
definition "fresh_clause2_name = (0::nat)"
definition "fresh_clause3_name = (0::nat)"
definition "fresh_clause4_name = (0::nat)"


(*
  (Var x) [X / x] = X
  x ~= y ==>  (Var x) [Y / y] = Var x
  (App X Y) [Z / z] = App (X [Z / z]) (Y [Z / z])
  [|x ~= y; fresh x Y|] ==>  (Lm x X) [Y / y] = Lm x (X [Y / y])
  [|y ~= x; fresh y X|] ==> Lm x X = Lm y (X [(Var y) / x]) *)
lemma [ffact]: "decl_hcl subst_clause1_name (QUANT x:var. QUANT X:terms_name.
   subst x := X in (Var_name $ x) === X)" ..
lemma [ffact]: "decl_hcl subst_clause2_name (QUANT x:var. QUANT y:var. QUANT Y:terms_name.
  neq $ x $ y --->
    subst y := Y in (Var_name $ x) === Var_name $ x)" ..
lemma [ffact]: "decl_hcl subst_clause3_name (QUANT z : var. QUANT X : terms_name. QUANT Y : terms_name. QUANT Z : terms_name.
  subst z := Z in (App_name $ X $ Y) === App_name $ (subst z := Z in X) $ (subst z := Z in Y))" ..
lemma [ffact]: "decl_hcl subst_clause4_name (QUANT x:var. QUANT y:var. QUANT X:terms_name. QUANT Y:terms_name.
  neq $ x $ y ---> fresh_name $ x $ Y --->
    subst y := Y in (Lam_name $ x $ X) === Lam_name $ x $ (subst y := Y in X))" ..
lemma [ffact]: "decl_hcl subst_clause5_name (QUANT x:var. QUANT y:var. QUANT X:terms_name.
  neq $ y $ x ---> fresh_name $ y $ X --->
    Lam_name $ x $ X === Lam_name $ y $ (subst x := (Var_name $ y) in X))" ..


(*  x ~= y ==> fresh x (Var y)
  [|fresh x Y; fresh x Z|] ==> fresh x (App Y Z)
  fresh x (Lm x X)
  fresh x Y ==> fresh x (Lm y Y) *)
lemma [ffact]: "decl_hcl fresh_clause1_name (QUANT x:var. QUANT y:var. QUANT X:terms_name.
  neq $ x $ y ---> fresh_name $ x $ (Var_name $ y))" ..
lemma [ffact]: "decl_hcl fresh_clause2_name (QUANT x:var. QUANT Y:terms_name. QUANT Z:terms_name.
  fresh_name $ x $ Y ---> fresh_name $ x $ Z ---> fresh_name $ x $ (App_name $ Y $ Z))" ..
lemma [ffact]: "decl_hcl fresh_clause3_name (QUANT x:var. QUANT X:terms_name.
  fresh_name $ x $ (Lam_name $ x $ X))" ..
lemma [ffact]: "decl_hcl fresh_clause4_name (QUANT x:var. QUANT y:var. QUANT Y:terms_name.
  fresh_name $ x $ Y ---> fresh_name $ x $ (Lam_name $ y $ Y))" ..



ML {*
 Toplevel.profiling := 0
*}

local_setup {* MetaRec.run_expl_frules *}

end


thm results.fresh_clause2
thm results.subst_clause4



locale algebra_results = results  var terms_name Var_name App_name Lam_name Subst_name fresh_name neq
    for var :: tyco
    and terms_name :: tyco
    and Var_name :: oper
    and App_name :: oper
    and Lam_name :: oper
    and Subst_name :: oper
    and fresh_name :: rel
    and neq :: pcond
begin


definition
  myiter_name where
  "myiter_name = (0::nat)"

definition freshint where
  "freshint == (% (x :: var) (y :: nat). True)"

lemma [ffact]: "decl_iter_name terms_name myiter_name" ..

lemma [ffact]: "terms_name alginterpr TYPE(nat)" ..
lemma [ffact]: "Var_name operalginterpr (% (x::var). 0::nat)" ..
lemma [ffact]: "App_name operalginterpr (% (X :: nat) Y. X + Y)" ..
lemma [ffact]: "Lam_name operalginterpr (% (x::var) X ::nat. X + 1)" ..
  (* wrong of course! just testing *)
lemma [ffact]: "Subst_name operalginterpr (% (X::nat) Y (x::var). X * Y)" ..
lemma [ffact]: "fresh_name relalginterpr freshint" ..

  (* assume everything! just testing *)
lemma [ffact]: "proven_hcl True" by (simp add: proven_hcl_def)
lemma [MR]: "proven_hcl P" by sorry2

local_setup {* MetaRec.run_expl_frules *}

end

thm algebra_results.iter_op_clauses0
thm algebra_results.iter_rel_clauses0


end
