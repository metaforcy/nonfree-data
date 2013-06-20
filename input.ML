
structure NonFreeInput = struct



datatype Kind = ParameterType | InternalType

type data_ty = {
  constructors: (term * Kind list) list, relations: term list,
  constr_int_vars: term list, rel_int_vars: term list,
  iterators: (typ * term) list, iter_rews: thm list, reified_hcls: term list }

fun data_eq (data1, data2) = 
  let
    val {constructors, relations, constr_int_vars, rel_int_vars,
   iterators, iter_rews, reified_hcls } = data1
    val {constructors=constructors2, relations=relations2, constr_int_vars=constr_int_vars2,
      rel_int_vars=rel_int_vars2, iterators=iterators2, iter_rews=iter_rews2,
      reified_hcls=reified_hcls2 } = data2
    fun term_list_eq (l1, l2) = forall (op aconv) (l1 ~~ l2)
  in
    forall term_list_eq
      [(relations, relations2),
       (constr_int_vars, constr_int_vars2),
       (rel_int_vars, rel_int_vars2),
       (map snd iterators, map snd iterators2),
       (reified_hcls, reified_hcls2)]
    andalso constructors ~~ constructors2 |> forall (op =) 
    andalso (iterators, iterators2) |> pairself (map fst) |> (op ~~) |> forall (op =)
    andalso forall Thm.eq_thm_prop (iter_rews ~~ iter_rews2)
  end

structure Data = Generic_Data(struct
   (* indexed by tyco *)
  type T = data_ty Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge (tab1, tab2) = 
    Symtab.merge (K true) (tab1, tab2)
end);

fun group_by f eq = map (fn x => (f x, x))
  #> Library.partition_eq (eq_fst eq) #> map (fn ys => (fst (hd ys), map snd ys))


fun fold_applied_heads f (Abs(_, _, t)) = fold_applied_heads f t
  | fold_applied_heads f t =
      let val (h, ts) = strip_comb t
      in
        f (h, ts) #> fold (fold_applied_heads f) ts
      end


val logical_tycos = [@{type_name "prop"}, @{type_name "bool"}, "fun"]
  

fun add_tycos (Type (tyco, Ts)) =
      insert (op =) (tyco, length Ts) #> fold add_tycos Ts
  | add_tycos _ = I

fun add_tyco_names T l =
   union (op =) (add_tycos T [] |> map fst) l


(* TODO(brittle): get rid of name hacking *)
val pseudofy_name = suffix "_name"


fun classify_type ctxt tfree_names ext_tycos full_int_tycos T =
  let
    val bad_tfrees = Term.add_tfreesT T []
      |> subtract (op = o apsnd fst) tfree_names
    val _ =
      if null bad_tfrees then ()
      else
        error ("type "^Syntax.string_of_typ ctxt T^" contains unknown TFrees "
          ^Library.commas (map (Syntax.string_of_typ ctxt o TFree) bad_tfrees))
    val tycos = add_tyco_names T []
    val non_ext_tycos = 
      tycos |> subtract (op =) ext_tycos
    val bad_tycos =
      non_ext_tycos |> subtract (op = o apfst fst) full_int_tycos
      |> subtract (op =) logical_tycos
  in
    if null non_ext_tycos then
      ParameterType
    else if null bad_tycos then
      InternalType
    else
      error ("classify_type: type "^Syntax.string_of_typ ctxt T
        ^" contains unrelated type constructors "^Library.commas bad_tycos)
  end
  

fun check_argtyp _ (TFree (n, _)) = true
  | check_argtyp _ (TVar _) = error "Illegal schematic type variable(s)"
  | check_argtyp full_int_tycos (Type (tname, Ts)) =
      (case AList.lookup (op =) full_int_tycos tname of
         NONE =>
           if fold add_tyco_names Ts [] |> exists (AList.defined (op =) full_int_tycos) then
             error "Nested datatypes not treated"
           else
             true
       | SOME vs =>
           if map (try (fst o dest_TFree)) Ts = map SOME vs then
             true
           else
             error ("Illegal occurrence of recursive type " ^ tname))

fun to_pseudotype ctxt tyco_to_pt tfrees_to_nats T =
  let
    val to_pT = to_pseudotype ctxt tyco_to_pt tfrees_to_nats
    fun app_to_args T1 Targs =
      T1 |> fold (fn Targ => fn res =>
          @{term TypeApp} $ res $ to_pT Targ)
        Targs
  in
    case T of
      Type("fun", [T1, T2]) =>
        @{term TypeArr} $ to_pT T1 $ to_pT T2
    | Type(k, Ts) =>
        if k = @{type_name "bool"} then
          @{term "Tyco bool"}
        else
          (case AList.lookup (op =) tyco_to_pt k of
            SOME t =>
              app_to_args (@{term Tyco} $ t) Ts
          | NONE => error ("to_pseudotype: type constructor "^quote k^" unregistered"))
    | TFree(n, _) =>
        (case AList.lookup (op =) tfrees_to_nats n of
          SOME i => @{term TypeVar} $ (@{term TypvarEmb} $ HOLMetaRec.holize_nat i)
        | NONE => error ("to_pseudotype: unknown type variable "^quote n))
    | _ => error ("to_pseudotype: encountered TVar")
  end

(* (schematisch) quantifizierte variablen werden zu Bounds ueber fix_to_bound *)
(* sym_to_pt maps Frees or Constants to pseudoterms for constructors, relation symbols and parameter conditions *)
fun to_pseudoterm ctxt (sym_to_pt : (term * term) list) fix_to_bound t =
  let
    val T = fastype_of t
    val (h, ts) = Term.strip_comb t
    val _ =
      if can Term.dest_funT T then
        error ("to_pseudoterm: term not of base type "^Syntax.string_of_term ctxt t)
      else
        ()
    fun app_to_args encapp h' = 
        let
          fun app t1 t2 =
            if encapp then @{term "App"} $ t1 $ t2
            else t1 $ t2
        in
          h' |> fold (fn t => fn res =>
              app res (to_pseudoterm ctxt sym_to_pt fix_to_bound t))
            ts
        end
  in
    case h of
      Free(n, _) =>
        (case AList.lookup (op =) sym_to_pt h of
          SOME t' => app_to_args true t'
        | NONE =>
            (case AList.lookup (op =) fix_to_bound h of
              SOME i => 
                if length ts = 0 then @{term PseudoVar} $ Bound i
                else error ("to_pseudoterm: variable "^quote n^" is of function type")
            | NONE => error ("to_pseudoterm: unknown Free "^quote n)))
    | Const(@{const_name "==>"}, _) =>
        app_to_args false @{term "implication :: terms => terms => terms"}
    | Const(@{const_name "HOL.eq"}, _) =>
        app_to_args false @{term "equality :: terms => terms => terms"}
    | Const(@{const_name "Trueprop"}, _) =>
        (case ts of
          [t'] => to_pseudoterm ctxt sym_to_pt fix_to_bound t'
        | _ => error ("to_pseudoterm: internal error: Trueprop application is wrong"))
    | Const(c, _) =>
        (case AList.lookup (op =) sym_to_pt h of
          SOME t' => app_to_args true t'
        | NONE => error ("to_pseudoterm: unknown constant "^quote c))
    | Abs(_, _, _) =>
        error ("to_pseudoterm: abstraction in term")
    | Bound _ => error ("to_pseudoterm: internal error: encountered bound")
    | _ => error ("to_pseudoterm: untreated term formation construct "^Syntax.string_of_term ctxt t)
  end


(** definitional introduction of datatypes **)

(* FIXME: TFree-Reihenfolge der Sorten-Typedefs (ueber Abbreviation)
  permutieren so das sie mit der vom User zusammenpasst *)

fun datatype_cmd tyco_names dts named_hcl_strs0 lthy0 =
  let
    (* TODO(hack):
       in neueren Isabelle Versionen macht es mehr Sinn
       wenn man stattdessen lthy2 zu neuem Target macht *)
    val lthy = Local_Theory.restore lthy0

    val thy = Proof_Context.theory_of lthy
    val _ = Theory.requires thy "NonFree"
      "meta-theory for non-freely generated datatypes"

    fun parse_optS unparsed_Sopt = case unparsed_Sopt of
        SOME unparsed_S => Typedecl.read_constraint lthy (SOME unparsed_S)
      | NONE => HOLogic.typeS

    (* this theory is used just for parsing *)
    val tmp_thy = thy |> Theory.copy
      (* Sign.add_types_global (map (fn (tvs, tyco, _) =>
        (tyco, length tvs, NoSyn)) dts) *)
      |> fold (fn (tv_unparsed_Sopt_s, tyco, _) =>
             Typedecl.typedecl_global (tyco, map (apsnd parse_optS) tv_unparsed_Sopt_s, NoSyn) #> snd)
           dts

    val (tfree_names_and_unparsed_optsorts, _, _) :: _ = dts
    val tfrees = tfree_names_and_unparsed_optsorts |> map (TFree o apsnd parse_optS)
    val tfree_names = tfrees |> map (fst o Term.dest_TFree)

    val tmp_lthy = lthy |> Local_Theory.raw_theory (K tmp_thy)
      |> fold Variable.declare_constraints (map Logic.mk_type tfrees)

    (* internal tycos (those that are being defined by the datatype cmd) as their full name and
       the type variable names they are applied to *)
    val full_int_tycos = dts |> map (fn (tv_unparsedS_s, tyco, _) =>
        let
          val full_tyco = Sign.full_name tmp_thy tyco
          val tvs = map fst tv_unparsedS_s
        in
          (case duplicates (op =) tvs of
            [] =>
              if eq_set (op =) (tfree_names, tvs) then (full_tyco, tvs)
              else error ("Mutually recursive datatypes must have same type parameters")
          | dups => error ("Duplicate parameter(s) for datatype " ^ quote (Binding.print tyco) ^
              " : " ^ commas dups))
        end)

    val _ =
      case duplicates (op =) (map fst full_int_tycos) @ duplicates (op =) tyco_names of
        [] => ()
      | dups => error ("Duplicate datatypes: " ^ commas dups)

    fun prep_dt_spec (_, tyco, (constrs : (binding * string list) list)) tyco_name
        (constrs', all_tycos') =
      let
        val full_tyco = Sign.full_name tmp_thy tyco
        fun prep_constr (cname, cargs) (constrs', all_tycos') =
          let
            val arg_types = cargs |> map (Syntax.read_typ tmp_lthy)
            val _ =
              (case subtract (op =) tfree_names (fold Term.add_tfree_namesT arg_types []) of
                [] => ()
              | tvs2 => error ("Extra type variables on rhs: " ^ commas tvs2))
            (* val c = Sign.full_name_path tmp_thy tyco_name cname *)
            val c = Binding.name_of cname
            val _ = arg_types |> forall (check_argtyp full_int_tycos)
            val res_type = Type(full_tyco, tfrees)
            val T = arg_types ---> res_type
          in
            (constrs' @ [(c, T)],
             all_tycos' |> fold add_tycos (res_type :: arg_types))
          end handle ERROR msg => cat_error msg
           ("The error above occurred in constructor " ^ quote (Binding.print cname) ^
            " of datatype " ^ quote (Binding.print tyco))

        val (new_constrs, all_tycos'') =
          fold prep_constr constrs ([], all_tycos')
      in
        case duplicates (op =) (map fst new_constrs) of
          [] =>
            (constrs' @ new_constrs, all_tycos'')
        | dups =>
            error ("Duplicate constructors " ^ commas dups
              ^" in datatype " ^ quote (Binding.print tyco))
      end

    val (constrs, all_tycos) = fold2 prep_dt_spec dts tyco_names ([], [])


    val tmp_lthy' = tmp_lthy
      |> Variable.add_fixes (map fst constrs) |> snd
      |> fold (fn (c, T) => Variable.declare_constraints (Free(c, T))) constrs

    val first_tyco_name =
      case full_int_tycos of
        (k, _) :: _ => Long_Name.base_name k
      | _ => error "nonfreedata: internal error: full_int_tycos empty"
    fun anon_hcl_name i = first_tyco_name ^ "_anon_hcl_clause" ^ string_of_int i |> pseudofy_name
    val named_hcl_strs = named_hcl_strs0 |> map_index (fn (i, ((bnd, atts), str)) =>
      if Binding.is_empty bnd then ((Binding.name (anon_hcl_name i), atts), str)
      else ((bnd, atts), str))

    val named_hcls = (map fst named_hcl_strs)
      ~~ (Syntax.read_props tmp_lthy' (map snd named_hcl_strs))

    val bad_tycos = []
      |> fold (fn (_, prop) => fold_types add_tyco_names prop) named_hcls
      |> subtract (op = o apfst fst) all_tycos
      |> subtract (op =) logical_tycos
    val _ =
      if null bad_tycos then ()
      else
        error ("nonfreedata: tycos in horn clauses that are not present in constructor types: "
          ^Library.commas bad_tycos)
    val _ = named_hcls |> forall (fn (_, prop) =>
      let
        val bad_tfrees = [] |> Term.add_tfrees prop
          |> subtract (op = o apsnd fst) tfree_names
        val _ =
          if null bad_tfrees then ()
          else
            error ("new type variables  "
              ^Library.commas (map (Syntax.string_of_typ tmp_lthy' o TFree) bad_tfrees)
              ^"  in horn clause  "^Syntax.string_of_term tmp_lthy' prop)
      in true end)

    val tfrees_to_nats = tfree_names |> map_index (fn (i, n) => (n, i))
    val tyco_to_pt = all_tycos
      |> map (fn (k, _) => (k, Free(Long_Name.base_name k |> pseudofy_name, @{typ "tyco"})))
    val ext_tycos = all_tycos |> subtract (fn ((k1, _), (k2, _)) => k1 = k2) full_int_tycos
    val ext_tycos' = map fst ext_tycos
    val classify_type_i =
      classify_type tmp_lthy' tfree_names ext_tycos' full_int_tycos
    val to_pseudotype_i = to_pseudotype tmp_lthy' tyco_to_pt tfrees_to_nats
    (* we explicitly consider tfrees because some of them might be unused as constructor arguments
       (which is actually a bit stupid but whatever) *)
    val ext_tyco_apps = [] |> fold (fn (_, T) => fold (fn T' =>
          if classify_type_i T' = ParameterType then
            insert (op =) T'
          else I)
        (binder_types T @ tfrees))
      constrs


    fun can_be_relation_type T =
      body_type T = @{typ "bool"}
      andalso not (null (binder_types T))
      andalso binder_types T |> forall (can classify_type_i)
    fun can_be_param_cond_type T = 
      body_type T = @{typ "bool"}
      andalso not (null (binder_types T))
      andalso binder_types T |> forall (fn T' => classify_type_i T' = ParameterType)

    (* FIXME: check that equated terms and arguments of relations are made from constructors and variables *)
    (* FIXME: check that equational conclusions are over internal types only *)
    val relations = [] |> fold (fn (_, prop) => fn relations =>
        let
          val concl = Logic.strip_assums_concl prop

          fun err_nonsimple_concl () =
            error ("nonfreedata: conclusion  "^Syntax.string_of_term tmp_lthy' concl
              ^"  is not an equality or an inductively-defined relation")
        in
          case concl of
            Const(@{const_name "Trueprop"}, _) $ (Const (@{const_name "HOL.eq"}, _) $ _ $ _) =>
              relations
          | Const(@{const_name "Trueprop"}, _) $ t =>
              (case head_of t of
                Free(n, T) =>
                  (case AList.lookup (op =) relations n of
                    NONE =>
                      if can_be_relation_type T then
                        cons (n,T) relations
                      else
                        err_nonsimple_concl ()
                  | SOME T' =>
                      if T = T' then
                        relations
                      else
                        error ("nonfreedata: inconsistent types for relation "^quote n))
              | _ => err_nonsimple_concl ())
          | _ => err_nonsimple_concl () 
        end)
      named_hcls

    (* FIXME: check that arguments of parameter conditions are variables *)
    val param_conds = [] |> fold (fn (_, prop) => fn param_conds =>
        let
          val assms = Logic.strip_assums_hyp prop
          fun err_nonsimple_assm assm t =
            error ("nonfreedata: assumption  "^Syntax.string_of_term tmp_lthy' assm
              ^"  is not an equality or an inductively-defined relation "
              ^"and its relevant subterm  "^Syntax.string_of_term tmp_lthy' t^
              "  cannot be regarded as a parameter condition")
          fun add assm n t =
            let val T = fastype_of t
            in
              case AList.lookup (op =) param_conds n of
                NONE =>
                  if can_be_param_cond_type T then
                    cons (n, t) param_conds
                  else
                    err_nonsimple_assm assm t
              | SOME t' => 
                  if t = t' then
                    param_conds
                  else
                    error ("nonfreedata: inconsistent types for parameter condition "
                      ^quote n)
            end
            
        in
          param_conds
          |> fold (fn assm => fn param_conds =>
              case assm of
                (* TODO(semantics): Gleichheitsannahmen machen nicht viel Sinn wegen
                     Abschluss unter Kongruenz, also vllt als Parameter-Conditions auffassen
                     oder Fehler melden?! *)
                Const(@{const_name "Trueprop"}, _) $ (Const (@{const_name "HOL.eq"}, _) $ _ $ _) =>
                  param_conds
              | Const(@{const_name "Trueprop"}, _) $ term =>
                  let val (head, args) = strip_comb term
                  in
                    if has_duplicates (op =) args then
                      err_nonsimple_assm assm head
                    else if not (args |> forall (Term.is_Free)) then
                      err_nonsimple_assm assm head
                    else
                      (case head of
                        Free (n, T) =>
                          (case AList.lookup (op =) relations n of
                            SOME T' => 
                              if T = T' then param_conds
                              else error ("nonfreedata: inconsistent types for relation "^quote n)
                          | NONE => (* can not be a constructor anyway *)
                              add assm n (Free (n, T)))
                      | Const (n, T) => add assm n (Const (n, T))
                      | _ => err_nonsimple_assm assm head)
                  end
              | _ => err_nonsimple_assm assm assm)
            assms
        end)
      named_hcls

    val sym_to_pt = 
      (constrs |> map (fn (n,T) =>
          (Free(n,T), @{term Oper} $ Free(pseudofy_name n, @{typ "oper"}))))
       @ (param_conds |> map (fn (_, t) =>
           let val n = case t of Const(n,_) => Long_Name.base_name n | Free(n,_) => n
           in
             (t, @{term PCond} $
              Free(pseudofy_name n, @{typ "pcond"}))
           end))
       @ (relations |> map (fn (n,T) =>
          (Free(n,T), @{term Rel} $ Free(pseudofy_name n, @{typ "rel"}))))

    val pseudo_hcls = named_hcls |> map (fn (bnd, prop) =>
      let
        val param_frees = Term.add_frees prop [] |> map Free
        val assms = Logic.strip_assums_hyp prop
        val concl = Logic.strip_assums_concl prop
        val fixes = param_frees
          |> filter_out (fn Free (n, _) =>
            AList.defined (op =) constrs n
            orelse AList.defined (op =) relations n
            orelse AList.defined (op =) param_conds n)
        val fix_to_bound = fixes |> map_index (fn (i, t) => (t, i))
      in 
        to_pseudoterm tmp_lthy' sym_to_pt fix_to_bound (Logic.list_implies (assms, concl))
        |> fold (fn (Free(n,T), i) => fn res_t =>
               @{term "Quant"} $ to_pseudotype_i T
                 $ Abs(n, @{typ "nat"}, res_t))
             fix_to_bound
        |> pair bnd
      end)

    val cert = cterm_of (Proof_Context.theory_of lthy)
    fun mk_kind_t num_args base_kind =
      (case base_kind of
        ParameterType => @{term ExtType}
      | InternalType => @{term IntType})
      |> fold (fn _ => fn t => @{term KindArr} $ @{term ExtType} $ t) (1 upto num_args)

    val init_facts =
      ((map (fn (k, vs) => (k, length vs, InternalType)) full_int_tycos
         @ map (fn (k, n) => (k, n, ParameterType)) ext_tycos)
       |> map (fn (k, n, base_kind) =>
         case AList.lookup (op =) tyco_to_pt k of
           SOME tyco_t =>
             @{thm decl_tycoI} |> Drule.instantiate' []
               (map (SOME o cert) [tyco_t, mk_kind_t n base_kind])
         | NONE => error "nonfreedata: internal error: tyco not mapped to pseudoterm"))
      @ [ @{thm decl_tyvarsI} |> Drule.instantiate' []
            [tfrees_to_nats |> map (fn (n, i) =>
               @{term TypvarEmb} $ HOLMetaRec.holize_nat i)
             |> HOLMetaRec.holize_list (Proof_Context.theory_of lthy) @{typ tyvar} |> cert |> SOME] ]
      @ (ext_tyco_apps |> map (fn T => @{thm decl_tyinterpr_easyI} OF
          (map (Thm.reflexive o cert) [to_pseudotype_i T,  Logic.mk_type T])))
      @ (sym_to_pt |> maps (fn (t, pt) =>
           let
             val T = fastype_of t 
             fun inst intro_th sym_t = 
               intro_th |> Drule.instantiate' []
                 (map (SOME o cert) [sym_t, to_pseudotype_i T])
           in
             case pt of
               @{term Oper} $ oper_t =>
                 [inst @{thm decl_operI} oper_t]
             | @{term Rel} $ rel_t =>
                 [inst @{thm decl_relI} rel_t]
             | @{term PCond} $ pcond_t =>
                 [inst @{thm decl_pcondI} pcond_t,
                  @{thm decl_pcond_interpr_easyI} OF (map (Thm.reflexive o cert) [pcond_t, t])]
             | _ => error "nonfreedata: internal error: wrong term in sym_to_pt"
           end))
      @ (pseudo_hcls |> map (fn ((bnd, _), t) => 
           @{thm decl_hcl_easyI} OF (map (Thm.reflexive o cert)
             [Free(Binding.name_of bnd |> pseudofy_name, @{typ "'a"}), t])))

    (* val _ = tracing ("initial facts are\n"
      ^cat_lines (init_facts |> map (Display.string_of_thm lthy))) *)



    val new_scope = serial ()
    val lthy2 = lthy
      |> fold Variable.declare_typ ext_tyco_apps
      |> MetaRec.add_non_pervasive_declaration (fn _ => MetaRec.new_scope true new_scope)
      |> MetaRec.add_non_pervasive_declaration (fn _ => MetaRec.set_scope new_scope)
          (* damit die init_facts auch ins Target gehen *)
      |> MetaRec.set_running_expl_frules true
      |> MetaRec.add_facts_decl init_facts
      |> MetaRec.run_expl_frules
      handle HOLMetaRec.distinguished_metarec_error (0, sort_ct, ctxt3, msg) =>
        let val (_, [name_t]) = MetaRec.metarec ctxt3 "NonFreeAnimation.sort_to_name_jud"
          (Thm.term_of sort_ct, [])
        in
          error ("nonfreedata: non-emptiness check failed for type constructor "
            ^Syntax.string_of_term ctxt3 name_t)
        end


    fun lookup_oneplace_fact mandatory rews lthy' pat =
      let
        val facts =
          MetaRec.lookup_facts (Context.Proof lthy') (Logic.varify_global pat)
        val _ =
          if mandatory andalso null facts then
            error ("nonfreedata: internal error: no fact found for "
              ^Syntax.string_of_term lthy' pat)
          else if length facts > 1 then
            error ("nonfreedata: internal error: multiple facts for "
              ^Syntax.string_of_term lthy' pat)
          else ()
        val t_opt = try hd facts |> Option.map (prop_of #> perhaps (try HOLogic.dest_Trueprop)
          #> strip_comb #> snd #> the_single)
      in
        case facts of
          [th] =>
             th |> Conv.fconv_rule (Conv.try_conv (Conv.rewrs_conv rews))
             |> MetaRec.unbalanced_conjuncts_to_thms
             |> map (Thm.forall_elim_vars 0)
             |> rpair t_opt
        | _ => ([], t_opt)
      end

    val induction_rules =
      lookup_oneplace_fact true [@{thm induction_rule_def}] lthy2 @{term "induction_rule P"} |> fst
    val cases_rules =
      lookup_oneplace_fact true [@{thm cases_rule_def}] lthy2 @{term "cases_rule P"} |> fst


    val (((tyco_int_ns, constr_int_ns), rel_int_ns), lthy3) = lthy2
      |> Local_Theory.notes (induction_rules |> map (fn indu_rule =>
           let
             val tname =
               case Thm.concl_of indu_rule |> HOLogic.dest_Trueprop of
                 P $ _ =>
                   (case domain_type (fastype_of P) of
                     Type(k, _) => k)
           in
             ((Binding.qualified_name (tname ^ "_induct"),
              [Attrib.internal (fn _ => Induct.induct_type tname)]), [([indu_rule], [])])
           end))
      |> snd
      |> Local_Theory.notes (cases_rules |> map (fn cases_rule =>
           let
             (* cases_rule : (!! p1 .. pn x1 .. xm. H = constr p1 .. pn x1 .. rm ==> P) ==> other cases
                             ==> P *)
             (* there always has to be some case because there always has to be some constructor
                otherwise the datatype would be empty *)
             val tname =
               case Thm.prems_of cases_rule |> hd |> Logic.strip_assums_hyp |> hd
                     |> HOLogic.dest_Trueprop |> HOLogic.dest_eq of
                 (H, _) =>
                   (case Term.body_type (fastype_of H) of
                     Type(k, _) => k)
           in
             ((Binding.qualified_name (tname ^ "_cases"),
              [Attrib.internal (fn _ => Induct.cases_type tname)]), [([cases_rule], [])])
           end))
      |> snd
      |> Variable.variant_fixes (replicate (length full_int_tycos) "'a")
      ||>> Variable.variant_fixes (replicate (length constrs) "constr_int")
      ||>> Variable.variant_fixes (replicate (length relations) "rhs_rel")
    val tycos_int =
      full_int_tycos ~~ tyco_int_ns |> map (fn ((k, _), n) => (k, TFree(n, HOLogic.typeS)))
    fun type_int (Type(k, Ts)) = 
        (case AList.lookup (op =) tycos_int k of
          SOME T => T
        | NONE => Type(k, map type_int Ts))
      | type_int T = T
    val constr_int_frees = constrs ~~ constr_int_ns |> map (fn ((_, T), n) => Free(n, type_int T))
    val rel_int_frees = relations ~~ rel_int_ns |> map (fn ((_, T), n) => Free(n, type_int T))
    val int_frees = constr_int_frees @ rel_int_frees
    (* TODO(semantics): in neueren Isabelle-Version soll lthy4 ein neues Target werden.
        Die fixes sind dann lokal und werden bei einem nachfolgenden restore einfach vergessen. *)
    (* auch im Target fixen damit defines bzgl dieser fixes lambda-geliftet werden *)
    val lthy4 = lthy3 |> fold Variable.declare_constraints int_frees
      |> Local_Theory.target (fn lthy' =>
           let
             val ns = tyco_int_ns @ constr_int_ns @ rel_int_ns
             val (ns', lthy'') = Variable.variant_fixes ns lthy'
               ||> fold Variable.declare_constraints int_frees
             val _ =
               if ns' = ns then ()
               else
                 error ("nonfreedata: internal error: inconsistent fixes between "
                   ^"aux and target ctxt in lthy")
           in lthy'' end)
    val int_frees_export_mor = Variable.export_morphism lthy4 lthy2


    val ([iter_name], _) = Variable.variant_fixes ["iter"] lthy4
    fun on_refl_cert th ts = th OF (ts |> map (Thm.reflexive o cterm_of (Proof_Context.theory_of lthy4)))
    fun lookup_pseudoterm print tab index = 
      case AList.lookup (op =) tab index of
        SOME pt => pt
      | NONE => error ("nonfreedata: internal error: no pseudoterm for "^print index)
    val interpr_facts =
      (tycos_int |> maps (fn (k, T') =>
        let val pt = Type(k, tfrees) |> to_pseudotype_i
        in
          [on_refl_cert @{thm decl_alg_interpr_easyI} [pt, Logic.mk_type T'],
           on_refl_cert @{thm decl_iter_name_easyI} [pt,
             Free(pseudofy_name (iter_name^"_"^Long_Name.base_name k), @{typ "'a"})]]
        end))
      @ (constrs ~~ constr_int_frees |> map (fn ((c, T), free) =>
           let val pt =
             case lookup_pseudoterm (Syntax.string_of_term lthy4) sym_to_pt (Free(c, T)) of
               @{term Oper} $ pt => pt
             | _ => error ("nonfreedata: internal error: strange sym_to_pt entry for constr")
           in on_refl_cert @{thm decl_oper_alg_interpr_easyI} [pt, free] end))
      @ (relations ~~ rel_int_frees |> map (fn ((r, T), free) =>
           let val pt = 
             case lookup_pseudoterm (Syntax.string_of_term lthy4) sym_to_pt (Free(r, T)) of
               @{term Rel} $ pt => pt
             | _ => error ("nonfreedata: internal error: strange sym_to_pt entry for relation")
           in on_refl_cert @{thm decl_rel_alg_interpr_easyI} [pt, free] end))

    val lthy5 = lthy4
      |> MetaRec.set_running_expl_frules true
      |> MetaRec.add_facts_decl interpr_facts
      |> MetaRec.run_expl_frules

    val sig_int_ts =
      [@{prop "sig_is sig"}, @{prop "intSt_is intSt"}, @{prop "intOp_is intOp"},
        @{prop "intRl_is intRl"}]
      |> map (the o snd o lookup_oneplace_fact true [] lthy5)
    val hcls_satisfied_t =
      list_comb
        (Const(@{const_name "NonFreeAnimation.hcls_satisfied"},
           map fastype_of sig_int_ts ---> @{typ bool}),
         sig_int_ts)
      |> HOLogic.mk_Trueprop
    val (calc_reified_hcls_th, [reified_hcls_t]) =
      MetaRec.metarec lthy5 "NonFreeAnimation.calc_reified_hcls_jud" (hd sig_int_ts, tl sig_int_ts)
    val reified_hcls = reified_hcls_t |> HOLMetaRec.metaize_list |> map HOLogic.mk_Trueprop
    val (reified_hcls_ths, lthy6) = lthy5
      |> Assumption.add_assumes (map (cterm_of (Proof_Context.theory_of lthy5)) reified_hcls)
    val all_reified_hcls_th =
      let 
        val ss = (Simplifier.context lthy6 empty_ss) addsimps @{thms ball_unroll_simps}
        val goal =
          Const(@{const_name "Ball"}, @{typ "bool set => (bool => bool) => bool"})
            $ (Const(@{const_name "set"}, @{typ "bool list => bool set"}) $ reified_hcls_t)
            $ (Abs("P", @{typ "bool"}, Bound 0))
          |> HOLogic.mk_Trueprop
      in
        Goal.init (cterm_of (Proof_Context.theory_of lthy6) goal)
        |> (Simplifier.simp_tac ss 1
           THEN REPEAT_DETERM_FIRST (rtac @{thm conjI} ORELSE' rtac @{thm TrueI})
           THEN ALLGOALS (resolve_tac reified_hcls_ths THEN_ALL_NEW atac))
        |> Seq.hd
        |> Goal.conclude
      end
    val hcls_satisfied = @{thm reified_hcls_to_hcls_satisfied} OF
      [calc_reified_hcls_th, all_reified_hcls_th]




    (* TODO(opt): better free the scope now? *)
    val lthy7 = lthy6
      |> MetaRec.set_running_expl_frules true
      |> MetaRec.add_facts_decl [hcls_satisfied]
      |> MetaRec.run_expl_frules

    val (iter_op_rews, iter_rel_rews) =
      ((@{term "iter_op_clauses P"}, true), (@{term "iter_rel_clauses P"}, false))
      |> pairself (fn (pat, mandatory) =>
           lookup_oneplace_fact mandatory [@{thm iter_op_clauses_def}, @{thm iter_rel_clauses_def}]
             lthy7 pat |> fst)
    val (iterators, iter_rews_for_tycos) = ([], []) |> fold (fn th => fn (iterators, iter_rews_for_tycos) =>
        (* th : iter_s (Constr args) = oper_int ... *)
        let
          val f = th |> prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst |> head_of
          val T = fastype_of f |> domain_type
        in
          (insert (op =) (T, f) iterators,
           AList.map_default (op =) (T, []) (cons th) iter_rews_for_tycos)
        end)
      iter_op_rews

        
    val lthy8 = lthy7
      |> MetaRec.add_non_pervasive_declaration (fn _ => MetaRec.set_scope MetaRec.base_scope)
      |> Local_Theory.notes (iter_rews_for_tycos |> map (fn (T, iter_rews_on_T) =>
           let val tname = case T of Type(k, _) => k
           in
             ((Binding.qualified_name (tname ^ "_iter_rews"), []), [(rev iter_rews_on_T, [])])
           end))
      |> snd
      |> MetaRec.add_non_pervasive_declaration (fn mor =>
          fold (fn (int_tyco, tvs) => fn gctxt =>
              let
                val int_tyco' =
                  case
                    Type(int_tyco, map (fn n => TFree(n, HOLogic.typeS)) tvs)
                    |> Morphism.typ mor
                  of
                    Type(int_tyco', _) => int_tyco'
                  | _ => error "nonfreedata: internal error: strange morphism effect on internal tyco"

                (* TODO(brittle): nutzt aus das int_frees_export_mor keinen
                     Effekt hat wenn die int_frees schon exportiert worden sind *)
                val int_frees' = int_frees |> map (Morphism.term mor)
                val mor' =
                  case gctxt of
                    Context.Theory _=> mor
                  | Context.Proof ctxt =>
                      let
                        val assm_frees = []
                          |> fold Term.add_frees (Assumption.all_assms_of ctxt |> map Thm.term_of)
                      in
                        if assm_frees |> exists (fn (n,T) => member (op aconv) int_frees' (Free(n,T))) then
                          mor
                        else
                          mor $> int_frees_export_mor
                      end
                val term = Morphism.term mor'
                val data = {
                  (* TODO(brittle): nutzt das Frees entstehen (ueber Local_Defs) *)
                  constructors = constrs |> map (fn (n, T) =>
                    (Free(n,T) |> term, binder_types T |> map classify_type_i)), 
                  relations = relations |> map (fn (n, T) => Free(n,T) |> term), 
                  constr_int_vars = constr_int_frees |> map term,
                  rel_int_vars = rel_int_frees |> map term,
                  iterators = iterators |> map (apfst (Morphism.typ mor') #> apsnd term),
                  iter_rews = iter_op_rews @ iter_rel_rews |> map (Morphism.thm mor'),
                  reified_hcls = reified_hcls |> map term }
              in
                gctxt |> Data.map (Symtab.update_new (int_tyco', data))
              end)
            full_int_tycos)
  in
    Local_Theory.restore lthy8
  end






(*
  nonfreeiter
    f_1, ..., f_n
  where
    f_i params_i (Constr_j x_k ...) = rhs_i
    rel interpretedas rel_interpretation
*)
fun iter_cmd fixes clause_strs lthy =
  let
    val ((fixes', attr_clauses), _) = 
      Specification.read_spec fixes clause_strs lthy
    val fixes_frees = fixes' |> map (fn ((bnd, T), _) => Free(Binding.name_of bnd, T))
    (* TODO: support bindings and attributes *)
    val clauses = map snd attr_clauses
    fun illformed clause msg =
      error ("nonfreeiter: ill-formed clause: "^Syntax.string_of_term lthy clause^"\n"^msg)

    val strip_clause = Term.strip_all_body #> HOLogic.dest_Trueprop #> try HOLogic.dest_eq
    val (first_tyco, {constructors, relations, constr_int_vars, rel_int_vars,
      iterators, iter_rews, reified_hcls, ...}) =
        clauses |> get_first (fn clause =>
             case strip_clause clause |> Option.map (fst #> strip_comb) of
               SOME (Free(f, fT), args) =>
                 if null args then NONE
                 else
                   let 
                     val quants = Term.strip_all_vars clause
                     val quants_len = length quants
                     fun quant_sel i = nth quants (quants_len - i - 1)
                     val T1 as Type(tyco, _) = 
                       case nth (binder_types fT) (length args - 1) of
                         Type(tyco, Ts) => Type(tyco, Ts)
                       | _ => illformed clause "domain of function not a type constructor application"
                   in
                     case Symtab.lookup (Data.get (Context.Proof lthy)) tyco of
                         SOME data => SOME (tyco, data)
                       | NONE =>
                           illformed clause
                             ("argument type "^Syntax.string_of_typ lthy T1
                               ^" of function not of a nonfree datatype")
                   end
             | _ => NONE)
        |> (fn res_opt =>
           case res_opt of
             SOME res => res
           | NONE => error "nonfreeiter: no wellformed equations. perhaps wrong fixes?")

    val (tyco_int, mk_constr_int, rel_int, Tinst0, params_opt) = ([], [], [], Vartab.empty, NONE)
      |> fold (fn clause => fn (tyco_int, mk_constr_int, rel_int, Tinst, params_opt) =>
         case strip_clause clause |> Option.map (apfst strip_comb) of
           SOME ((ft as Free(_, fT), args), rhs) =>
             let 
               val quants = Term.strip_all_vars clause
               val quants_len = length quants
               fun quant_sel i = nth quants (quants_len - i - 1)
               val T1 as Type(tyco, _) = 
                 case nth (binder_types fT) (length args - 1) of
                   Type(tyco, Ts) => Type(tyco, Ts)
                 | _ => illformed clause "domain of function not a type constructor application"
               val T2 = drop (length args) (binder_types fT) ---> body_type fT
               val _ =
                 case Symtab.lookup (Data.get (Context.Proof lthy)) tyco of
                   SOME _ => ()
                 | NONE =>
                     illformed clause
                       ("argument type "^Syntax.string_of_typ lthy T1
                         ^" of function not of a nonfree datatype"
                         ^"\n  args are "
                         ^cat_lines (map (fn Bound i => Syntax.string_of_term lthy (Free (quant_sel i))) args))
               val _ = 
                 if null args then illformed clause "function not applied to constructor"
                 else ()

               val params_len = length args - 1
               val params2 = take params_len args
               val _ =
                 if params2 |> exists (not o Term.is_Bound) then
                   illformed clause "function parameters are not variables"
                 else if params2 |> has_duplicates (op =) then
                   illformed clause "function parameters are not distinct"
                 else
                   ()
               val params2' = params2 |> map (fn Bound i => quant_sel i |> Free)
               val params_opt' = case params_opt of
                 SOME params =>
                   if params2' = params then params_opt
                   else
                     illformed clause "parameters differ"
               | NONE => SOME params2'

               val (constr, constr_args) = strip_comb (nth args params_len)
               val thy = Proof_Context.theory_of lthy
               val (Tinst', constr_arg_kinds, constr_int_var) =
                 case
                   get_first (fn ((constr', constr_arg_kinds), constr_int_var) => 
                       let
                         val maxidx = ~1 |> fold Term.maxidx_term [constr, constr']
                       in
                         case try (Pattern.first_order_match thy (constr', constr))
                           (Tinst, Vartab.empty) of
                           NONE => NONE
                         | SOME (Tinst', _) => SOME (Tinst', constr_arg_kinds, constr_int_var)
                       end)
                     (constructors ~~ constr_int_vars)
                 of
                   SOME x => x
                 | NONE =>
                     illformed clause "function not applied to a constructor (of matching type)"
               val _ = 
                 if constr_args |> forall Term.is_Bound then ()
                 else
                   illformed clause "function not applied to constructor on variables"
               val _ =
                 if has_duplicates (op =) constr_args then
                   illformed clause "constructor applied to non-distinct variables"
                 else ()
               val constr_args' = constr_args |> map (fn Bound i => quant_sel i |> Free)

                 (* parameters are not abstracted *)
               fun mk_abstr_rhs final_funfrees =
                 let
                   val rhs_subst =
                     rhs |> curry subst_bounds (rev (map Free quants))
                   val structarg_to_funapp = [] |> fold_applied_heads (fn (h, ts) => fn structarg_to_funapp =>
                       if not (member (op =) final_funfrees h) then structarg_to_funapp
                       else
                         let
                           val params3 = take params_len ts
                           val _ =
                             if params3 = params2' then ()
                             else
                               illformed clause ("function "^Syntax.string_of_term lthy h
                                 ^" in rhs is applied to different parameters "
                                 ^Library.commas (map (Syntax.string_of_term lthy) params3))

                           fun structarg_err () =
                             illformed clause ("function "^Syntax.string_of_term lthy (list_comb (h, ts))
                               ^" in rhs is not applied to the structural decreasing argument")
                           val structarg =
                             case drop params_len ts of
                               structarg :: _ => structarg
                             | [] => structarg_err ()
                           val _ = 
                             if member (op =) constr_args' structarg then ()
                             else structarg_err ()
                           val app = list_comb (h, params3 @ [structarg])
                         in
                           case AList.lookup (op aconv) structarg_to_funapp structarg of
                             NONE =>
                               cons (structarg, app) structarg_to_funapp
                           | SOME app' =>
                               if app' aconv app then structarg_to_funapp
                               else
                                 error ("nonfreeiter: internal error: different function applications "
                                   ^"on structuraly decreasing argument "^Syntax.string_of_term lthy h
                                   ^" ?!")
                         end)
                     rhs_subst
                 in
                   rhs_subst
                   |> fold_rev (fn ((free as Free(n, T), kind), int_arg_T) =>
                          case kind of
                             (* FIXME? auch int_arg_T nutzen damit Parameter-Typen uminterpretiert werden koennen? *)
                            ParameterType => absfree (n, T)
                          | InternalType =>
                              (case AList.lookup (op aconv) structarg_to_funapp free of
                                SOME app => Term.lambda_name (n, app)
                              | NONE => absfree (n, int_arg_T)))
                        ((constr_args' ~~ constr_arg_kinds) ~~
                          (fastype_of constr_int_var |> Term.binder_types))
                 end
               val _ =
                 if AList.defined (op =) mk_constr_int constr_int_var  then
                   illformed clause "two clauses for the same constructor"
                 else ()
               val mk_constr_int' = cons (constr_int_var, (constr, mk_abstr_rhs)) mk_constr_int
             in
               case AList.lookup (op =) tyco_int tyco of
                 SOME (T2', ft') =>
                   if T2 <> T2' then
                     illformed clause ("type constructor "^quote tyco^" gets inconsistent interpretations")
                   else if ft' <> ft then
                     illformed clause "serveral functions on the same type constructor"
                   else
                     (tyco_int, mk_constr_int', rel_int, Tinst', params_opt')
               | NONE =>
                     (cons (tyco, (T2, ft)) tyco_int, mk_constr_int', rel_int, Tinst', params_opt')
             end
         | NONE =>
             let
               val (lhs, rhs) =
                 case Term.strip_all_body clause of
                   Const(@{const_name "Trueprop"}, _) $
                     (Const(@{const_name "interpretedas_const"}, _)$ lhs $ rhs) => (lhs, rhs)
                 | _ => illformed clause "not an equation and not a relation interpretation"
               val (lhshead, lhsargs) = strip_comb lhs
               val _ =
                 if null lhsargs then ()
                 else
                   illformed clause "lhs is a function application and not a relation"
               val (Tinst', rel_int_var) =
                 case
                   get_first (fn (rel, rel_int_var) =>
                       let val maxidx = ~1 |> fold Term.maxidx_term [lhshead, rel]
                       in
                         case
                           try (Pattern.first_order_match (Proof_Context.theory_of lthy) (rel, lhshead))
                             (Tinst, Vartab.empty)
                         of
                           NONE => NONE
                         | SOME (Tinst', _) => SOME (Tinst', rel_int_var)
                       end)
                     (relations ~~ rel_int_vars)
                 of
                   SOME x => x
                 | NONE =>
                     illformed clause
                       "lhs is not a relation application"
             in
               if AList.defined (op =) rel_int rel_int_var then
                 illformed clause "duplicate relation interpretation"
               else
                 (tyco_int, mk_constr_int, cons (rel_int_var, (lhshead, rhs)) rel_int, Tinst', params_opt)
             end)
       clauses

    val final_funfrees = tyco_int |> map (fn (_, (_, ft)) => ft)
    val (constr_int, (Tinst, _)) = (Tinst0, 0)
      |> fold_map (fn (constr_int_var, (constr, mk_rhs)) => fn (Tinst', maxidx) =>
        let
          val rhs = mk_rhs final_funfrees
          val rhsT = fastype_of rhs
          val varT = fastype_of constr_int_var
          val maxidx2 = Term.maxidx_typs [rhsT, varT] maxidx
          (* val _ = tracing ("matching "^Syntax.string_of_term lthy rhs
              ^" :: "^Syntax.string_of_typ lthy rhsT
            ^" against "^Syntax.string_of_typ lthy varT
            ^"  (constructor is "^Syntax.string_of_term lthy constr^")") *)
          val (Tinst'', maxidx3) = Sign.typ_unify (Proof_Context.theory_of lthy) (varT, rhsT) (Tinst', maxidx2)
            handle TYPE_MATCH =>
              error ("nonfreeiter: internal error: constructor interpretation type mismatch"
                ^"\n constructor: "^Syntax.string_of_term lthy constr
                   ^"  :: "^Syntax.string_of_typ lthy (fastype_of constr) 
                ^"\n rhs: "^Syntax.string_of_term lthy rhs^" :: "^Syntax.string_of_typ lthy rhsT
                ^"\n constr_int_var: "^Syntax.string_of_term lthy constr_int_var
                   ^"  :: "^Syntax.string_of_typ lthy varT
                ^"\n instantiated constr_int_var type: "
                   ^"  :: "^Syntax.string_of_typ lthy (Envir.norm_type Tinst' varT))
        in
          ((constr_int_var, (constr, rhs)), (Tinst'', maxidx3))
        end)
      mk_constr_int 
    val Tinst_l = Vartab.dest Tinst |> map (fn (ixn, (S, T)) => ((ixn, S), T))
    val normT_term = Envir.norm_term
      (Envir.Envir { maxidx = ~1 |> fold Term.maxidx_term clauses,
        tenv = Vartab.empty, tyenv = Tinst})
    val params = these params_opt
    val constructors_inst = map fst constructors |> map normT_term
    val relations_inst = relations |> map normT_term

    val untreated_constrs = constructors_inst |> subtract (op = o apfst (snd #> fst)) constr_int
    val _ =
      if null untreated_constrs then ()
      else
        error ("nonfreeiter: function definition on constructors "^
          Library.commas (map (Syntax.string_of_term lthy) untreated_constrs)
          ^" not given")
    val untreated_rels = relations_inst |> subtract (op = o apfst (snd #> fst)) rel_int
    val _ =
      if null untreated_rels then ()
      else
        error ("nonfreeiter: relations  "
          ^Library.commas (map (Syntax.string_of_term lthy) untreated_rels)
          ^" not interpreted")

    val tinst_l = constr_int @ rel_int |> map (fn (var, (_, rhs)) =>
      case var of
        Var(ixn, T) =>
          ((ixn, Envir.norm_type Tinst T),
           Envir.norm_term (Envir.Envir {maxidx=0, tenv=Vartab.empty, tyenv=Tinst}) rhs)
      | _ => error "nonfreeiter: internal error: constr_int_var or rel_int_var is not a Var")

    
    val (fold_def_ths, lthy2) = lthy
      |> fold_map (fn (tyco, (_, ft)) => fn lthy' =>
          let
            val iter =
              case
                iterators |> get_first (fn (T, iter) =>
                  case T of
                    Type(tyco', _) =>
                      if tyco = tyco' then SOME iter
                      else NONE
                  | _ => error "nonfreeiter: internal error: strange indexing type in iterator alist")
              of
                SOME iter => iter
              | NONE => error ("nonfreeiter: internal error: no iterator found for tyco "^quote tyco)

            val iter_inst = iter |> Term_Subst.instantiate (Tinst_l, tinst_l)
            val bnd = Binding.name (Term.dest_Free ft |> fst)
            val rhs = iter_inst |> fold_rev (absfree o Term.dest_Free) params
            (* val _ = tracing ("Tinst_l:  "^commas (Tinst_l |> map (fn (ixnS, T) =>
               Syntax.string_of_typ lthy' (TVar(ixnS)) ^" := "^Syntax.string_of_typ lthy' T)))
            val _ = tracing ("tinst_l:  "^commas (tinst_l |> map (fn (ixnT, t) =>
               Syntax.string_of_term lthy' (Var(ixnT)) ^" := "^Syntax.string_of_term lthy' t)))
            val _ = tracing ("iter_inst:  "^Syntax.string_of_term lthy' iter_inst)
            val _ = tracing ("rhs:  "^Syntax.string_of_term lthy' rhs) *)
            val ((lhs, (n, def_th)), lthy'2) = lthy'
              |> Local_Theory.define ((bnd, NoSyn), ((Thm.def_binding bnd, []), rhs))
            val def_th' = Raw_Simplifier.rewrite_cterm (false, false, false) (fn _ => fn _ => NONE)
              (Simplifier.context lthy'2 empty_ss  addsimps  [def_th])
              (cterm_of (Proof_Context.theory_of lthy'2) (list_comb (lhs, params)))
          in
            (Thm.symmetric def_th', lthy'2)
          end)
        tyco_int
    val (params', lthy3) = lthy2 |> Variable.variant_fixes (map (fst o Term.dest_Free) params)
      ||> fold Variable.declare_constraints params
    val _ =
      if map (fst o Term.dest_Free) params = params' then ()
      else error "nonfreeiter: internal error: parameters names were already taken?!"

    val goals = reified_hcls |> map (Term_Subst.instantiate (Tinst_l, tinst_l) #> Envir.beta_norm)
    val thy3 = Proof_Context.theory_of lthy3
    val cinst = (Tinst_l |> map (fn ((ixn, S), T) => (TVar(ixn, S), T) |> pairself (ctyp_of thy3)),
      tinst_l |> map (fn ((ixn,T), t) => (Var(ixn,T), t) |> pairself (cterm_of thy3)))

    fun after_qed [goal_ths] lthy4 = 
      let
        val iter_rews' = iter_rews |> map (fn iter_rew =>
            (Thm.instantiate cinst iter_rew OF goal_ths)
            |> Raw_Simplifier.simplify false fold_def_ths)
          |> Variable.export lthy3 lthy2
        val first_funfree_n =
          case final_funfrees of Free(n, _) :: _ => n
            | _ => error "nonfreeiter: internal error: no function frees?!"
        val simp_bnd = Binding.qualify true first_funfree_n (Binding.name "simps")
        fun match_cls clause th =
          let
            fun get_constr cls =
              let
                val args = cls |> strip_clause |> the |> fst |> strip_comb |> snd
                val constr = nth args (length args - 1) |> strip_comb |> fst
              in constr end
          in
            get_constr (prop_of th) = get_constr clause
          end
      in
        lthy4
        |> Local_Theory.notes [((simp_bnd, [Attrib.internal (fn _ => Simplifier.simp_add)]), [(iter_rews', [])])]
        |> snd
        |> Local_Theory.notes (attr_clauses |> map_filter (fn (attr, clause) =>
             if clause |> strip_clause |> is_some then
               case find_first (match_cls clause) iter_rews' of
                 SOME th =>
                   SOME (attr, [([th], [])])
               | NONE =>
                   error ("nonfreeiter: internal error: no iterator rewriting clause for "
                     ^Syntax.string_of_term lthy4 clause)
             else
               NONE))
        |> snd
      end
    val refine_goals_tac = REPEAT_DETERM_FIRST (resolve_tac [@{thm allI}, @{thm impI}])
  in
    (* TODO(correctness): goal is its own goal pattern?
         declare constraints of params in lthy3 ?? *)
    Proof.theorem NONE after_qed [(goals |> map (fn goal => (goal, [goal])))] lthy3
    |> Proof.refine (Method.primitive_text (refine_goals_tac #> Seq.hd))
    |> Seq.hd
  end


local

fun prep_datatype_decls (args, named_hcls_opt) =
  let
    val tyco_names = map (fn ((_, tyco), _) => Binding.name_of tyco) args
    val specs = map (fn ((vs, tyco), cons) => (vs, tyco, cons)) args
  in (tyco_names, specs, these named_hcls_opt) end

val parse_datatype_decl =
  ( Parse.type_args_constrained -- Parse.binding --
    (Parse.$$$ "=" |-- Parse.enum1 "|" (Parse.binding -- Scan.repeat Parse.typ)))

val parse_datatype_decls =
  Parse.and_list1 parse_datatype_decl
  -- Scan.option Parse_Spec.where_alt_specs
  >> prep_datatype_decls

val parse_iter_clauses =
  Parse.fixes -- Parse_Spec.where_alt_specs

in

val _ =
  Outer_Syntax.local_theory @{command_spec "nonfreedata"}
    "definition of non-freely generated datatypes"
    (parse_datatype_decls >> (fn (tyco_names, specs, named_hcls) =>
      datatype_cmd tyco_names specs named_hcls))
val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "nonfreeiter"}
    ("definition of primitive recursive functions on non-freely generated datatypes "
      ^"(requires compatibility with equational consequences of the horn theory)")
    (parse_iter_clauses >> (fn (fixes, clauses) => iter_cmd fixes clauses))

end

end
