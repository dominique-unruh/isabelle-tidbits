structure Wlog : sig

val wlog : Position.T -> (* Position (for bindings and markup) *)
           binding * term -> (* New assumption *)
           term -> (* Goal to operate on *)
           (binding * string * typ) list -> (* Generalizing *)
           (string * thm list) list -> (* Assumptions to keep *)
           bool -> (* internal (as in Proof.show, Proof.have) *)
           Proof.state -> Proof.state

val wlog_cmd : Position.T -> binding * string -> string -> binding list -> (Facts.ref * Token.src list) list -> bool -> Proof.state -> Proof.state

end =
struct

fun print_entity_binding entity binding = 
  Pretty.marks_str ([Position.entity_markup entity (Binding.name_of binding, Binding.pos_of binding)], Binding.name_of binding) |> Pretty.string_of

val print_fact_binding = print_entity_binding Markup.factN

fun print_term_as_statement ctxt heading term = 
  Element.pretty_statement ctxt heading (Thm.assume (Thm.cterm_of ctxt term)) |> Pretty.string_of

val wlog_lost_facts_prefix = "lost"

fun binding_within qualifier pos name = let
  val (path, name) = split_last (Long_Name.explode name)
  val path = case path of "local" :: path => path | path => path
  val path = case path of p :: ps => if p = wlog_lost_facts_prefix then ps else ps | ps => ps 
  val binding = Binding.make (name,pos)
      |> fold_rev (fn qualifier => fn b => Binding.qualify true qualifier b) path
      |> Binding.qualify true qualifier
in binding end

(* Proves premise i using facts if possible. Otherwise, just leaves it in place. *)
fun prove_prem_if_possible ctxt facts i thm = let
  val prem = nth (Thm.prems_of thm) (i-1)
  val candidates = Facts.could_unify facts prem |> map fst
  val result = solve_tac ctxt candidates i thm |> Seq.pull |> Option.map fst
in case result of SOME thm => thm | NONE => thm end


(* Given a theorem thm, replaces all occurrences of the free vars "fixes" by the free vars "fixed".
   For any hypothesis of thm that is not a fact in the context "ctxt", a premise is added to the theorem.
   (Thus, the resulting theorem will be valid in "ctxt")

   fixes is a list of (_,n,T) where n is the var name and T the type

   fixed is a list of variable names (types will be the same).
 *)
fun translate_thm ctxt fixes fixed thm = 
  let val hyps = Thm.chyps_of thm
      (* Make all hypotheses of thm into premises (using \<Longrightarrow>) *)
      val thm = fold_rev Thm.implies_intr hyps thm
      val idx = Thm.maxidx_of thm + 1
      (* Replace all free vars in "fixes" by schematic vars of the same name *)
      val thm = Thm.generalize (Names.empty, map #2 fixes |> Names.make_set) idx thm
      (* And now replace those schematic vars by the free variables in `fixes` *)
      val thm = thm |> Thm.instantiate (TVars.empty,
        map2 (fn (_,n,T) => fn m => (((n,idx),T), Thm.cterm_of ctxt (Free (m,T)))) fixes fixed |> Vars.make)
      val facts = Proof_Context.facts_of ctxt
      (* And now prove all the assumptions (that were hypotheses) where this is possible by applying a fact from the context. *)
      val thm = fold (prove_prem_if_possible ctxt facts) (length hyps downto 1) thm
   in thm end

(* TODO: Use something like map_aterms or something? *)
fun ren_frees [] = I
  | ren_frees pairs =
      let fun substf u =
            case u of Abs(a,T,t) => Abs(a, T, substf t)
                    | t$u' => substf t $ substf u'
                    | Free(n,T) => (case AList.lookup (op=) pairs n of
                                      SOME n' => Free(n',T)
                                    | NONE => u)
                    | _ => u
      in  substf  end;

(* We only support negation of bools here (not something like "\<And>P. t \<Longrightarrow> P") because it is not clear
   how to prove negation_tac below otherwise. *)
fun negate _ (Const(@{const_name Trueprop},_) $ t) = HOLogic.mk_Trueprop (HOLogic.mk_not t)
  | negate ctxt t = error ("The wlog-assumption must be of type bool (i.e., don't use \<Longrightarrow>, \<And>, &&&). You specified: " ^ Syntax.string_of_term ctxt t)

(* Assumes: goal=X, thm=\<not>Y\<Longrightarrow>X, hyp_thm="Y\<Longrightarrow>A\<^sub>1\<Longrightarrow>\<dots>\<Longrightarrow>A\<^sub>n\<Longrightarrow>X", assms=[A1,\<dots>,A\<^sub>n] *)
fun negation_tac ctxt thm hyp_thm assms = 
  (* Goal: X *)
  resolve_tac ctxt (@{thms HOL.case_split}) 1
  THEN
  (* Goal: ?P\<Longrightarrow>X, \<not>?P\<Longrightarrow>X  *)
  solve_tac ctxt [thm] 2
  THEN  
  (* Goal: Y\<Longrightarrow>X  *)
  resolve_tac ctxt [hyp_thm] 1
  THEN
  (* Goal: Y\<Longrightarrow>Y, A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  assume_tac ctxt 1
  (* Goal: A1\<Longrightarrow>Y, \<dots>, An\<Longrightarrow>Y  *)
  THEN
  ALLGOALS (fn i => (@{print} (assms,i); resolve_tac ctxt [nth assms (i-1)] i))

(* Prefix put in front of "lost" facts. *)
val wlog_lost_facts_prefix = "lost"

(* 
wlog wlogassmname: \<open>wlogassm\<close> goal G generalizing x y z keeping fact1 fact2
  [\<dots> your proof \<dots>]

(Defaults: goal ?thesis generalizing <nothing> keeping <nothing>)

translates roughly to:

  presume hypothesis[case_names wlogassmname fact1 fact2]:
    \<open>\<And>x y z. \<lbrakk>wlogassm; fact1; fact2\<rbrakk> \<Longrightarrow> ?thesis\<close>
  have \<open>G\<close> if negation: \<open>\<not> wlogassm\<close>
    [\<dots> your proof \<dots>]
  then show \<open>G\<close>
    [\<dots> autogenerated proof \<dots>]
next
  fix x y z
  (* Below, in all terms, occurrences of x y z renamed to the fixed x y z *)
  let ?wlog_goal = \<open>[what ?thesis was before]\<close>
  let ?x = \<open>[what ?x was before]\<close> (* for each ?x that was defined before; with occurrences of x y z renamed to the fixed x y z *)
  assume wlogassmname: \<open>wlogassm\<close>  
  assume fact1: \<open>fact1\<close>
  assume fact2: \<open>fact2\<close>
  have lost.xxx: \<open>assms \<Longrightarrow> xxx\<close> 
     (* For any fact xxx: \<open>xxx\<close> that was present in the proof before the wlog command.
         assms are the assumptions that were present in the context before "next" (e.g., via assume command).
         (Assumptions that still hold, e.g., "fact1", "fact2", are removed automatically from assms.) *)
    [\<dots> proof carried over \<dots>]

*)
fun wlog (pos:Position.T) (newassm_name, newassm) (goal: term)
    (fixes: (binding*string*typ) list)
    (assms: (string*thm list) list) int state =
  let
      (* val _ = @{print} (Proof.goal state) *)
      val ctxt = Proof.context_of state
      val facts = Proof_Context.facts_of ctxt
      (* flat_assms: list of (name,i,t) where t are all assumptions, with i an index to distinguish several propositions in the same fact. (i=0 if there is only one) *)
      val flat_assms = assms |> map (fn (name,thms) => case thms of [th] => [(name,0,Thm.prop_of th)]
                                                          | _ => map_index (fn (i,thm) => (name,i+1,Thm.prop_of thm)) thms) |> List.concat
      fun idx_name (name,0) = name | idx_name (name,i) = name ^ "_" ^ string_of_int i
      val flat_assms = (Binding.name_of newassm_name, 0, newassm) :: flat_assms
      val hyp = Logic.list_implies (map #3 flat_assms, goal)
      val hyp = fold (fn (_,a,T) => fn t => Logic.all_const T $ (Term.absfree (a,T) t)) fixes hyp
      val case_names = map (fn (name,i,_) => idx_name(name,i)) flat_assms
      val case_names = Rule_Cases.cases_hyp_names case_names (map (K []) case_names)
      val negated_newassm = negate ctxt newassm
      val _ = Output.information ("Please prove that \"" ^ print_fact_binding newassm_name ^ "\" can be assumed w.l.o.g.\nYou may use the following facts:\n" ^
            print_term_as_statement ctxt "hypothesis:" hyp ^ "\n" ^ print_term_as_statement ctxt "negation:" negated_newassm)

      val state = Proof.presume [] [] [((Binding.make ("hypothesis", pos), [case_names]), [(hyp,[])])] state
      val hyp_thm = Proof.the_fact state

      fun after_qed (_,_) state = 
      let 
          val proven_thm = Proof.the_fact state
          val (_,state) = Proof.show true NONE (fn _ => I) [] [] 
                             [((Binding.empty,[]),[(goal,[])])] int state
          val state = Proof.apply (Method.Basic (fn ctxt => 
              (Method.SIMPLE_METHOD (negation_tac ctxt proven_thm hyp_thm (assms |> map snd |> List.concat)))),
                      Position.no_range) state
              |> Seq.the_result "internal error: negation_tac failed"
          val state = Proof.local_done_proof state
          val ctxt_before_next = Proof.context_of state
          val let_bindings = Variable.binds_of ctxt_before_next |> Vartab.dest
          val state = Proof.next_block state
          val lost_facts = Facts.dest_static false [Proof_Context.facts_of (Proof.context_of state)] facts
                  |> filter (fn (name,_) => name <> "local.this")
          val _ = @{print} ("lost_facts",map #1 lost_facts)
          val (fixed,state) = Proof.map_context_result (Proof_Context.add_fixes (map (fn (a,_,T) => (a,SOME T,NoSyn)) fixes)) state
          val rename_fixed = ren_frees (map2 (fn (_,a,_) => fn b => (a,b)) fixes fixed)
          val state = fold (fn (name,(_,t)) => Proof.map_context (Variable.bind_term (name,rename_fixed t))) let_bindings state
          val state = Proof.map_context (Variable.bind_term (("wlog_goal",0),rename_fixed goal)) state
          val state = fold (fn (name,assm) => fn state => 
                        Proof.assume [] [] [((Binding.name name,[]), map (fn t => (rename_fixed (Thm.prop_of t),[])) assm)] state) assms state
          val ctxt = Proof.context_of state
          fun export thm = translate_thm ctxt fixes fixed thm
          val state = Proof.note_thmss (map (fn (name,thms) => ((binding_within wlog_lost_facts_prefix pos name, []),
                        [(map export thms, [])])) lost_facts) state
          val state = Proof.assume [] [] [((newassm_name,[]),[(rename_fixed newassm,[])])] state (* Should be last in order to override "this" *)
          (* TODO: define assms to contain all assumptions (carried over and new) *)
          (* TODO: Print info about "lost facts". *)
      in state end

      val (_,state) = Proof.have true NONE after_qed [] 
             [((Binding.make ("negation", pos),[]), [(negated_newassm, [])])]
             [((Binding.empty,[]), [(goal,[])])] int state
  in state end

fun wlog_cmd (pos: Position.T) 
             ((bind,stmt) : Binding.binding * string) (* New assumptions added wlog *)
             (goal: string) (* Which goal to work on (should be something that "show" accepts. *)
             (fixes : binding list) (* Variables to be generalized *)
             (assms : (Facts.ref * Token.src list) list) (* Assumptions to keep *)
             int state =
  let val ctxt = Proof.context_of state
      val stmt = Syntax.read_prop ctxt stmt                                 
      val assms' = map (fn (fact,_) => (Facts.ref_name fact, Proof_Context.get_fact ctxt fact)) assms
      val goal' = Syntax.read_prop ctxt goal
      val constr = Variable.constraints_of ctxt |> #1
      val fixes' = map (fn b => let val internal = Variable.lookup_fixed ctxt (Binding.name_of b) |> Option.valOf
                                    val T = Vartab.lookup constr (internal,~1) |> Option.valOf
                                in (b,internal,T) end) fixes
      (* val _ = @{print} assms *)
  in wlog pos (bind,stmt) goal' fixes' assms' int state end                 

val wlog_parser = (Scan.optional (Parse.binding --| Parse.$$$ ":") Binding.empty -- Parse.prop) -- 
                  (Scan.optional (@{keyword "goal"} |-- Parse.prop) "?thesis") --
                  (Scan.optional (@{keyword "generalizing"} |-- Scan.repeat Parse.binding) []) --
                  (Scan.optional (@{keyword "keeping"} |-- Parse.thms1) [])
                  |> Parse.position

val _ =
  Outer_Syntax.command @{command_keyword wlog} "Adds an assumption that holds without loss of generality"
    (wlog_parser >> (fn ((((stmt,goal),fixes),assms),pos) => Toplevel.proof' (wlog_cmd pos stmt goal fixes assms)));


(* fun extract_thesis ctx [] [] [(_,[thesis])] = 
  (case Proof_Context.read_propp ctx [[thesis]] |> #1 of
      [[Const ("HOL.Trueprop",_) $ t]] => SOME t
    | _ => NONE)
  | extract_thesis _ _ _ _ = NONE

val _ =
  Outer_Syntax.command @{command_keyword goal} "tests if 'show'ing the given goal will work (i.e., whether 'show' will succeed); also sets ?thesis"
    (Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes >> (fn ((shows, (strict, assumes)), fixes) =>
      Toplevel.proof' (fn int => fn state =>
      (Proof.show_cmd strict NONE (K I) fixes assumes shows int state;
      case extract_thesis (Proof.context_of state) fixes assumes shows of NONE => state
        | SOME t => Proof.map_context (Variable.bind_term (("thesis",0),t)) state
      )))) *)

end
