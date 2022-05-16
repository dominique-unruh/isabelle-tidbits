theory Nondeterministic_Code
  imports Complex_Main "HOL-Library.Code_Target_Numeral" "HOL-Library.Rewrite" "HOL-Library.RBT_Mapping"
begin

section "Generic (trusted base)"

class nondet_rep =
  fixes nondet_sets :: "unit \<Rightarrow> 'a set set"
  assumes nonempty_nondet_sets: "nondet_sets() \<noteq> {}"
  assumes no_empty_nondet_set: "S\<in>nondet_sets() \<Longrightarrow> S\<noteq>{}"
typedef (overloaded) 'a::nondet_rep nondet = "nondet_sets() :: 'a set set" 
  using nonempty_nondet_sets by auto
setup_lifting type_definition_nondet
code_printing 
  type_constructor nondet \<rightharpoonup> (SML) "_ nondet"
  | code_module nondet \<rightharpoonup> (SML) "datatype 'a nondet = Nondet of 'a Unsynchronized.ref"

typedef (overloaded) 'a::nondet_rep updater = 
  "{f::'a\<Rightarrow>'a option. (\<forall>S\<in>nondet_sets(). \<forall>x\<in>S. case f x of Some y \<Rightarrow> y\<in>S | None \<Rightarrow> True)}" 
  morphisms Rep_updater Updater
  apply (rule exI[of _ "\<lambda>_. None"]) by auto
declare Rep_updater_inverse[code abstype]
definition [code del]: "update (f::'a updater) (x::'a nondet) = x"
code_reserved SML update_nondet
code_printing
  code_module update_nondet \<rightharpoonup> (SML) 
    "fun update_nondet f (nd as Nondet r) = (case f (!r) of SOME x => r := x | NONE => (); nd)"
  | constant update \<rightharpoonup> (SML) "(case _ of Updater f => update'_nondet f)"

typedef (overloaded) ('a::nondet_rep) representation =
  "{(x,S) | (x::'a) S. x\<in>Rep_nondet (S())}"
  morphisms Rep_representation Representation
  apply (rule exI[of _ "(SOME x. x\<in>Rep_nondet undefined, (\<lambda>_. undefined))"])
  by (simp add: Rep_nondet no_empty_nondet_set some_in_eq)
declare Rep_representation_inverse[code abstype]
definition [code del]: "make_nondet (x::'a::nondet_rep representation) = snd (Rep_representation x) ()"
code_printing 
  code_module make_nondet \<rightharpoonup> (SML)
    "fun make_nondet x = Nondet (Unsynchronized.ref x)"
  | constant make_nondet \<rightharpoonup> (SML) "(case _ of Representation (x,'_) => make'_nondet x)"

typedef (overloaded) ('a::nondet_rep,'b::nondet_rep) applier = 
  "{(f,g) | (f::'a\<Rightarrow>'b option) (g::'a nondet \<Rightarrow> 'b nondet). 
      (\<forall>x. \<forall>rx\<in>Rep_nondet x. case f rx of Some ry \<Rightarrow> ry \<in> Rep_nondet (g x) | None \<Rightarrow> True)}" 
  morphisms Rep_applier Applier
  by (rule exI[of _ "(\<lambda>_. None, \<lambda>_. undefined)"], auto)
declare Rep_applier_inverse[code abstype]
definition [code del]: "apply a = snd (Rep_applier a)"
code_printing
  code_module apply_nondet \<rightharpoonup> (SML)
    "fun apply_nondet (f,_) (nd as Nondet r) = (case f (!r) of SOME x => make_nondet x 
                                  | NONE => raise Fail \"apply_nondet\")"
  | constant "apply" \<rightharpoonup> (SML) "(case _ of Applier f => apply'_nondet f _)"

typedef (overloaded) ('a::nondet_rep,'b) extractor =
  "{(f,g) | (f::'a\<Rightarrow>'b option) (g::'a nondet \<Rightarrow> 'b).
    (\<forall>x. \<forall>rx\<in>Rep_nondet x. case f rx of Some b \<Rightarrow> b=g x | None \<Rightarrow> True)}"
  morphisms Rep_extractor Extractor
  apply (rule exI[of _ "(\<lambda>_. None, \<lambda>_. undefined)"]) by simp
declare Rep_extractor_inverse[code abstype]
definition [code del]: "extract a = snd (Rep_extractor a)"
code_printing
  code_module extract_nondet \<rightharpoonup> (SML)
    "fun extract_nondet (f,_) (Nondet r) = case f (!r) of SOME x => x | NONE => raise Fail \"extract_nondet\""
  | constant "extract" \<rightharpoonup> (SML) "(case _ of Extractor f => extract'_nondet f _)"

instantiation prod :: (nondet_rep,nondet_rep) nondet_rep begin
definition [code del]: "nondet_sets_prod (_::unit) = {X\<times>Y | X Y. X\<in>nondet_sets() \<and> Y\<in>nondet_sets()}"
instance apply intro_classes
  unfolding nondet_sets_prod_def apply auto
  apply (metis Abs_nondet_cases)
  using no_empty_nondet_set by auto
end

lift_definition pair_nondet :: "'a::nondet_rep nondet \<Rightarrow> 'b::nondet_rep nondet \<Rightarrow> ('a*'b) nondet" is
  "\<lambda>(S::'a set) (T::'b set). (S\<times>T)"
  unfolding nondet_sets_prod_def by auto
code_printing
  constant pair_nondet \<rightharpoonup> (SML) "(case (_,_) of (Nondet a, Nondet b) => make'_nondet (!a,!b))"


section {* Generic (untrusted) *}

setup_lifting type_definition_extractor
setup_lifting type_definition_applier
setup_lifting type_definition_representation
setup_lifting type_definition_updater

definition some_rep :: "'a nondet \<Rightarrow> 'a::nondet_rep" where
  [code del]: "some_rep x = (SOME r. r \<in> Rep_nondet x)"
lemma some_rep: "some_rep x \<in> Rep_nondet x"
  unfolding some_rep_def using Rep_nondet no_empty_nondet_set
  by (simp add: Rep_nondet no_empty_nondet_set some_in_eq) 

lemma Rep_nondet_pair: "\<exists>a' b'. Rep_nondet x = Rep_nondet a' \<times> Rep_nondet b'"
  by (smt Rep_nondet Rep_nondet_inverse eq_onp_same_args mem_Collect_eq nondet_sets_prod_def pair_nondet.abs_eq pair_nondet.rep_eq) 

section "Rationals"

subsection "Representation"

datatype rat_rep = RatRep "int*int" | RatRepNorm rat
fun rat_of_rat_rep where 
  "rat_of_rat_rep (RatRep x) = Fract (fst x) (snd x)"
| "rat_of_rat_rep (RatRepNorm x) = x"


definition "rat_rep_of_rat x = RatRep (quotient_of x)"
lemma rat_rep_of_rat_inverse[simp]: "rat_of_rat_rep (rat_rep_of_rat r) = r" 
  unfolding rat_rep_of_rat_def apply (cases r) by (auto simp: quotient_of_Fract)

instantiation rat_rep :: nondet_rep begin
definition [code del]: "nondet_sets_rat_rep = (\<lambda>(). {(rat_of_rat_rep -` {r})| r. True})"
instance apply intro_classes
  unfolding nondet_sets_rat_rep_def unit.case
   apply auto
  using rat_rep_of_rat_inverse by fastforce
end
lemma two_reps: "rx \<in> Rep_nondet x \<Longrightarrow> rx' \<in> Rep_nondet x \<Longrightarrow> rat_of_rat_rep rx = rat_of_rat_rep rx'"
  by (smt Rep_nondet mem_Collect_eq nondet_sets_rat_rep_def old.unit.case vimage_singleton_eq)

fun simplify_rat_rep where 
  "simplify_rat_rep (RatRep r) = Some (RatRepNorm (Fract (fst r) (snd r)))"
| "simplify_rat_rep (RatRepNorm r) = None"

lemma rat_of_rat_rep_simplify_rat_rep: 
  "simplify_rat_rep r = Some r' \<Longrightarrow> rat_of_rat_rep r' = rat_of_rat_rep r"
  apply (cases r) by auto

fun quotient_of_rat_rep where
  "quotient_of_rat_rep (RatRep (a,b)) = (a,b)"
| "quotient_of_rat_rep (RatRepNorm r) = quotient_of r"
lemma Fract_quotient_of_rat_rep:
  "Fract (fst (quotient_of_rat_rep x)) (snd (quotient_of_rat_rep x)) = rat_of_rat_rep x"
  apply (cases x)
  using rat_rep_of_rat_def rat_rep_of_rat_inverse by auto

fun times_rat_rep' where "times_rat_rep' (a,b) (c,d) = (a*c,b*d)"
definition "times_rat_rep x y = RatRep (times_rat_rep' (quotient_of_rat_rep x) (quotient_of_rat_rep y))"
lemma rat_of_rat_rep_times_rat_rep: "rat_of_rat_rep (times_rat_rep x y) = rat_of_rat_rep x * rat_of_rat_rep y"
  unfolding times_rat_rep_def apply auto
  using Fract_quotient_of_rat_rep
  by (metis (no_types, lifting) mult_rat old.prod.inject prod.collapse times_rat_rep'.simps)

fun inverse_rat_rep' where "inverse_rat_rep' (a,b) = (b,a)"
definition "inverse_rat_rep x = RatRep (inverse_rat_rep' (quotient_of_rat_rep x))"
lemma rat_of_rat_rep_inverse_rat_rep: "rat_of_rat_rep (inverse_rat_rep x) = inverse (rat_of_rat_rep x)"
  unfolding inverse_rat_rep_def apply auto
  by (metis Fract_quotient_of_rat_rep inverse_rat inverse_rat_rep'.simps prod.exhaust_sel snd_conv)

subsection "Nondeterministic rats"

context begin
declare [[typedef_overloaded]]
datatype nondet_rat = NRat (the_rat_rep: "rat_rep nondet")
end

(* nondeterministic_rat *)

lift_definition nondeterministic_rat0 :: "rat \<Rightarrow> rat_rep nondet" is
  "\<lambda>x. rat_of_rat_rep -` {x}"
  unfolding nondet_sets_rat_rep_def unit.case by auto

lift_definition nondeterministic_rat_representation :: "rat \<Rightarrow> rat_rep representation" is
  "\<lambda>r. (rat_rep_of_rat r, 
        \<lambda>(). nondeterministic_rat0 r)"
  apply simp unfolding Nitpick.case_unit_unfold apply transfer by simp

lemma [code]: "nondeterministic_rat0 x = make_nondet (nondeterministic_rat_representation x)"
  unfolding make_nondet_def nondeterministic_rat_representation.rep_eq by simp

definition "nondeterministic_rat x = NRat (nondeterministic_rat0 x)"

(* of_nondet_rat *)

definition [code del]: "of_nondet_rat0 x = rat_of_rat_rep (some_rep x)"
definition "nondet_rat_of_int i = nondeterministic_rat (of_int i)"

lift_definition rat_extractor :: "(rat_rep,rat) extractor" is 
  "(\<lambda>x. Some (rat_of_rat_rep x), \<lambda>x. of_nondet_rat0 x)"
  apply simp
  using Rep_nondet[of "_::rat_rep nondet"]
  unfolding nondet_sets_rat_rep_def unit.case of_nondet_rat0_def
  using some_rep
  by (smt mem_Collect_eq vimage_singleton_eq)
lemma [code]: "of_nondet_rat0 x = extract rat_extractor x"
  by (simp add: Nondeterministic_Code.extract_def rat_extractor.rep_eq)

fun of_nondet_rat where "of_nondet_rat (NRat x) = of_nondet_rat0 x"

(* simplify *)

lift_definition simplify_updater :: "rat_rep updater" is "simplify_rat_rep"
  unfolding nondet_sets_rat_rep_def unit.case
  apply (case_tac "simplify_rat_rep rat_rep")
   apply auto
  apply (drule rat_of_rat_rep_simplify_rat_rep)
  by simp
  
fun simplify where "simplify (NRat x) = NRat (update simplify_updater x)"

(* times *)

instantiation nondet_rat :: times begin
definition [code del]: "a * b = nondeterministic_rat (of_nondet_rat a * of_nondet_rat b)"
instance ..
end

definition "times_applier_fun xy = (case (some_rep xy) of (x,y) \<Rightarrow> 
      nondeterministic_rat0 (rat_of_rat_rep x * rat_of_rat_rep y))"

lemma times_applier_fun: "(a, b) \<in> Rep_nondet x \<Longrightarrow> times_rat_rep a b \<in> Rep_nondet (times_applier_fun x)"
proof (unfold times_applier_fun_def case_prod_unfold)
  assume ab: "(a, b) \<in> Rep_nondet x"
  obtain a' b' where Rep_nondet_x: "Rep_nondet x = Rep_nondet a' \<times> Rep_nondet b'" using Rep_nondet_pair by blast
  let ?rep = "some_rep x"
  let ?a = "fst ?rep"
  let ?b = "snd ?rep"
  have qa: "?a \<in> Rep_nondet a'" and qb: "?b \<in> Rep_nondet b'"
     apply (metis Rep_nondet_x SigmaD1 prod.collapse some_rep)
    by (metis Rep_nondet_x SigmaD2 prod.collapse some_rep)
  moreover have a: "a \<in> Rep_nondet a'" and b: "b \<in> Rep_nondet b'"
    using Rep_nondet_x ab by blast+
  ultimately have qaa: "rat_of_rat_rep ?a = rat_of_rat_rep a" and qbb: "rat_of_rat_rep ?b = rat_of_rat_rep b"
    using two_reps by blast+
  show "times_rat_rep a b
             \<in> Rep_nondet
                 (nondeterministic_rat0 (rat_of_rat_rep ?a * rat_of_rat_rep ?b))"
    using qaa qbb by (simp add: nondeterministic_rat0.rep_eq rat_of_rat_rep_times_rat_rep)
qed

lift_definition times_applier :: "(rat_rep*rat_rep,rat_rep) applier" is
  "(\<lambda>(x,y). Some (times_rat_rep x y), times_applier_fun)"
  using times_applier_fun by auto

lemma [code]: "(NRat x) * (NRat y) = NRat (apply times_applier (pair_nondet x y))"
  unfolding apply_def times_applier.rep_eq apply simp
  unfolding times_nondet_rat_def apply auto
  by (smt SigmaE fst_conv nondeterministic_rat_def of_nondet_rat0_def pair_nondet.rep_eq sndI 
          some_rep split_def times_applier_fun_def two_reps)


(* inverse / divide *)


instantiation nondet_rat :: inverse begin
definition [code del]: "inverse_nondet_rat a = nondeterministic_rat (inverse (of_nondet_rat a))"
definition "divide_nondet_rat a b = a * (inverse b :: nondet_rat)"
instance ..
end

definition "inverse_applier_fun x = nondeterministic_rat0 (inverse (of_nondet_rat0 x))"

lift_definition inverse_applier :: "(rat_rep,rat_rep) applier" is 
  "((\<lambda>x. Some(inverse_rat_rep x)), inverse_applier_fun)"
  apply auto
  by (metis (full_types) inverse_applier_fun_def nondeterministic_rat0.rep_eq of_nondet_rat0_def rat_of_rat_rep_inverse_rat_rep some_rep two_reps vimage_singleton_eq)

lemma [code]: "inverse (NRat x) = NRat (apply inverse_applier x)"
  unfolding apply_def unfolding inverse_applier.rep_eq inverse_applier_fun_def
  apply simp
  by (simp add: inverse_nondet_rat_def nondeterministic_rat_def)

section {* Memoization *}

fun fib :: "nat \<Rightarrow> nat" where 
"fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib n = fib (n-1) + fib (n-2)"

definition "good = {m. All_mapping m (\<lambda>x y. fib x = y)}"
typedef cache_fib_rep = "good" 
  apply (rule exI[of _ Mapping.empty]) unfolding good_def by auto
setup_lifting type_definition_cache_fib_rep

instantiation cache_fib_rep :: nondet_rep begin
lift_definition nondet_sets_cache_fib_rep :: "unit \<Rightarrow> cache_fib_rep set set" is "\<lambda>(). {good}"
  unfolding Nitpick.case_unit_unfold by auto
instance apply intro_classes
  unfolding nondet_sets_cache_fib_rep_def Nitpick.case_unit_unfold apply auto
  using Abs_cache_fib_rep_cases by auto
end
lemma [code]: "nondet_rep_cache_fib_rep_inst.nondet_sets_cache_fib_rep ()
= Code.abort (STR ''bla'') (%_. nondet_rep_cache_fib_rep_inst.nondet_sets_cache_fib_rep ())" by simp

definition the_cache :: "cache_fib_rep nondet" where "the_cache = undefined"
lemma Rep_nondet_the_cache[simp]: "Rep_nondet the_cache = UNIV"
  using Rep_nondet[of the_cache] 
  unfolding nondet_sets_cache_fib_rep_def Nitpick.case_unit_unfold 
  apply simp
  using type_definition.Abs_image type_definition_cache_fib_rep by blast 

lift_definition empty_cache_rep :: cache_fib_rep is "Mapping.empty :: (nat,nat)mapping"
  unfolding good_def by simp
lift_definition empty_representation :: "cache_fib_rep representation" is
  "(empty_cache_rep, \<lambda>(). the_cache)"
  apply simp unfolding Nitpick.case_unit_unfold by simp

lemma [code]: "the_cache = make_nondet empty_representation"
  unfolding make_nondet_def empty_representation.rep_eq by simp

lift_definition lookup_extractor :: "nat \<Rightarrow> (cache_fib_rep,nat) extractor" is 
  "\<lambda>n. (\<lambda>c. Mapping.lookup (Rep_cache_fib_rep c) n,
        \<lambda>c::cache_fib_rep nondet. fib n)"
  apply auto
  by (smt All_mapping_def Rep_cache_fib_rep good_def mem_Collect_eq option.case_eq_if) 

fun fib' where 
"fib' 0 = 0"
| "fib' (Suc 0) = 1"
| "fib' n = fib (n-1) + fib (n-2)"

lemma fib_fib': "fib n = fib' n" apply (cases n) apply simp apply (case_tac nat) by auto

typedef fibresult = "{(n,m)| n m. fib n = m}" by auto
setup_lifting type_definition_fibresult
lemma [code abstype]: "Abs_fibresult (Rep_fibresult x) = x"
  by (simp add: Rep_fibresult_inverse)

lemma m_update: assumes "m \<in> good" shows "Mapping.update n (fib n) m \<in> good"
      using assms unfolding good_def apply auto
      apply (rule All_mapping_update) 
       apply auto
      by (metis (no_types, lifting) All_mapping_mono)

lift_definition cache_fib_rep_update :: "fibresult \<Rightarrow> cache_fib_rep \<Rightarrow> cache_fib_rep" is
  "\<lambda>(n,m) c. (Mapping.update n m c)"
  using m_update by auto 

lift_definition update_at_updater :: "fibresult \<Rightarrow> cache_fib_rep updater" is "\<lambda>r c. Some (cache_fib_rep_update r c)"
  unfolding nondet_sets_cache_fib_rep_def Nitpick.case_unit_unfold apply auto
  by (metis UNIV_I type_definition.Abs_image type_definition_cache_fib_rep)

definition "update_at n c = update (update_at_updater n) c"

lift_definition fib'' :: "nat \<Rightarrow> fibresult" is 
  "\<lambda>n. (n, if n=0 then 0 else if n=1 then 1 else fib (n-1) + fib (n-2))"
  apply auto
  by (metis One_nat_def fib.elims neq0_conv)
lemma snd_fib'': "snd (Rep_fibresult (fib'' n)) = fib n"
  apply transfer apply auto
  by (metis One_nat_def fib.elims neq0_conv)

lift_definition lookup_compute :: "nat \<Rightarrow> cache_fib_rep \<Rightarrow> nat" is
  "\<lambda>n c. case Mapping.lookup c n of
            Some m \<Rightarrow> m
          | None \<Rightarrow> let res = fib'' n in let x = update_at res the_cache in snd (Rep_fibresult res)" .
lemma lookup_compute_fib: "lookup_compute n c = fib n"
  apply transfer unfolding update_at_def update_def Let_def snd_fib''  good_def
  apply (case_tac "Mapping.lookup c n") apply auto
  by (metis (mono_tags, lifting) All_mapping_def option.simps(5))

lift_definition lookup_compute_extractor :: "nat \<Rightarrow> (cache_fib_rep,nat) extractor" is 
  "\<lambda>n. (\<lambda>c. Some (lookup_compute n c),
        \<lambda>c::cache_fib_rep nondet. fib n)"
  unfolding lookup_compute_fib by auto




lemma [code]: "fib n = 
    (extract (lookup_compute_extractor n) the_cache)"
  unfolding extract_def apply transfer by simp

definition "testf = fib 1000"
export_code testf in SML module_name Test file "testf.ML" 
(* ML_file "testf.ML"  *)
value testf



section "Test"

declare [[coercion nondet_rat_of_int]]

definition t1 ::nondet_rat where "t1=inverse 11"
definition "t2 = 33 * t1"
definition test where "test = of_nondet_rat (fst (t2,simplify t2))"
definition "test2 = (3*4 :: int)"
export_code test in SML module_name "Test" file "test.ML" 
ML_file "test.ML"
ML {* Test.test *}
