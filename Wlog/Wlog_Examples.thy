theory Wlog_Examples
  imports Wlog Complex_Main
begin

lemma "a*a \<ge> (0::int)"
proof -
  wlog geq0: "a\<ge>0" generalizing a
  proof -
    from negation have "- a \<ge> 0" by simp
    then have "- a * - a \<ge> 0" by (rule hypothesis)
    then show "a*a \<ge> 0" by simp
  qed

  from geq0 show ?thesis by simp
qed


lemma
  fixes a b :: nat
  assumes bla: "True"
  assumes neq: "a \<noteq> b"
  shows "a+b \<ge> 1" (is ?th) and "a+b \<ge> 0"
proof -
  goal "a+b \<ge> 1"

  (* goal "?thesis" (is "a+b \<ge> 1") *)
  have neq2: "a>b \<or> b>a" using neq bla by auto 
  have comm: "1 \<le> a + b \<Longrightarrow> 1 \<le> b + a" for a b :: nat by auto

  let ?a = a

  have test: "\<And>a. b \<noteq> a \<Longrightarrow> a \<noteq> b \<Longrightarrow> 1 \<le> a + b" sorry

  wlog neq3: "b\<noteq>a" generalizing a keeping neq
  proof (cases rule:hypothesis[where a=a]) print_cases
    case neq show ?case using assms(2) by blast 
    case neq3 show ?case using assms(2) by blast 
  qed

  have aux: "P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> Q" for P Q by metis

  wlog geq: "a > b" generalizing a b keeping neq3
  proof (cases "a > b")
    case True 
    show ?thesis
      using True hypothesis by blast
  next
    case False
    show ?thesis
    proof (rule aux, cases rule:hypothesis[of a b])
      case geq
      show ?case
        using False lost.neq2
        by simp
    next
      case neq3 
      show ?case using lost.neq2 by auto
    next 
      assume "1 \<le> b + a" 
      then show "1 \<le> a + b" by linarith
    qed
  qed

  note assms = neq neq3 

  have "b<a \<or> a<b" by (simp add: geq)

 (* apply (tactic \<open>resolve_tac @{context} [neq2'] 1\<close>) using assms by auto *)

  wlog tmp: "a=a" generalizing a b keeping geq 
    print_theorems
    using hypothesis neq geq by metis

  from geq have "a \<ge> 1" by auto

  then show "1 \<le> a + b" by auto
next
  goal "a+b \<ge> 0"
  show ?thesis by auto
qed
