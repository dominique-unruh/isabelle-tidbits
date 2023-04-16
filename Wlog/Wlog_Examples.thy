theory Wlog_Examples
  imports Wlog Complex_Main
begin

lemma
  fixes a b :: nat
  assumes bla: "True"
  assumes neq: "a \<noteq> b"
  shows "a+b \<ge> 1" (is ?th) and "a+b \<ge> 0"
proof -
  let ?thesis = "a+b \<ge> 1"

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
        using False wlog.neq2
        by simp
    next
      case neq3 
      show ?case using wlog.neq2 by auto
    next 
      assume "1 \<le> b + a" 
      then show "1 \<le> a + b" by linarith
    qed
  qed

  note assms = neq neq3 

  have "b<a \<or> a<b" by (simp add: geq)

  wlog tmp: "a=a" generalizing a b keeping geq 
    print_theorems
    using hypothesis neq geq by metis

  from geq have "a \<ge> 1" by auto

  then show "1 \<le> a + b" by auto
next
  show "a+b \<ge> 0" by auto
qed

text \<open>The theorem @{thm [source] Complex.card_nth_roots} has the additional assumption \<^term>\<open>n > 0\<close>.
  We use exactly the same proof except for stating that w.l.o.g., \<^term>\<open>n > 0\<close>.\<close>
lemma card_nth_roots_strengthened:
  assumes "c \<noteq> 0"
  shows   "card {z::complex. z ^ n = c} = n"
proof -
  wlog n_pos: "n > 0"
    using negation by (simp add: infinite_UNIV_char_0)
  have "card {z. z ^ n = c} = card {z::complex. z ^ n = 1}"
    by (rule sym, rule bij_betw_same_card, rule bij_betw_nth_root_unity) fact+
  also have "\<dots> = n" by (rule card_roots_unity_eq) fact+
  finally show ?thesis .
qed

text \<open>This example follows very roughly Harrison, \<^url>\<open>https://www.cl.cam.ac.uk/~jrh13/papers/wlog.pdf\<close>\<close>
lemma schur_ineq:
  fixes a b c :: \<open>'a :: linordered_idom\<close> and k :: nat
  assumes a0: \<open>a \<ge> 0\<close> and b0: \<open>b \<ge> 0\<close> and c0: \<open>c \<ge> 0\<close>
  shows \<open>a^k * (a - b) * (a - c) + b^k * (b - a) * (b - c) + c^k * (c - a) * (c - b) \<ge> 0\<close>
    (is \<open>?lhs \<ge> 0\<close>)
proof -
  wlog \<open>a \<le> b \<and> b \<le> c\<close> generalizing a b c keeping a0 b0 c0
    (* TODO: we'd like to directly specify \<open>a \<le> b\<close> and \<open>b \<le> c\<close> *)
    (* TODO: we'd like to add [simp] or similar to the wlog assumption *)
    (* TODO: Informative message should not refer to "". *)
    apply (rule rev_mp[OF c0]; rule rev_mp[OF b0]; rule rev_mp[OF a0])
    apply (rule linorder_wlog_3[of _ a b c])
     apply (simp add: algebra_simps)
    by (simp add: hypothesis)

  then have [simp]: \<open>a \<le> b\<close> \<open>b \<le> c\<close>
    by auto
  then have [simp]: \<open>a \<le> c\<close>
    by linarith

  have \<open>?lhs = (c - b) * (c^k * (c - a) - b^k * (b - a)) + a^k * (c - a) * (b - a)\<close>
    by (simp add: algebra_simps)
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg mult_mono power_mono zero_le_power simp: a0 b0 c0)
  finally show \<open>?lhs \<ge> 0\<close>
    by -
qed

