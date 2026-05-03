(*
  SIR_Threshold.thy — Epidemic growth condition and threshold ratios.

  The infected compartment I has positive derivative if and only if
  I > 0 and beta * S > gamma. This is the pointwise growth criterion.

  We also define the effective threshold ratio R_e(t) = β·S(t)/γ
  and its initial value R_zero = β·S(a)/γ.

  License: BSD-3-Clause
*)

theory SIR_Threshold
  imports SIR_Monotonicity
begin

context SIR_solution
begin

section \<open>Epidemic Growth Condition\<close>

text \<open>
  The derivative of $I$ at time $t$ is:
  \[
    \frac{dI}{dt} = \beta S I - \gamma I = I(\beta S - \gamma)
  \]
  This is positive (epidemic grows) iff $I > 0$ and $\beta S > \gamma$.
\<close>

theorem epidemic_growth_iff:
  assumes t_in: "t \<in> {a..b}"
  shows "\<beta> * S t * I t - \<gamma> * I t > 0 \<longleftrightarrow> (I t > 0 \<and> \<beta> * S t > \<gamma>)"
proof
  assume pos: "\<beta> * S t * I t - \<gamma> * I t > 0"
  have factored: "\<beta> * S t * I t - \<gamma> * I t = I t * (\<beta> * S t - \<gamma>)"
    by (simp add: algebra_simps)
  have "I t > 0"
  proof (rule ccontr)
    assume "\<not> I t > 0"
    then have "I t = 0" using I_nonneg[OF t_in] by linarith
    then have "\<beta> * S t * I t - \<gamma> * I t = 0" by simp
    with pos show False by linarith
  qed
  moreover have "\<beta> * S t > \<gamma>"
  proof (rule ccontr)
    assume "\<not> \<beta> * S t > \<gamma>"
    then have "\<beta> * S t - \<gamma> \<le> 0" by simp
    then have "I t * (\<beta> * S t - \<gamma>) \<le> 0"
      using I_nonneg[OF t_in] by (simp add: mult_nonneg_nonpos)
    with pos factored show False by linarith
  qed
  ultimately show "I t > 0 \<and> \<beta> * S t > \<gamma>" by simp
next
  assume asm: "I t > 0 \<and> \<beta> * S t > \<gamma>"
  then have "I t > 0" "\<beta> * S t - \<gamma> > 0" by auto
  have "\<beta> * S t * I t - \<gamma> * I t = I t * (\<beta> * S t - \<gamma>)"
    by (simp add: algebra_simps)
  also have "\<dots> > 0"
    using \<open>I t > 0\<close> \<open>\<beta> * S t - \<gamma> > 0\<close> by (intro mult_pos_pos) auto
  finally show "\<beta> * S t * I t - \<gamma> * I t > 0" .
qed

section \<open>Effective Threshold Ratio\<close>

text \<open>
  The effective threshold ratio at time $t$ is $R_e(t) = \beta S(t) / \gamma$.
  The quantity $R_zero = \beta S(a) / \gamma$ is its initial value.
  Epidemic growth at time $t$ requires $R_e(t) > 1$ (i.e., $\beta S(t) > \gamma$).
\<close>

definition R_eff :: "real \<Rightarrow> real" where
  "R_eff t \<equiv> \<beta> * S t / \<gamma>"

definition R_zero :: real where
  "R_zero \<equiv> \<beta> * S a / \<gamma>"

lemma R_eff_initial: "R_eff a = R_zero"
  unfolding R_eff_def R_zero_def ..

lemma R_zero_pos: "0 \<le> R_zero"
  unfolding R_zero_def using pos_beta pos_gamma init_S
  by (intro divide_nonneg_pos mult_nonneg_nonneg) auto

theorem epidemic_growth_R_eff:
  assumes t_in: "t \<in> {a..b}" and I_pos: "I t > 0"
  shows "\<beta> * S t * I t - \<gamma> * I t > 0 \<longleftrightarrow> R_eff t > 1"
proof -
  have "\<beta> * S t * I t - \<gamma> * I t > 0 \<longleftrightarrow> (I t > 0 \<and> \<beta> * S t > \<gamma>)"
    by (rule epidemic_growth_iff[OF t_in])
  also have "\<dots> \<longleftrightarrow> \<beta> * S t > \<gamma>"
    using I_pos by simp
  also have "\<dots> \<longleftrightarrow> \<beta> * S t / \<gamma> > 1"
    using pos_gamma by (simp add: field_simps)
  also have "\<dots> \<longleftrightarrow> R_eff t > 1"
    unfolding R_eff_def ..
  finally show ?thesis .
qed

theorem initial_epidemic_growth:
  assumes "I a > 0" and "R_zero > 1"
  shows "\<beta> * S a * I a - \<gamma> * I a > 0"
proof -
  have "\<beta> * S a > \<gamma>"
    using assms(2) pos_gamma unfolding R_zero_def
    by (simp add: field_simps)
  with assms(1) show ?thesis
    using epidemic_growth_iff[OF a_in_interval] by simp
qed

theorem initial_no_epidemic:
  assumes "I a > 0" and "R_zero \<le> 1"
  shows "\<beta> * S a * I a - \<gamma> * I a \<le> 0"
proof -
  have "\<beta> * S a \<le> \<gamma>"
    using assms(2) pos_gamma unfolding R_zero_def
    by (simp add: field_simps)
  then have "\<beta> * S a * I a - \<gamma> * I a = I a * (\<beta> * S a - \<gamma>)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> 0"
    using assms(1) \<open>\<beta> * S a \<le> \<gamma>\<close>
    by (simp add: mult_nonneg_nonpos)
  finally show ?thesis .
qed

theorem initial_epidemic_decline:
  assumes "I a > 0" and "R_zero < 1"
  shows "\<beta> * S a * I a - \<gamma> * I a < 0"
proof -
  have "\<beta> * S a < \<gamma>"
    using assms(2) pos_gamma unfolding R_zero_def
    by (simp add: field_simps)
  then have "\<beta> * S a * I a - \<gamma> * I a = I a * (\<beta> * S a - \<gamma>)"
    by (simp add: algebra_simps)
  also have "\<dots> < 0"
    using assms(1) \<open>\<beta> * S a < \<gamma>\<close>
    by (simp add: mult_pos_neg)
  finally show ?thesis .
qed

section \<open>Global Monotonicity of I under $R_zero \le 1$\<close>

text \<open>
  If the initial threshold ratio $R_zero$ is at most 1, then
  $\beta S(t) \le \gamma$ for all $t \in [a,b]$ (since $S$ is
  nonincreasing), so $I'(t) = I(t)(\beta S(t) - \gamma) \le 0$ and $I$
  is nonincreasing on the entire interval.
\<close>

lemma R_eff_nonincreasing:
  assumes "t \<in> {a..b}"
  shows "R_eff t \<le> R_zero"
proof -
  have "a \<le> t" using assms by auto
  then have "S t \<le> S a" by (rule S_nonincreasing[OF a_in_interval assms])
  then have "\<beta> * S t \<le> \<beta> * S a" using pos_beta by simp
  then show ?thesis
    unfolding R_eff_def R_zero_def using pos_gamma
    by (simp add: divide_right_mono)
qed

lemma beta_S_le_gamma_if_R_zero_le_one:
  assumes "R_zero \<le> 1" and "t \<in> {a..b}"
  shows "\<beta> * S t \<le> \<gamma>"
proof -
  have "R_eff t \<le> R_zero" by (rule R_eff_nonincreasing[OF assms(2)])
  also have "\<dots> \<le> 1" by (rule assms(1))
  finally have "R_eff t \<le> 1" .
  then show "\<beta> * S t \<le> \<gamma>"
    unfolding R_eff_def using pos_gamma by (simp add: field_simps)
qed

theorem I_nonincreasing_if_R_zero_le_one:
  assumes R0: "R_zero \<le> 1"
    and s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}" and st: "s \<le> t"
  shows "I t \<le> I s"
proof -
  define f' where "f' \<equiv> \<lambda>u. \<beta> * S u * I u - \<gamma> * I u"
  have df: "(I has_real_derivative f' u) (at u)" if "u \<in> {s..t}" for u
  proof -
    have "u \<in> {a..b}" using that s_in t_in by auto
    then show ?thesis unfolding f'_def by (rule ode_I)
  qed
  have sign: "f' u \<le> 0" if "u \<in> {s..t}" for u
  proof -
    have u_ab: "u \<in> {a..b}" using that s_in t_in by auto
    have "f' u = I u * (\<beta> * S u - \<gamma>)" unfolding f'_def by (simp add: algebra_simps)
    also have "\<dots> \<le> 0"
      using I_nonneg[OF u_ab] beta_S_le_gamma_if_R_zero_le_one[OF R0 u_ab]
      by (simp add: mult_nonneg_nonpos)
    finally show ?thesis .
  qed
  show ?thesis by (rule nonincreasing_from_nonpos_derivative[OF st df sign])
qed

text \<open>$R_e$ is nonincreasing (since $S$ is nonincreasing, proved elsewhere).\<close>

end

end
