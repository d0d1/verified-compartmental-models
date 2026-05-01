(*
  SIR_Threshold.thy — Epidemic growth condition.

  The infected compartment I has positive derivative if and only if
  I > 0 and beta * S > gamma. This is the pointwise growth criterion
  for the SIR ODE right-hand side.

  License: BSD-3-Clause
*)

theory SIR_Threshold
  imports SIR_Defs
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
  The condition $\beta S(t) > \gamma$ is the pointwise growth criterion;
  equivalently, $\beta S(t) / \gamma > 1$ (the effective reproduction
  condition at time $t$).
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
    then have "I t = 0" using nonneg_I[OF t_in] by linarith
    then have "\<beta> * S t * I t - \<gamma> * I t = 0" by simp
    with pos show False by linarith
  qed
  moreover have "\<beta> * S t > \<gamma>"
  proof (rule ccontr)
    assume "\<not> \<beta> * S t > \<gamma>"
    then have "\<beta> * S t - \<gamma> \<le> 0" by simp
    then have "I t * (\<beta> * S t - \<gamma>) \<le> 0"
      using nonneg_I[OF t_in] by (simp add: mult_nonneg_nonpos)
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

text \<open>
  The threshold condition at the initial time determines whether an epidemic
  occurs (I initially increasing).
\<close>

corollary initial_epidemic_growth:
  assumes "I a > 0" and "\<beta> * S a > \<gamma>"
  shows "\<beta> * S a * I a - \<gamma> * I a > 0"
  using epidemic_growth_iff[OF a_in_interval] assms by simp

corollary initial_no_epidemic:
  assumes "I a > 0" and "\<beta> * S a \<le> \<gamma>"
  shows "\<beta> * S a * I a - \<gamma> * I a \<le> 0"
proof -
  have "\<beta> * S a * I a - \<gamma> * I a = I a * (\<beta> * S a - \<gamma>)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> 0"
    using assms nonneg_I[OF a_in_interval]
    by (simp add: mult_nonneg_nonpos)
  finally show ?thesis .
qed

end

end
