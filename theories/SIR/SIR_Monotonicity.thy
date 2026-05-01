(*
  SIR_Monotonicity.thy — Monotonicity of S and R compartments.

  Under the SIR dynamics with derived nonnegativity:
    - S is nonincreasing (susceptibles only decrease)
    - R is nondecreasing (recovered only increase)

  License: BSD-3-Clause
*)

theory SIR_Monotonicity
  imports SIR_Conservation
begin

context SIR_solution
begin

section \<open>Monotonicity of Compartments\<close>

subsection \<open>S is Nonincreasing\<close>

text \<open>
  Since $dS/dt = -\beta S I \le 0$ (all factors nonneg, derived from
  forward invariance), S is nonincreasing.
\<close>

lemma S_deriv_nonpos:
  assumes "t \<in> {a..b}"
  shows "- \<beta> * S t * I t \<le> 0"
proof -
  have "0 \<le> \<beta> * S t * I t"
    using pos_beta S_nonneg[OF assms] I_nonneg[OF assms]
    by (intro mult_nonneg_nonneg) auto
  then show ?thesis by simp
qed

theorem S_nonincreasing:
  assumes s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}" and st: "s \<le> t"
  shows "S t \<le> S s"
proof (rule nonincreasing_from_nonpos_derivative[OF st])
  fix u assume "u \<in> {s..t}"
  then have u_in: "u \<in> {a..b}" using s_in t_in by auto
  show "(S has_real_derivative (- \<beta> * S u * I u)) (at u)" by (rule ode_S[OF u_in])
next
  fix u assume "u \<in> {s..t}"
  then have u_in: "u \<in> {a..b}" using s_in t_in by auto
  show "- \<beta> * S u * I u \<le> 0" by (rule S_deriv_nonpos[OF u_in])
qed

corollary S_bounded_above:
  assumes "t \<in> {a..b}"
  shows "S t \<le> S a"
  using S_nonincreasing[OF a_in_interval assms] interval assms by auto

subsection \<open>R is Nondecreasing\<close>

text \<open>
  Since $dR/dt = \gamma I \ge 0$ (using derived $I \ge 0$), R is nondecreasing.
\<close>

lemma R_deriv_nonneg:
  assumes "t \<in> {a..b}"
  shows "0 \<le> \<gamma> * I t"
  using pos_gamma I_nonneg[OF assms]
  by (intro mult_nonneg_nonneg) auto

theorem R_nondecreasing:
  assumes s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}" and st: "s \<le> t"
  shows "R s \<le> R t"
proof (rule nondecreasing_from_nonneg_derivative[OF st])
  fix u assume "u \<in> {s..t}"
  then have u_in: "u \<in> {a..b}" using s_in t_in by auto
  show "(R has_real_derivative (\<gamma> * I u)) (at u)" by (rule ode_R[OF u_in])
next
  fix u assume "u \<in> {s..t}"
  then have u_in: "u \<in> {a..b}" using s_in t_in by auto
  show "0 \<le> \<gamma> * I u" by (rule R_deriv_nonneg[OF u_in])
qed

corollary R_bounded_below:
  assumes "t \<in> {a..b}"
  shows "R a \<le> R t"
  using R_nondecreasing[OF a_in_interval assms] interval assms by auto

end

end
