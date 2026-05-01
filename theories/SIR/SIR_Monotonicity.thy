(*
  SIR_Monotonicity.thy — Monotonicity of S and R compartments.

  Under the SIR dynamics with nonnegative compartments:
    - S is nonincreasing (susceptibles only decrease)
    - R is nondecreasing (recovered only increase)

  License: BSD-3-Clause
*)

theory SIR_Monotonicity
  imports SIR_Defs
begin

context SIR_solution
begin

section \<open>Monotonicity of Compartments\<close>

subsection \<open>S is Nonincreasing\<close>

text \<open>
  Since $dS/dt = -\beta S I \le 0$ (all factors nonneg), S is nonincreasing.
\<close>

lemma S_deriv_nonpos:
  assumes "t \<in> {a..b}"
  shows "- \<beta> * S t * I t \<le> 0"
proof -
  have "0 \<le> \<beta> * S t * I t"
    using pos_beta nonneg_S[OF assms] nonneg_I[OF assms]
    by (intro mult_nonneg_nonneg) auto
  then show ?thesis by simp
qed

theorem S_nonincreasing:
  assumes s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}" and st: "s \<le> t"
  shows "S t \<le> S s"
proof (rule DERIV_nonpos_imp_nonincreasing[OF st])
  fix x assume "s \<le> x" "x \<le> t"
  then have x_in: "x \<in> {a..b}" using s_in t_in by auto
  show "\<exists>y. DERIV S x :> y \<and> y \<le> 0"
    using ode_S[OF x_in] S_deriv_nonpos[OF x_in] by blast
qed

corollary S_bounded_above:
  assumes "t \<in> {a..b}"
  shows "S t \<le> S a"
  using S_nonincreasing[OF a_in_interval assms] interval assms by auto

subsection \<open>R is Nondecreasing\<close>

text \<open>
  Since $dR/dt = \gamma I \ge 0$ (both factors nonneg), R is nondecreasing.
\<close>

lemma R_deriv_nonneg:
  assumes "t \<in> {a..b}"
  shows "0 \<le> \<gamma> * I t"
  using pos_gamma nonneg_I[OF assms]
  by (intro mult_nonneg_nonneg) auto

theorem R_nondecreasing:
  assumes s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}" and st: "s \<le> t"
  shows "R s \<le> R t"
proof (rule DERIV_nonneg_imp_nondecreasing[OF st])
  fix x assume "s \<le> x" "x \<le> t"
  then have x_in: "x \<in> {a..b}" using s_in t_in by auto
  show "\<exists>y. DERIV R x :> y \<and> y \<ge> 0"
    using ode_R[OF x_in] R_deriv_nonneg[OF x_in] by blast
qed

corollary R_bounded_below:
  assumes "t \<in> {a..b}"
  shows "R a \<le> R t"
  using R_nondecreasing[OF a_in_interval assms] interval assms by auto

end

end
