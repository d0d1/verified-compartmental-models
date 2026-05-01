(*
  SIR_Phase_Plane.thy — Kermack-McKendrick phase plane invariant.

  V(t) = I(t) + S(t) - (γ/β)·ln(S(t)) is constant along SIR solutions.

  License: BSD-3-Clause
*)

theory SIR_Phase_Plane
  imports SIR_Forward_Invariance
begin

context SIR_solution
begin

section \<open>Kermack-McKendrick Invariant\<close>

definition KM_invariant :: "real \<Rightarrow> real" where
  "KM_invariant t \<equiv> I t + S t - (\<gamma> / \<beta>) * ln (S t)"

lemma S_pos_preserved:
  assumes S_a_pos: "0 < S a" and t_in: "t \<in> {a..b}"
  shows "0 < S t"
  by (rule linear_ode_pos[OF interval cont_S_coeff S_ode_linear t_in S_a_pos])

theorem KM_invariant_constant:
  assumes S_a_pos: "0 < S a"
    and s_in: "s \<in> {a..b}" and t_in: "t \<in> {a..b}"
  shows "KM_invariant s = KM_invariant t"
proof -
  define V where "V \<equiv> KM_invariant"

  have V_deriv: "DERIV V u :> 0" if u_ab: "a < u" "u < b" for u
  proof -
    have u_in: "u \<in> {a..b}" using that by auto
    have S_pos: "0 < S u"
      by (rule S_pos_preserved[OF S_a_pos u_in])
    have dI: "(I has_real_derivative (\<beta> * S u * I u - \<gamma> * I u)) (at u)"
      by (rule ode_I[OF u_in])
    have dS: "(S has_real_derivative (- \<beta> * S u * I u)) (at u)"
      by (rule ode_S[OF u_in])
    \<comment> \<open>Chain rule for ln(S): derivative = (1/S(u)) * S'(u)\<close>
    have d_ln_S: "((\<lambda>t. ln (S t)) has_real_derivative (1 / S u * (- \<beta> * S u * I u))) (at u)"
      using DERIV_ln_divide[OF S_pos] dS by (rule DERIV_chain2)
    \<comment> \<open>Scalar multiple: (γ/β) * ln(S)\<close>
    have d_scaled_ln: "((\<lambda>t. (\<gamma> / \<beta>) * ln (S t)) has_real_derivative
           (\<gamma> / \<beta>) * (1 / S u * (- \<beta> * S u * I u))) (at u)"
      by (rule DERIV_cmult[OF d_ln_S])
    \<comment> \<open>Sum I + S\<close>
    have d_sum: "((\<lambda>t. I t + S t) has_real_derivative
           (\<beta> * S u * I u - \<gamma> * I u) + (- \<beta> * S u * I u)) (at u)"
      by (rule DERIV_add[OF dI dS])
    \<comment> \<open>Difference (I + S) - (γ/β)*ln(S)\<close>
    have d_V: "((\<lambda>t. I t + S t - (\<gamma> / \<beta>) * ln (S t)) has_real_derivative
           ((\<beta> * S u * I u - \<gamma> * I u) + (- \<beta> * S u * I u))
           - (\<gamma> / \<beta>) * (1 / S u * (- \<beta> * S u * I u))) (at u)"
      by (rule DERIV_diff[OF d_sum d_scaled_ln])
    moreover have "((\<beta> * S u * I u - \<gamma> * I u) + (- \<beta> * S u * I u))
                   - (\<gamma> / \<beta>) * (1 / S u * (- \<beta> * S u * I u)) = 0"
      using S_pos pos_beta by (simp add: field_simps)
    ultimately show "DERIV V u :> 0" unfolding V_def KM_invariant_def by simp
  qed

  have S_pos_all: "\<And>t. t \<in> {a..b} \<Longrightarrow> S t \<noteq> 0"
    using S_pos_preserved[OF S_a_pos] by (auto simp: less_imp_neq[symmetric])
  have cont_ln_S: "continuous_on {a..b} (\<lambda>t. ln (S t))"
    by (rule continuous_on_ln[OF continuous_S]) (rule ballI, rule S_pos_all)
  have cont_V: "continuous_on {a..b} V"
    unfolding V_def KM_invariant_def
    using continuous_I continuous_S cont_ln_S
    by (intro continuous_on_add continuous_on_diff continuous_on_mult
            continuous_on_const) auto

  have "V s = V a"
    by (rule DERIV_isconst2[OF interval cont_V])
       (use V_deriv s_in in auto)
  moreover have "V t = V a"
    by (rule DERIV_isconst2[OF interval cont_V])
       (use V_deriv t_in in auto)
  ultimately show "KM_invariant s = KM_invariant t"
    unfolding V_def by simp
qed

corollary KM_invariant_value:
  assumes "0 < S a" and "t \<in> {a..b}"
  shows "I t + S t - (\<gamma> / \<beta>) * ln (S t) = I a + S a - (\<gamma> / \<beta>) * ln (S a)"
  using KM_invariant_constant[OF assms(1) assms(2) a_in_interval]
  unfolding KM_invariant_def by simp

end

end
