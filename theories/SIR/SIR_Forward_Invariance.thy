(*
  SIR_Forward_Invariance.thy — Nonnegativity from initial conditions.

  The key insight is that the SIR ODE is linear in each compartment:
    S' = (-β·I(t)) · S     →  linear in S with coefficient -β·I(t)
    I' = (βS(t)-γ) · I     →  linear in I with coefficient βS(t)-γ
    R' = γ·I(t)            →  nonneg derivative (once I≥0 is known)

  By the linear ODE solution formula from the framework:
    S(t) = S(a)·exp(-β ∫ₐᵗ I)   ≥ 0  (since S(a)≥0, exp>0)
    I(t) = I(a)·exp(∫ₐᵗ (βS-γ)) ≥ 0  (since I(a)≥0, exp>0)
    R(t) = R(a) + γ∫ₐᵗ I        ≥ 0  (since R(a)≥0, I≥0, γ>0)

  These derivations do NOT require Picard-Lindelöf or Grönwall.
  They only require:
    - Fundamental Theorem of Calculus
    - exp > 0
    - Continuous functions are integrable

  License: BSD-3-Clause
*)

theory SIR_Forward_Invariance
  imports SIR_Defs
begin

context SIR_solution
begin

section \<open>Forward Invariance: Nonnegativity from Initial Conditions\<close>

text \<open>
  We derive nonnegativity of all compartments from the nonneg initial
  conditions and the ODE structure, using the framework's
  @{thm [source] linear_ode_solution} theorem.
\<close>

subsection \<open>I is Nonneg (Linear ODE)\<close>

text \<open>
  The I-equation $I' = (\beta S - \gamma) I$ is linear in $I$.
  By the linear ODE framework lemma, $I(t) = I(a) \cdot \exp(\int_a^t (\beta S - \gamma))$.
  Since $I(a) \ge 0$ and $\exp > 0$, we get $I(t) \ge 0$.
\<close>

lemma I_ode_linear: "\<And>t. t \<in> {a..b} \<Longrightarrow>
  (I has_real_derivative ((\<beta> * S t - \<gamma>) * I t)) (at t)"
proof -
  fix t assume "t \<in> {a..b}"
  from ode_I[OF this] show "(I has_real_derivative ((\<beta> * S t - \<gamma>) * I t)) (at t)"
    by (simp add: algebra_simps)
qed

lemma cont_I_coeff: "continuous_on {a..b} (\<lambda>t. \<beta> * S t - \<gamma>)"
  using continuous_S by (intro continuous_intros)

theorem I_nonneg:
  assumes "t \<in> {a..b}"
  shows "0 \<le> I t"
  by (rule linear_ode_nonneg[OF interval cont_I_coeff I_ode_linear assms init_I])

theorem I_solution:
  assumes "t \<in> {a..b}"
  shows "I t = I a * exp (integral {a..t} (\<lambda>s. \<beta> * S s - \<gamma>))"
  by (rule linear_ode_solution[OF interval cont_I_coeff I_ode_linear assms])

subsection \<open>S is Nonneg (Linear ODE)\<close>

text \<open>
  The S-equation $S' = -\beta I \cdot S$ is linear in $S$.
  By the framework lemma, $S(t) = S(a) \cdot \exp(-\beta \int_a^t I)$.
  Since $S(a) \ge 0$ and $\exp > 0$, we get $S(t) \ge 0$.
\<close>

lemma S_ode_linear: "\<And>t. t \<in> {a..b} \<Longrightarrow>
  (S has_real_derivative ((- \<beta> * I t) * S t)) (at t)"
proof -
  fix t assume "t \<in> {a..b}"
  from ode_S[OF this] show "(S has_real_derivative ((- \<beta> * I t) * S t)) (at t)"
    by (simp add: algebra_simps)
qed

lemma cont_S_coeff: "continuous_on {a..b} (\<lambda>t. - \<beta> * I t)"
  using continuous_I by (intro continuous_intros)

theorem S_nonneg:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t"
  by (rule linear_ode_nonneg[OF interval cont_S_coeff S_ode_linear assms init_S])

theorem S_solution:
  assumes "t \<in> {a..b}"
  shows "S t = S a * exp (integral {a..t} (\<lambda>s. - \<beta> * I s))"
  by (rule linear_ode_solution[OF interval cont_S_coeff S_ode_linear assms])

subsection \<open>R is Nonneg (Nonneg Derivative)\<close>

text \<open>
  The R-equation $R' = \gamma I \ge 0$ (using $I \ge 0$ just proved
  and $\gamma > 0$). Combined with $R(a) \ge 0$, we get $R(t) \ge 0$.
\<close>

theorem R_nonneg:
  assumes "t \<in> {a..b}"
  shows "0 \<le> R t"
proof (rule nonneg_deriv_nonneg[OF interval ode_R _ assms init_R])
  fix u assume "u \<in> {a..b}"
  show "0 \<le> \<gamma> * I u"
    using pos_gamma I_nonneg[OF \<open>u \<in> {a..b}\<close>]
    by (intro mult_nonneg_nonneg) auto
qed

subsection \<open>Summary\<close>

text \<open>
  All compartments are nonneg on the entire interval, derived purely
  from the ODE structure and nonneg initial conditions.
\<close>

theorem forward_invariance:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t" and "0 \<le> I t" and "0 \<le> R t"
  using S_nonneg[OF assms] I_nonneg[OF assms] R_nonneg[OF assms] .

end

end
