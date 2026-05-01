(*
  SIR_Invariant.thy — Boundedness of the SIR system.

  Given conservation and forward invariance (derived from initial conditions),
  all compartments are bounded by the total population N.

  License: BSD-3-Clause
*)

theory SIR_Invariant
  imports SIR_Conservation SIR_Monotonicity
begin

context SIR_solution
begin

section \<open>Boundedness of Compartments\<close>

text \<open>
  Given conservation and nonnegativity (both derived from ODE structure
  and nonneg initial conditions), each compartment is bounded by the
  total population:
  \[
    0 \le X(t) \le N \quad \text{for } X \in \{S, I, R\}
  \]
  where $N = S(a) + I(a) + R(a)$.
\<close>

theorem S_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t" and "S t \<le> total_population"
proof -
  show "0 \<le> S t" by (rule S_nonneg[OF assms])
next
  have "S t \<le> S t + I t + R t"
    using I_nonneg[OF assms] R_nonneg[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "S t \<le> total_population" .
qed

theorem I_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> I t" and "I t \<le> total_population"
proof -
  show "0 \<le> I t" by (rule I_nonneg[OF assms])
next
  have "I t \<le> S t + I t + R t"
    using S_nonneg[OF assms] R_nonneg[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "I t \<le> total_population" .
qed

theorem R_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> R t" and "R t \<le> total_population"
proof -
  show "0 \<le> R t" by (rule R_nonneg[OF assms])
next
  have "R t \<le> S t + I t + R t"
    using S_nonneg[OF assms] I_nonneg[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "R t \<le> total_population" .
qed

lemma total_population_nonneg: "0 \<le> total_population"
  unfolding total_population_def
  using init_S init_I init_R by linarith

corollary compartment_bounds:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t" and "S t \<le> total_population"
    and "0 \<le> I t" and "I t \<le> total_population"
    and "0 \<le> R t" and "R t \<le> total_population"
    and "S t + I t + R t = total_population"
  using S_bounded[OF assms] I_bounded[OF assms] R_bounded[OF assms]
        conservation_N[OF assms]
  by auto

end

end
