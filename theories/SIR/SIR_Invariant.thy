(*
  SIR_Invariant.thy — Boundedness of the SIR system.

  Given conservation and nonnegativity (assumed in the locale), all
  compartments are bounded by the total population N.
  This establishes that each compartment satisfies 0 ≤ X(t) ≤ N
  on the interval [a, b].

  Note: Nonnegativity is a locale assumption for the full trajectory.
  This is NOT a forward-invariance proof from initial conditions.

  License: BSD-3-Clause
*)

theory SIR_Invariant
  imports SIR_Conservation SIR_Monotonicity
begin

context SIR_solution
begin

section \<open>Boundedness of Compartments\<close>

text \<open>
  Given conservation and the nonnegativity assumptions (locale hypotheses),
  each compartment is bounded by the total population:
  \[
    0 \le X(t) \le N \quad \text{for } X \in \{S, I, R\}
  \]
  where $N = S(a) + I(a) + R(a)$.

  Note: nonnegativity is assumed for the full trajectory; this is
  \emph{not} a forward-invariance result from initial conditions.
\<close>

theorem S_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t" and "S t \<le> total_population"
proof -
  show "0 \<le> S t" by (rule nonneg_S[OF assms])
next
  have "S t \<le> S t + I t + R t"
    using nonneg_I[OF assms] nonneg_R[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "S t \<le> total_population" .
qed

theorem I_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> I t" and "I t \<le> total_population"
proof -
  show "0 \<le> I t" by (rule nonneg_I[OF assms])
next
  have "I t \<le> S t + I t + R t"
    using nonneg_S[OF assms] nonneg_R[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "I t \<le> total_population" .
qed

theorem R_bounded:
  assumes "t \<in> {a..b}"
  shows "0 \<le> R t" and "R t \<le> total_population"
proof -
  show "0 \<le> R t" by (rule nonneg_R[OF assms])
next
  have "R t \<le> S t + I t + R t"
    using nonneg_S[OF assms] nonneg_I[OF assms] by linarith
  also have "\<dots> = total_population"
    by (rule conservation_N[OF assms])
  finally show "R t \<le> total_population" .
qed

text \<open>
  The total population is nonneg (it equals the sum of nonneg quantities).
\<close>

lemma total_population_nonneg: "0 \<le> total_population"
  unfolding total_population_def
  using nonneg_S[OF a_in_interval] nonneg_I[OF a_in_interval]
        nonneg_R[OF a_in_interval]
  by linarith

text \<open>
  Combined boundedness: all compartments are nonneg (assumed) and bounded by $N$.
\<close>

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
