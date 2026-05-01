(*
  SIR_Invariant.thy — Invariant region for the SIR system.

  Given conservation and nonnegativity (assumed in the locale), the
  trajectory is confined to the simplex
    {(S, I, R) | 0 ≤ S ∧ 0 ≤ I ∧ 0 ≤ R ∧ S + I + R = N}
  which is bounded (hence no blow-up). This establishes that the
  solution remains in a compact invariant region.

  License: BSD-3-Clause
*)

theory SIR_Invariant
  imports SIR_Conservation SIR_Monotonicity
begin

context SIR_solution
begin

section \<open>Invariant Region and Boundedness\<close>

text \<open>
  The trajectory of the SIR system is confined to the simplex
  \[
    \Delta_N = \{(S, I, R) \in \mathbb{R}^3 \mid S \ge 0,\; I \ge 0,\;
                 R \ge 0,\; S + I + R = N\}
  \]
  where $N = S(a) + I(a) + R(a)$ is the total population.
  This follows immediately from conservation and the nonnegativity
  assumptions. The simplex is a closed bounded subset of $\mathbb{R}^3$,
  so solutions cannot blow up in finite time.
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
  Combined simplex invariant: all compartments are nonneg and sum to $N$.
\<close>

corollary simplex_invariant:
  assumes "t \<in> {a..b}"
  shows "0 \<le> S t" and "0 \<le> I t" and "0 \<le> R t"
    and "S t + I t + R t = total_population"
  using S_bounded[OF assms] I_bounded[OF assms] R_bounded[OF assms]
        conservation_N[OF assms]
  by auto

end

end
