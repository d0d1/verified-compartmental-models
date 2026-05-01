(*
  SIR_Conservation.thy — Conservation law S + I + R = constant.

  The total population N = S + I + R is conserved under the SIR dynamics.
  This follows from the derivative sum being identically zero.

  License: BSD-3-Clause
*)

theory SIR_Conservation
  imports SIR_Defs
begin

context SIR_solution
begin

section \<open>Conservation of Total Population\<close>

text \<open>
  The derivative of $S + I + R$ is:
  \[
    (-\beta S I) + (\beta S I - \gamma I) + (\gamma I) = 0
  \]
  Hence the total population is constant on the interval.
\<close>

theorem conservation:
  assumes t_in: "t \<in> {a..b}"
  shows "S t + I t + R t = S a + I a + R a"
proof (rule three_compartment_conservation)
  show "a < b" by (rule interval)
next
  fix s assume "s \<in> {a..b}"
  then show "(S has_real_derivative (- \<beta> * S s * I s)) (at s)" by (rule ode_S)
next
  fix s assume "s \<in> {a..b}"
  then show "(I has_real_derivative (\<beta> * S s * I s - \<gamma> * I s)) (at s)" by (rule ode_I)
next
  fix s assume "s \<in> {a..b}"
  then show "(R has_real_derivative (\<gamma> * I s)) (at s)" by (rule ode_R)
next
  fix s assume "s \<in> {a..b}"
  show "- \<beta> * S s * I s + (\<beta> * S s * I s - \<gamma> * I s) + \<gamma> * I s = 0" by simp
next
  show "t \<in> {a..b}" by (rule t_in)
qed

text \<open>Convenient formulation with a named total population.\<close>

definition total_population :: real where
  "total_population \<equiv> S a + I a + R a"

corollary conservation_N:
  assumes "t \<in> {a..b}"
  shows "S t + I t + R t = total_population"
  unfolding total_population_def using conservation[OF assms] .

end

end
