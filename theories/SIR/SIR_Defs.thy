(*
  SIR_Defs.thy — Locale definition for the classical SIR epidemic model.

  We define the SIR system as a locale capturing:
    - Positive parameters beta (transmission rate) and gamma (recovery rate)
    - Differentiable trajectories S, I, R satisfying the SIR ODEs
    - Nonnegativity of all compartments (physical constraint)

  The locale assumes a solution exists on a closed interval [a, b] and
  derives properties of that solution. Existence and uniqueness are deferred
  to future work (requiring the AFP ODE entry or equivalent).

  License: BSD-3-Clause
*)

theory SIR_Defs
  imports Compartmental_Model
begin

section \<open>The Classical SIR Model\<close>

text \<open>
  The SIR model partitions a population into three compartments:
  \begin{description}
    \item[S (Susceptible)] Individuals who can be infected.
    \item[I (Infectious)] Individuals who are infected and can transmit.
    \item[R (Recovered)] Individuals who have recovered and are immune.
  \end{description}

  The ODE system is:
  \[
    \frac{dS}{dt} = -\beta S I, \quad
    \frac{dI}{dt} = \beta S I - \gamma I, \quad
    \frac{dR}{dt} = \gamma I
  \]
  where $\beta > 0$ is the transmission rate and $\gamma > 0$ is the recovery rate.
\<close>

locale SIR_solution =
  fixes \<beta> \<gamma> :: real
    and S I R :: "real \<Rightarrow> real"
    and a b :: real
  assumes pos_beta: "0 < \<beta>"
    and pos_gamma: "0 < \<gamma>"
    and interval: "a < b"
    and ode_S: "\<And>t. t \<in> {a..b} \<Longrightarrow> (S has_real_derivative (- \<beta> * S t * I t)) (at t)"
    and ode_I: "\<And>t. t \<in> {a..b} \<Longrightarrow>
      (I has_real_derivative (\<beta> * S t * I t - \<gamma> * I t)) (at t)"
    and ode_R: "\<And>t. t \<in> {a..b} \<Longrightarrow> (R has_real_derivative (\<gamma> * I t)) (at t)"
    and nonneg_S: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> S t"
    and nonneg_I: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> I t"
    and nonneg_R: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> R t"
begin

text \<open>Derived facts available throughout the locale.\<close>

lemma a_in_interval: "a \<in> {a..b}"
  using interval by auto

lemma beta_nonneg: "0 \<le> \<beta>"
  using pos_beta by auto

lemma gamma_nonneg: "0 \<le> \<gamma>"
  using pos_gamma by auto

end

end
