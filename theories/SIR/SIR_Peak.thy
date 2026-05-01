(*
  SIR_Peak.thy — Peak condition for the infected compartment.

  At the peak of infection (dI/dt = 0 with I > 0), we have S = gamma/beta.
  This gives the critical susceptible population at which the epidemic
  transitions from growing to declining.

  License: BSD-3-Clause
*)

theory SIR_Peak
  imports SIR_Defs
begin

context SIR_solution
begin

section \<open>Peak of Infection\<close>

text \<open>
  When the derivative of $I$ is zero and $I > 0$:
  \[
    \beta S I - \gamma I = I(\beta S - \gamma) = 0
    \implies \beta S = \gamma
    \implies S = \frac{\gamma}{\beta}
  \]
  This identifies the critical value of $S$ at the epidemic peak.
\<close>

theorem peak_condition:
  assumes t_in: "t \<in> {a..b}"
    and I_pos: "I t > 0"
    and at_peak: "\<beta> * S t * I t - \<gamma> * I t = 0"
  shows "S t = \<gamma> / \<beta>"
proof -
  from at_peak have "I t * (\<beta> * S t - \<gamma>) = 0"
    by (simp add: algebra_simps)
  with I_pos have "\<beta> * S t - \<gamma> = 0" by simp
  then have "\<beta> * S t = \<gamma>" by simp
  with pos_beta show "S t = \<gamma> / \<beta>" by (simp add: field_simps)
qed

text \<open>Converse: if $S = \gamma/\beta$, then the derivative of $I$ is zero.\<close>

theorem peak_condition_converse:
  assumes t_in: "t \<in> {a..b}"
    and S_eq: "S t = \<gamma> / \<beta>"
  shows "\<beta> * S t * I t - \<gamma> * I t = 0"
proof -
  from S_eq pos_beta have "\<beta> * S t = \<gamma>"
    by (simp add: field_simps)
  then show ?thesis by (simp add: algebra_simps)
qed

text \<open>Combined characterization of the peak (when $I > 0$).\<close>

corollary peak_iff:
  assumes t_in: "t \<in> {a..b}" and I_pos: "I t > 0"
  shows "\<beta> * S t * I t - \<gamma> * I t = 0 \<longleftrightarrow> S t = \<gamma> / \<beta>"
  using peak_condition[OF t_in I_pos] peak_condition_converse[OF t_in] by auto

end

end
