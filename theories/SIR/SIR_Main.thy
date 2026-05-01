(*
  SIR_Main.thy — Main entry point importing all SIR theories.

  This theory provides a unified view of the complete SIR formalization.
  It imports all component theories and provides a summary of the main results.

  License: BSD-3-Clause
*)

theory SIR_Main
  imports
    SIR_Conservation
    SIR_Monotonicity
    SIR_Threshold
    SIR_Peak
    SIR_Invariant
begin

section \<open>Summary of Results\<close>

text \<open>
  The locale @{locale SIR_solution} formalizes a solution to the classical
  SIR epidemic model on a closed interval $[a, b]$ with parameters
  $\beta > 0$ (transmission rate) and $\gamma > 0$ (recovery rate).

  Assuming the solution exists with nonnegative compartments, we have proved:

  \begin{enumerate}
    \item \textbf{Conservation} (@{thm [source] SIR_solution.conservation}):
      $S(t) + I(t) + R(t) = S(a) + I(a) + R(a)$ for all $t \in [a,b]$.

    \item \textbf{Monotonicity of S} (@{thm [source] SIR_solution.S_nonincreasing}):
      $S$ is nonincreasing on $[a,b]$.

    \item \textbf{Monotonicity of R} (@{thm [source] SIR_solution.R_nondecreasing}):
      $R$ is nondecreasing on $[a,b]$.

    \item \textbf{Epidemic threshold} (@{thm [source] SIR_solution.epidemic_growth_iff}):
      $dI/dt > 0$ iff $I > 0$ and $\beta S > \gamma$.

    \item \textbf{Stationary infection condition} (@{thm [source] SIR_solution.peak_iff}):
      $dI/dt = 0$ with $I > 0$ iff $S = \gamma/\beta$.
      This characterizes the critical susceptible level at which the
      epidemic transitions from growing to declining.
  \end{enumerate}

  The conservation theorem is an instantiation of the generic
  @{thm [source] three_compartment_conservation} from the reusable
  compartmental model framework; similarly the monotonicity results
  use the framework corollaries
  @{thm [source] nonincreasing_from_nonpos_derivative} and
  @{thm [source] nondecreasing_from_nonneg_derivative}.

  Nonnegativity of compartments is assumed; existence and uniqueness of
  solutions are deferred to future work using the AFP ODE infrastructure.

  Additionally, we prove that the assumed nonnegativity together with
  conservation confines the trajectory to the simplex
  $\{(S,I,R) \mid S,I,R \ge 0,\; S+I+R=N\}$, establishing individual
  upper bounds on all compartments
  (@{thm [source] SIR_solution.simplex_invariant}).
\<close>

end
