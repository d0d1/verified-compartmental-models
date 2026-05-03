(*
  SIR_Main.thy — Main entry point importing all SIR theories.

  This theory provides a unified view of the complete SIR formalization.
  It imports all component theories and provides a summary of the main results.

  License: BSD-3-Clause
*)

theory SIR_Main
  imports
    "VCM_Base.SIR_Forward_Invariance"
    "VCM_Base.SIR_Conservation"
    "VCM_Base.SIR_Monotonicity"
    "VCM_Base.SIR_Threshold"
    "VCM_Base.SIR_Peak"
    "VCM_Base.SIR_Phase_Plane"
    "VCM_Base.SIR_Invariant"
    SIR_Existence
begin


section \<open>Summary of Results\<close>

text \<open>
  The locale @{locale SIR_solution} formalizes a solution to the classical
  SIR epidemic model on a closed interval $[a, b]$ with parameters
  $\beta > 0$ (transmission rate) and $\gamma > 0$ (recovery rate).

  The locale assumes only the ODE equations and \emph{nonneg initial conditions}.
  All trajectory-level properties (nonnegativity, boundedness, monotonicity)
  are \emph{derived}, not assumed.

  \paragraph{Forward Invariance (from initial conditions only).}
  \begin{enumerate}
    \item \textbf{S nonneg} (@{thm [source] SIR_solution.S_nonneg}):
      $S(t) \ge 0$ derived from $S(a) \ge 0$ using the integrating factor method.
    \item \textbf{I nonneg} (@{thm [source] SIR_solution.I_nonneg}):
      $I(t) \ge 0$ derived from $I(a) \ge 0$ using the integrating factor method.
    \item \textbf{R nonneg} (@{thm [source] SIR_solution.R_nonneg}):
      $R(t) \ge 0$ derived from $R(a) \ge 0$ and $I \ge 0$.
  \end{enumerate}

  \paragraph{Solution Formulas.}
  \begin{enumerate}
    \item \textbf{S solution} (@{thm [source] SIR_solution.S_solution}):
      $S(t) = S(a) \cdot \exp(-\beta \int_a^t I)$.
    \item \textbf{I solution} (@{thm [source] SIR_solution.I_solution}):
      $I(t) = I(a) \cdot \exp(\int_a^t (\beta S - \gamma))$.
  \end{enumerate}

  \paragraph{Structural Properties.}
  \begin{enumerate}
    \item \textbf{Conservation} (@{thm [source] SIR_solution.conservation}):
      $S(t) + I(t) + R(t) = S(a) + I(a) + R(a)$ for all $t \in [a,b]$.
    \item \textbf{Monotonicity of S} (@{thm [source] SIR_solution.S_nonincreasing}):
      $S$ is nonincreasing on $[a,b]$.
    \item \textbf{Monotonicity of R} (@{thm [source] SIR_solution.R_nondecreasing}):
      $R$ is nondecreasing on $[a,b]$.
    \item \textbf{Boundedness} (@{thm [source] SIR_solution.compartment_bounds}):
      $0 \le X(t) \le N$ for $X \in \{S, I, R\}$.
  \end{enumerate}

  \paragraph{Epidemic Dynamics.}
  \begin{enumerate}
    \item \textbf{Growth condition} (@{thm [source] SIR_solution.epidemic_growth_iff}):
      $dI/dt > 0$ iff $I > 0$ and $\beta S > \gamma$.
    \item \textbf{Reproduction number} (@{thm [source] SIR_solution.epidemic_growth_R_eff}):
      Growth iff $R_e(t) = \beta S(t)/\gamma > 1$.
    \item \textbf{Peak condition} (@{thm [source] SIR_solution.peak_iff}):
      $dI/dt = 0$ with $I > 0$ iff $S = \gamma/\beta$.
    \item \textbf{KM invariant} (@{thm [source] SIR_solution.KM_invariant_value}):
      $I + S - (\gamma/\beta)\ln S$ is constant (Kermack-McKendrick first integral).
  \end{enumerate}

  The forward invariance results use the generic
  @{thm [source] linear_ode_solution} framework theorem (integrating factor
  method). Conservation uses @{thm [source] three_compartment_conservation}.
  Monotonicity uses @{thm [source] nonincreasing_from_nonpos_derivative} and
  @{thm [source] nondecreasing_from_nonneg_derivative}.

  Existence and uniqueness of solutions is proved via the AFP
  Picard-Lindel\"of infrastructure (locale @{locale c1_on_open}).
  The SIR vector field is $C^1$, hence locally Lipschitz. Conservation and
  forward invariance confine the flow to a compact simplex, giving global
  forward existence via @{text flow_in_compact_right_existence}.
  The locale @{locale SIR_ODE} provides the unconditional bridge: given
  initial conditions alone, it constructs the unique global solution and
  interprets @{locale SIR_solution}, making all the above results
  unconditional consequences of the initial-value problem.
\<close>


end
