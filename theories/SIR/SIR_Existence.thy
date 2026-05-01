(*
  SIR_Existence.thy — Existence and uniqueness for the SIR ODE system.

  Uses the AFP Ordinary_Differential_Equations entry (Picard-Lindelöf) to prove:
    1. The SIR vector field is continuously differentiable (C¹) on all of ℝ³.
    2. Local existence and uniqueness of solutions (from c1_on_open).
    3. Global forward existence for nonnegative initial data via conservation
       and the continuation lemma (flow_in_compact_right_existence).
    4. Bridge to the scalar SIR_solution locale, making all 56 existing
       theorems unconditional.

  License: BSD-3-Clause
*)

theory SIR_Existence
  imports
    SIR_Defs
    "Ordinary_Differential_Equations.ODE_Analysis"
begin

section \<open>SIR Vector Field Definition\<close>

text \<open>
  We define the SIR system as an autonomous vector ODE on @{typ "real^3"}.
  Components: $1 = S$, $2 = I$, $3 = R$.
\<close>

definition sir_vf :: "real \<Rightarrow> real \<Rightarrow> (real^3) \<Rightarrow> (real^3)" where
  "sir_vf \<beta> \<gamma> x = (\<chi> i.
     if i = 1 then - \<beta> * (x$1) * (x$2)
     else if i = 2 then \<beta> * (x$1) * (x$2) - \<gamma> * (x$2)
     else \<gamma> * (x$2))"

lemma sir_vf_components:
  "(sir_vf \<beta> \<gamma> x)$1 = - \<beta> * (x$1) * (x$2)"
  "(sir_vf \<beta> \<gamma> x)$2 = \<beta> * (x$1) * (x$2) - \<gamma> * (x$2)"
  "(sir_vf \<beta> \<gamma> x)$3 = \<gamma> * (x$2)"
  unfolding sir_vf_def by simp_all

lemma sir_vf_sum_zero:
  "(sir_vf \<beta> \<gamma> x)$1 + (sir_vf \<beta> \<gamma> x)$2 + (sir_vf \<beta> \<gamma> x)$3 = 0"
  unfolding sir_vf_components by simp

section \<open>Continuous Differentiability\<close>

text \<open>
  The SIR vector field is polynomial, hence $C^1$ on all of @{term "UNIV :: (real^3) set"}.
  We compute the Jacobian explicitly and prove differentiability.
\<close>

definition sir_vf_deriv :: "real \<Rightarrow> real \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow>\<^sub>L (real^3)" where
  "sir_vf_deriv \<beta> \<gamma> x = blinfun_of_matrix (\<lambda> i j.
     if i = axis 1 1 \<and> j = axis 1 1 then - \<beta> * (x$2)
     else if i = axis 1 1 \<and> j = axis 2 1 then - \<beta> * (x$1)
     else if i = axis 2 1 \<and> j = axis 1 1 then \<beta> * (x$2)
     else if i = axis 2 1 \<and> j = axis 2 1 then \<beta> * (x$1) - \<gamma>
     else if i = axis 3 1 \<and> j = axis 2 1 then \<gamma>
     else 0)"

lemma sir_vf_has_derivative:
  "(sir_vf \<beta> \<gamma> has_derivative blinfun_apply (sir_vf_deriv \<beta> \<gamma> x)) (at x)"
proof -
  \<comment> \<open>Step 1: Show that each component of sir\_vf has the expected derivative.\<close>
  have d_nth1: "((\<lambda>y :: real^3. y$1) has_derivative (\<lambda>h :: real^3. h$1)) (at x)"
    using bounded_linear_imp_has_derivative[OF bounded_linear_vec_nth[where i="1::3"]]
    by auto
  have d_nth2: "((\<lambda>y :: real^3. y$2) has_derivative (\<lambda>h :: real^3. h$2)) (at x)"
    using bounded_linear_imp_has_derivative[OF bounded_linear_vec_nth[where i="2::3"]]
    by auto
  have d_prod: "((\<lambda>y. y$1 * y$2) has_derivative (\<lambda>h. x$1 * h$2 + h$1 * x$2)) (at x)"
    by (rule bounded_bilinear.FDERIV[OF bounded_bilinear_mult d_nth1 d_nth2])
  have d_comp1: "((\<lambda>y. - \<beta> * (y$1 * y$2)) has_derivative (\<lambda>h. - \<beta> * (x$1 * h$2 + h$1 * x$2))) (at x)"
    by (intro derivative_eq_intros d_prod) auto
  have d_comp2: "((\<lambda>y. \<beta> * (y$1 * y$2) - \<gamma> * y$2) has_derivative
                  (\<lambda>h. \<beta> * (x$1 * h$2 + h$1 * x$2) - \<gamma> * h$2)) (at x)"
    by (intro derivative_eq_intros d_prod d_nth2) auto
  have d_comp3: "((\<lambda>y. \<gamma> * y$2) has_derivative (\<lambda>h. \<gamma> * h$2)) (at x)"
    by (intro derivative_eq_intros d_nth2) auto
  \<comment> \<open>Step 2: Assemble into componentwise derivative of the vector function.\<close>
  have "(sir_vf \<beta> \<gamma> has_derivative (\<lambda>h. \<chi> i.
      if i = 1 then - \<beta> * (x$1 * h$2 + h$1 * x$2)
      else if i = 2 then \<beta> * (x$1 * h$2 + h$1 * x$2) - \<gamma> * h$2
      else \<gamma> * h$2)) (at x)"
    (is "(_ has_derivative ?D) _")
    unfolding has_derivative_componentwise_within[where S=UNIV, simplified]
  proof
    fix b :: "real^3" assume "b \<in> Basis"
    then obtain i :: 3 where bi: "b = axis i 1" by (auto simp: Basis_vec_def)
    show "((\<lambda>y. sir_vf \<beta> \<gamma> y \<bullet> b) has_derivative (\<lambda>h. ?D h \<bullet> b)) (at x)"
      unfolding bi inner_axis sir_vf_def
    proof (cases "i = 1")
      case True then show ?thesis using d_comp1 by simp
    next
      case False
      show ?thesis
      proof (cases "i = 2")
        case True then show ?thesis using d_comp2 by simp
      next
        case False
        then have "i = 3" using \<open>i \<noteq> 1\<close> exhaust_3[of i] by auto
        then show ?thesis using d_comp3 by simp
      qed
    qed
  qed
  \<comment> \<open>Step 3: Show this equals the blinfun application.\<close>
  moreover have "?D = blinfun_apply (sir_vf_deriv \<beta> \<gamma> x)"
  proof (rule ext)
    fix h :: "real^3"
    show "?D h = blinfun_apply (sir_vf_deriv \<beta> \<gamma> x) h"
      unfolding sir_vf_deriv_def blinfun_of_matrix_apply
      by (simp add: vec_eq_iff sum_3 inner_axis algebra_simps
               forall_3 axis_eq_axis)
  qed
  ultimately show ?thesis by simp
qed

lemma continuous_on_sir_vf_deriv:
  "continuous_on UNIV (sir_vf_deriv \<beta> \<gamma>)"
  unfolding sir_vf_deriv_def
proof (intro continuous_on_blinfun_of_matrix)
  fix i j :: "real^3" assume "i \<in> Basis" "j \<in> Basis"
  then obtain a b :: 3 where ab: "i = axis a 1" "j = axis b 1"
    by (auto simp: Basis_vec_def)
  show "continuous_on UNIV (\<lambda>x. if i = axis 1 1 \<and> j = axis 1 1 then - \<beta> * x $ 2
        else if i = axis 1 1 \<and> j = axis 2 1 then - \<beta> * x $ 1
        else if i = axis 2 1 \<and> j = axis 1 1 then \<beta> * x $ 2
        else if i = axis 2 1 \<and> j = axis 2 1 then \<beta> * x $ 1 - \<gamma>
        else if i = axis 3 1 \<and> j = axis 2 1 then \<gamma> else 0)"
    unfolding ab
    by (cases a rule: exhaust_3; cases b rule: exhaust_3;
        simp add: axis_eq_axis; intro continuous_intros)
qed

text \<open>
  Instantiate the @{locale c1_on_open} locale for the SIR vector field.
  This immediately gives us:
  \begin{itemize}
    \item Local Lipschitz continuity (via @{locale auto_ll_on_open})
    \item The maximal flow @{term flow0} and existence interval @{term existence_ivl0}
    \item Local existence and uniqueness of solutions
  \end{itemize}
\<close>

interpretation sir_c1: c1_on_open "sir_vf \<beta> \<gamma>" "sir_vf_deriv \<beta> \<gamma>" "UNIV :: (real^3) set"
  for \<beta> \<gamma>
proof unfold_locales
  show "open (UNIV :: (real^3) set)" by simp
next
  fix x :: "real^3"
  show "(sir_vf \<beta> \<gamma> has_derivative blinfun_apply (sir_vf_deriv \<beta> \<gamma> x)) (at x)"
    by (rule sir_vf_has_derivative)
next
  show "continuous_on UNIV (sir_vf_deriv \<beta> \<gamma>)"
    by (rule continuous_on_sir_vf_deriv)
qed

section \<open>Local Existence and Uniqueness\<close>

text \<open>
  From the @{locale c1_on_open} interpretation, we inherit the autonomous flow
  and its properties. For any initial condition @{term "x0 \<in> UNIV"},
  there exists a unique maximal solution @{term "sir_c1.flow0 \<beta> \<gamma> x0"} defined
  on the open interval @{term "sir_c1.existence_ivl0 \<beta> \<gamma> x0"} containing 0.
\<close>

lemma sir_local_existence:
  "0 \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  by simp

lemma sir_open_existence_ivl:
  "open (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
  by simp

lemma sir_is_interval_existence_ivl:
  "is_interval (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
  by (simp add: sir_c1.is_interval_existence_ivl)

lemma sir_convex_existence_ivl:
  "convex (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
  by (rule is_interval_convex[OF sir_is_interval_existence_ivl])

lemma sir_flow_solves_ode:
  "(sir_c1.flow0 \<beta> \<gamma> x0 has_vderiv_on (\<lambda>t. sir_vf \<beta> \<gamma> (sir_c1.flow0 \<beta> \<gamma> x0 t)))
   (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
proof -
  have "x0 \<in> (UNIV :: (real^3) set)" by simp
  then show ?thesis by (rule sir_c1.flow_has_vderiv_on)
qed

lemma sir_flow_solves_ode':
  "(sir_c1.flow0 \<beta> \<gamma> x0 solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>))
   (sir_c1.existence_ivl0 \<beta> \<gamma> x0) UNIV"
proof -
  have "x0 \<in> (UNIV :: (real^3) set)" by simp
  then show ?thesis by (rule sir_c1.flow_solves_ode)
qed

lemma sir_segment_subset:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  shows "closed_segment 0 t \<subseteq> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
proof -
  have "x0 \<in> (UNIV :: (real^3) set)" by simp
  then show ?thesis using assms by (rule sir_c1.closed_segment_subset_existence_ivl)
qed

lemma sir_flow_continuous_on:
  "continuous_on (sir_c1.existence_ivl0 \<beta> \<gamma> x0) (sir_c1.flow0 \<beta> \<gamma> x0)"
proof -
  have "x0 \<in> (UNIV :: (real^3) set)" by simp
  then show ?thesis by (rule sir_c1.flow_continuous_on)
qed

lemma sir_flow_initial:
  "sir_c1.flow0 \<beta> \<gamma> x0 0 = x0"
  by simp

lemma sir_flow_unique:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
    and "y 0 = x0"
    and "(y has_vderiv_on (\<lambda>t. sir_vf \<beta> \<gamma> (y t))) (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
  shows "sir_c1.flow0 \<beta> \<gamma> x0 t = y t"
proof -
  let ?E = "sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  have sol_y: "(y solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>)) ?E UNIV"
    using assms(3) unfolding solves_ode_def has_vderiv_on_def by auto
  have sol_fl: "(sir_c1.flow0 \<beta> \<gamma> x0 solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>)) ?E UNIV"
    by (rule sir_flow_solves_ode')
  have iv: "sir_c1.flow0 \<beta> \<gamma> x0 0 = y 0"
    using assms(2) sir_flow_initial by simp
  show ?thesis
    by (rule sir_c1.unique_solution[OF sol_fl sol_y sir_local_existence _
            sir_is_interval_existence_ivl iv assms(1)]) simp
qed

section \<open>Conservation Along the Flow\<close>

text \<open>
  The sum $S + I + R$ is conserved along the flow. This follows from the
  derivative sum being identically zero.
\<close>

lemma sir_flow_conservation:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  shows "(sir_c1.flow0 \<beta> \<gamma> x0 t)$1 + (sir_c1.flow0 \<beta> \<gamma> x0 t)$2 +
         (sir_c1.flow0 \<beta> \<gamma> x0 t)$3 = x0$1 + x0$2 + x0$3"
proof -
  let ?E = "sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  define g where "g t = ?fl t $1 + ?fl t $2 + ?fl t $3" for t
  have flow_ode: "(?fl has_vderiv_on (\<lambda>t. sir_vf \<beta> \<gamma> (?fl t))) ?E"
    by (rule sir_flow_solves_ode)
  have open_E: "open ?E" by simp
  have "(g has_vderiv_on (\<lambda>t. 0)) ?E"
    unfolding has_vderiv_on_def
  proof
    fix s assume "s \<in> ?E"
    then have hvd: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s)) (at s)"
      using flow_ode open_E
      by (simp add: has_vderiv_on_def at_within_open)
    have "(((\<lambda>v. v$1) \<circ> ?fl) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$1) (at s)"
      using bounded_linear.has_vector_derivative[OF bounded_linear_vec_nth hvd] by (simp add: o_def)
    then have d1: "((\<lambda>t. ?fl t $1) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$1) (at s)"
      by (simp add: o_def)
    have "(((\<lambda>v. v$2) \<circ> ?fl) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$2) (at s)"
      using bounded_linear.has_vector_derivative[OF bounded_linear_vec_nth hvd] by (simp add: o_def)
    then have d2: "((\<lambda>t. ?fl t $2) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$2) (at s)"
      by (simp add: o_def)
    have "(((\<lambda>v. v$3) \<circ> ?fl) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$3) (at s)"
      using bounded_linear.has_vector_derivative[OF bounded_linear_vec_nth hvd] by (simp add: o_def)
    then have d3: "((\<lambda>t. ?fl t $3) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s))$3) (at s)"
      by (simp add: o_def)
    have "(g has_vector_derivative
        ((sir_vf \<beta> \<gamma> (?fl s))$1 + (sir_vf \<beta> \<gamma> (?fl s))$2 + (sir_vf \<beta> \<gamma> (?fl s))$3)) (at s)"
      unfolding g_def using d1 d2 d3
      by (intro has_vector_derivative_add; assumption)
    then show "(g has_vector_derivative 0) (at s within ?E)"
      by (simp add: sir_vf_sum_zero at_within_open[OF \<open>s \<in> ?E\<close> open_E])
  qed
  moreover have "convex ?E"
    by (intro is_interval_convex sir_c1.is_interval_existence_ivl)
  ultimately obtain c where gc: "\<And>s. s \<in> ?E \<Longrightarrow> g s = c"
    by (rule has_vderiv_on_zero_constant)
  have "g 0 = c" by (rule gc) simp
  also have "g 0 = x0$1 + x0$2 + x0$3"
    unfolding g_def by simp
  finally have "c = x0$1 + x0$2 + x0$3" ..
  then show ?thesis using gc[OF assms] unfolding g_def by simp
qed

section \<open>Forward Invariance of the Nonnegative Orthant\<close>

text \<open>
  We show that if $S(0) \geq 0$, $I(0) \geq 0$, $R(0) \geq 0$,
  then the flow stays nonnegative for all forward time in the existence interval.
  Combined with conservation, this gives boundedness.

  The proof uses the existing framework lemma @{thm linear_ode_nonneg}:
  if $X' = f(t) \cdot X$ and $X(0) \geq 0$, then $X(t) \geq 0$.
  The SIR equations are linear in each component when the others are fixed.
\<close>

lemma sir_flow_component_deriv:
  assumes "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  shows "((\<lambda>t. sir_c1.flow0 \<beta> \<gamma> x0 t $ i) has_real_derivative
         (sir_vf \<beta> \<gamma> (sir_c1.flow0 \<beta> \<gamma> x0 s)) $ i) (at s)"
proof -
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  have open_E: "open (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
    by (rule sir_open_existence_ivl)
  have flow_vd: "(?fl has_vderiv_on (\<lambda>t. sir_vf \<beta> \<gamma> (?fl t))) (sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
    by (rule sir_flow_solves_ode)
  have hvd: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s)) (at s)"
    using flow_vd
    by (simp add: has_vderiv_on_def at_within_open[OF assms open_E])
  have "((\<lambda>t. ?fl t $ i) has_vector_derivative (sir_vf \<beta> \<gamma> (?fl s)) $ i) (at s)"
    using bounded_linear.has_vector_derivative[OF bounded_linear_vec_nth hvd]
    by (simp add: o_def)
  then show ?thesis
    by (simp add: has_real_derivative_iff_has_vector_derivative)
qed

lemma sir_flow_continuous_on_segment:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" "0 \<le> t"
  shows "continuous_on {0..t} (\<lambda>s. sir_c1.flow0 \<beta> \<gamma> x0 s $ i)"
proof -
  have seg: "{0..t} \<subseteq> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
    using sir_segment_subset
      assms sir_local_existence
    by (simp add: closed_segment_eq_real_ivl)
  show ?thesis
    by (intro continuous_on_subset[OF _ seg]
         continuous_on_compose2[OF continuous_on_vec_nth sir_flow_continuous_on subset_refl])
qed

lemma sir_flow_nonneg_S:
  assumes "0 < \<beta>" "0 < \<gamma>"
    and nonneg: "0 \<le> x0$1" "0 \<le> x0$2" "0 \<le> x0$3"
    and t_in: "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" and "0 \<le> t"
  shows "0 \<le> (sir_c1.flow0 \<beta> \<gamma> x0 t)$1"
proof (cases "t = 0")
  case True
  then show ?thesis using nonneg by simp
next
  case False
  then have "0 < t" using \<open>0 \<le> t\<close> by auto
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  let ?S = "\<lambda>s. ?fl s $ 1"
  let ?f = "\<lambda>s. - \<beta> * (?fl s $ 2)"
  have S_ode: "(?S has_real_derivative (?f s * ?S s)) (at s)" if "s \<in> {0..t}" for s
  proof -
    have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_segment_subset
        t_in sir_local_existence that
      by (auto simp: closed_segment_eq_real_ivl)
    have "((\<lambda>t. ?fl t $ 1) has_real_derivative (sir_vf \<beta> \<gamma> (?fl s)) $ 1) (at s)"
      by (rule sir_flow_component_deriv[OF s_in])
    also have "(sir_vf \<beta> \<gamma> (?fl s)) $ 1 = - \<beta> * (?fl s $ 1) * (?fl s $ 2)"
      by (simp add: sir_vf_components)
    also have "- \<beta> * (?fl s $ 1) * (?fl s $ 2) = ?f s * ?S s"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have f_cont: "continuous_on {0..t} ?f"
    by (intro continuous_intros sir_flow_continuous_on_segment[OF t_in \<open>0 \<le> t\<close>])
  show ?thesis
    using linear_ode_nonneg[OF \<open>0 < t\<close> f_cont S_ode _ nonneg(1)]
    by simp
qed

lemma sir_flow_nonneg_I:
  assumes "0 < \<beta>" "0 < \<gamma>"
    and nonneg: "0 \<le> x0$1" "0 \<le> x0$2" "0 \<le> x0$3"
    and t_in: "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" and "0 \<le> t"
  shows "0 \<le> (sir_c1.flow0 \<beta> \<gamma> x0 t)$2"
proof (cases "t = 0")
  case True
  then show ?thesis using nonneg by simp
next
  case False
  then have "0 < t" using \<open>0 \<le> t\<close> by auto
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  let ?I_comp = "\<lambda>s. ?fl s $ 2"
  let ?f = "\<lambda>s. \<beta> * (?fl s $ 1) - \<gamma>"
  have I_ode: "(?I_comp has_real_derivative (?f s * ?I_comp s)) (at s)" if "s \<in> {0..t}" for s
  proof -
    have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_segment_subset
        t_in sir_local_existence that
      by (auto simp: closed_segment_eq_real_ivl)
    have "((\<lambda>t. ?fl t $ 2) has_real_derivative (sir_vf \<beta> \<gamma> (?fl s)) $ 2) (at s)"
      by (rule sir_flow_component_deriv[OF s_in])
    also have "(sir_vf \<beta> \<gamma> (?fl s)) $ 2 = \<beta> * (?fl s $ 1) * (?fl s $ 2) - \<gamma> * (?fl s $ 2)"
      by (simp add: sir_vf_components)
    also have "\<beta> * (?fl s $ 1) * (?fl s $ 2) - \<gamma> * (?fl s $ 2) = ?f s * ?I_comp s"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have f_cont: "continuous_on {0..t} ?f"
    by (intro continuous_intros sir_flow_continuous_on_segment[OF t_in \<open>0 \<le> t\<close>])
  show ?thesis
    using linear_ode_nonneg[OF \<open>0 < t\<close> f_cont I_ode _ nonneg(2)]
    by simp
qed

lemma sir_flow_nonneg_R:
  assumes "0 < \<beta>" "0 < \<gamma>"
    and nonneg: "0 \<le> x0$1" "0 \<le> x0$2" "0 \<le> x0$3"
    and t_in: "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" and "0 \<le> t"
  shows "0 \<le> (sir_c1.flow0 \<beta> \<gamma> x0 t)$3"
proof (cases "t = 0")
  case True
  then show ?thesis using nonneg by simp
next
  case False
  then have "0 < t" using \<open>0 \<le> t\<close> by auto
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  have R_deriv: "\<And>s. s \<in> {0..t} \<Longrightarrow>
    ((\<lambda>t. ?fl t $ 3) has_real_derivative \<gamma> * (?fl s $ 2)) (at s)"
  proof -
    fix s assume "s \<in> {0..t}"
    then have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_segment_subset
        t_in sir_local_existence
      by (auto simp: closed_segment_eq_real_ivl)
    have "((\<lambda>t. ?fl t $ 3) has_real_derivative (sir_vf \<beta> \<gamma> (?fl s)) $ 3) (at s)"
      by (rule sir_flow_component_deriv[OF s_in])
    then show "((\<lambda>t. ?fl t $ 3) has_real_derivative \<gamma> * (?fl s $ 2)) (at s)"
      by (simp add: sir_vf_components)
  qed
  have "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 \<le> \<gamma> * (?fl s $ 2)"
  proof -
    fix s assume "s \<in> {0..t}"
    then have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_segment_subset
        t_in sir_local_existence
      by (auto simp: closed_segment_eq_real_ivl)
    have "0 \<le> s" using \<open>s \<in> {0..t}\<close> by auto
    then show "0 \<le> \<gamma> * (?fl s $ 2)"
      using sir_flow_nonneg_I[OF assms(1-5) s_in] assms(2) by auto
  qed
  then show ?thesis
    using nonneg_deriv_nonneg[OF \<open>0 < t\<close> R_deriv _ _ nonneg(3)]
    by auto
qed

section \<open>Global Forward Existence\<close>

text \<open>
  For nonneg initial data with $N = S_0 + I_0 + R_0$, the flow stays in the
  compact simplex $\{x \in \mathbb{R}^3 \mid x_i \geq 0, \sum x_i = N\}$.
  By the continuation lemma, the solution exists for all $t \geq 0$.
\<close>

definition sir_simplex :: "real \<Rightarrow> (real^3) set" where
  "sir_simplex N = {x :: real^3. x$1 \<ge> 0 \<and> x$2 \<ge> 0 \<and> x$3 \<ge> 0 \<and> x$1 + x$2 + x$3 = N}"

lemma sir_simplex_compact:
  assumes "N \<ge> 0"
  shows "compact (sir_simplex N)"
proof -
  have "sir_simplex N \<subseteq> cball 0 N"
  proof
    fix x :: "real^3" assume "x \<in> sir_simplex N"
    then have h: "x$1 \<ge> 0" "x$2 \<ge> 0" "x$3 \<ge> 0" "x$1 + x$2 + x$3 = N"
      unfolding sir_simplex_def by auto
    have "norm x \<le> N"
    proof -
      have comp_le: "\<And>i :: 3. \<bar>x$i\<bar> \<le> N"
      proof -
        fix i :: 3
        have "x$i \<ge> 0 \<and> x$i \<le> N"
          using h exhaust_3[of i] by linarith
        then show "\<bar>x$i\<bar> \<le> N" by auto
      qed
      have "norm x \<le> sum (\<lambda>i. \<bar>x$i\<bar>) UNIV"
        by (rule norm_le_l1)
      also have "... \<le> sum (\<lambda>i :: 3. N) UNIV"
        by (rule sum_mono[OF comp_le])
      also have "... = 3 * N" by simp
      finally show "norm x \<le> N"
        using h by linarith
    qed
    then show "x \<in> cball 0 N" by (simp add: dist_norm)
  qed
  moreover have "closed (sir_simplex N)"
    unfolding sir_simplex_def
    by (intro closed_Collect_conj closed_Collect_le closed_Collect_eq continuous_intros)
  ultimately show ?thesis
    using compact_eq_bounded_closed bounded_subset[OF bounded_cball]
    by blast
qed

lemma sir_simplex_subset_UNIV: "sir_simplex N \<subseteq> (UNIV :: (real^3) set)"
  by simp

lemma sir_flow_in_simplex:
  assumes "0 < \<beta>" "0 < \<gamma>"
    and nonneg: "0 \<le> x0$1" "0 \<le> x0$2" "0 \<le> x0$3"
    and "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" and "0 \<le> t"
  shows "sir_c1.flow0 \<beta> \<gamma> x0 t \<in> sir_simplex (x0$1 + x0$2 + x0$3)"
  unfolding sir_simplex_def mem_Collect_eq
  using sir_flow_nonneg_S[OF assms] sir_flow_nonneg_I[OF assms]
        sir_flow_nonneg_R[OF assms] sir_flow_conservation[OF assms(6)]
  by auto

theorem sir_global_existence:
  assumes "0 < \<beta>" "0 < \<gamma>"
    and nonneg: "0 \<le> x0$1" "0 \<le> x0$2" "0 \<le> x0$3"
    and "0 \<le> t"
  shows "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
proof (rule sir_c1.flow_in_compact_right_existence[of \<beta> \<gamma> x0 "sir_simplex (x0$1 + x0$2 + x0$3)"])
  fix s assume "0 \<le> s" "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  then show "sir_c1.flow0 \<beta> \<gamma> x0 s \<in> sir_simplex (x0$1 + x0$2 + x0$3)"
    using sir_flow_in_simplex[OF assms(1-5)] by auto
next
  show "compact (sir_simplex (x0$1 + x0$2 + x0$3))"
    using nonneg by (intro sir_simplex_compact) linarith
next
  show "sir_simplex (x0$1 + x0$2 + x0$3) \<subseteq> UNIV" by simp
next
  show "x0 \<in> (UNIV :: (real^3) set)" by simp
next
  show "0 \<le> t" by fact
qed

section \<open>Bridge to Scalar SIR Locale\<close>

text \<open>
  We define a new locale @{text SIR_ODE} that takes scalar initial conditions
  and derives the existence of the unique solution. The components of the flow
  satisfy the scalar SIR ODEs, giving a sublocale relationship with
  @{locale SIR_solution}. This makes all 56 existing theorems unconditional.
\<close>

locale SIR_ODE =
  fixes \<beta> \<gamma> :: real
    and S\<^sub>0 I\<^sub>0 R\<^sub>0 :: real
  assumes pos_beta: "0 < \<beta>"
    and pos_gamma: "0 < \<gamma>"
    and nonneg_S0: "0 \<le> S\<^sub>0"
    and nonneg_I0: "0 \<le> I\<^sub>0"
    and nonneg_R0: "0 \<le> R\<^sub>0"
begin

definition x\<^sub>0 :: "real^3" where
  "x\<^sub>0 = (\<chi> i. if i = 1 then S\<^sub>0 else if i = 2 then I\<^sub>0 else R\<^sub>0)"

lemma x0_components: "x\<^sub>0$1 = S\<^sub>0" "x\<^sub>0$2 = I\<^sub>0" "x\<^sub>0$3 = R\<^sub>0"
  unfolding x\<^sub>0_def by simp_all

lemma x0_nonneg: "0 \<le> x\<^sub>0$1" "0 \<le> x\<^sub>0$2" "0 \<le> x\<^sub>0$3"
  using nonneg_S0 nonneg_I0 nonneg_R0 unfolding x0_components by auto

definition N :: real where "N = S\<^sub>0 + I\<^sub>0 + R\<^sub>0"

text \<open>The unique solution as scalar functions.\<close>

definition S_sol :: "real \<Rightarrow> real" where
  "S_sol t = (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)$1"

definition I_sol :: "real \<Rightarrow> real" where
  "I_sol t = (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)$2"

definition R_sol :: "real \<Rightarrow> real" where
  "R_sol t = (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)$3"

text \<open>Global forward existence: the solution exists for all $t \geq 0$.\<close>

lemma global_existence: "0 \<le> t \<Longrightarrow> t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
  using sir_global_existence[OF pos_beta pos_gamma x0_nonneg] by auto

text \<open>Initial conditions.\<close>

lemma sol_initial: "S_sol 0 = S\<^sub>0" "I_sol 0 = I\<^sub>0" "R_sol 0 = R\<^sub>0"
  unfolding S_sol_def I_sol_def R_sol_def
  using sir_flow_initial x0_components by simp_all

text \<open>The scalar functions satisfy the SIR ODEs.\<close>

lemma sol_ode_S:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
  shows "(S_sol has_real_derivative (- \<beta> * S_sol t * I_sol t)) (at t)"
proof -
  have "((\<lambda>t. sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t $ 1) has_real_derivative
        (sir_vf \<beta> \<gamma> (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)) $ 1) (at t)"
    by (rule sir_flow_component_deriv[OF assms])
  then show ?thesis
    unfolding S_sol_def I_sol_def sir_vf_components by (simp add: algebra_simps)
qed

lemma sol_ode_I:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
  shows "(I_sol has_real_derivative (\<beta> * S_sol t * I_sol t - \<gamma> * I_sol t)) (at t)"
proof -
  have "((\<lambda>t. sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t $ 2) has_real_derivative
        (sir_vf \<beta> \<gamma> (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)) $ 2) (at t)"
    by (rule sir_flow_component_deriv[OF assms])
  then show ?thesis
    unfolding S_sol_def I_sol_def sir_vf_components by (simp add: algebra_simps)
qed

lemma sol_ode_R:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
  shows "(R_sol has_real_derivative (\<gamma> * I_sol t)) (at t)"
proof -
  have "((\<lambda>t. sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t $ 3) has_real_derivative
        (sir_vf \<beta> \<gamma> (sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t)) $ 3) (at t)"
    by (rule sir_flow_component_deriv[OF assms])
  then show ?thesis
    unfolding R_sol_def I_sol_def sir_vf_components .
qed

text \<open>
  Bridge: for any interval $[0, b]$ with $b > 0$, we get a valid @{locale SIR_solution}
  interpretation. This makes all existing SIR theorems unconditional.
\<close>

lemma sir_solution_on_interval:
  assumes "0 < b"
  shows "SIR_solution \<beta> \<gamma> S_sol I_sol R_sol 0 b"
proof unfold_locales
  show "0 < \<beta>" by (rule pos_beta)
  show "0 < \<gamma>" by (rule pos_gamma)
  show "0 < b" by (rule assms)
  fix t assume "t \<in> {0..b}"
  then have "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
    using global_existence assms by auto
  then show "(S_sol has_real_derivative (- \<beta> * S_sol t * I_sol t)) (at t)"
    by (rule sol_ode_S)
  from \<open>t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0\<close>
  show "(I_sol has_real_derivative (\<beta> * S_sol t * I_sol t - \<gamma> * I_sol t)) (at t)"
    by (rule sol_ode_I)
  from \<open>t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0\<close>
  show "(R_sol has_real_derivative (\<gamma> * I_sol t)) (at t)"
    by (rule sol_ode_R)
next
  show "0 \<le> S_sol 0" using sol_initial nonneg_S0 by simp
  show "0 \<le> I_sol 0" using sol_initial nonneg_I0 by simp
  show "0 \<le> R_sol 0" using sol_initial nonneg_R0 by simp
qed

text \<open>Uniqueness: any other solution equals the flow.\<close>

theorem sir_uniqueness:
  assumes "0 < b"
    and ode_S': "\<And>t. t \<in> {0..b} \<Longrightarrow>
      (S' has_real_derivative (- \<beta> * S' t * I' t)) (at t)"
    and ode_I': "\<And>t. t \<in> {0..b} \<Longrightarrow>
      (I' has_real_derivative (\<beta> * S' t * I' t - \<gamma> * I' t)) (at t)"
    and ode_R': "\<And>t. t \<in> {0..b} \<Longrightarrow>
      (R' has_real_derivative (\<gamma> * I' t)) (at t)"
    and "S' 0 = S\<^sub>0" "I' 0 = I\<^sub>0" "R' 0 = R\<^sub>0"
    and "t \<in> {0..b}"
  shows "S' t = S_sol t \<and> I' t = I_sol t \<and> R' t = R_sol t"
proof -
  define y :: "real \<Rightarrow> real^3" where
    "y s = (\<chi> i. if i = 1 then S' s else if i = 2 then I' s else R' s)" for s
  have y0: "y 0 = x\<^sub>0"
    using assms(5-7) unfolding y_def x\<^sub>0_def by auto
  have seg: "{0..b} \<subseteq> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0"
    using sir_segment_subset
      global_existence[of b] assms(1)
    by (auto simp: closed_segment_eq_real_ivl)
  have y_vderiv: "(y has_vderiv_on (\<lambda>s. sir_vf \<beta> \<gamma> (y s))) {0..b}"
    unfolding has_vderiv_on_def
  proof
    fix s assume s_in: "s \<in> {0..b}"
    have S_hd: "(S' has_derivative (\<lambda>h. h * (- \<beta> * S' s * I' s))) (at s within {0..b})"
      using ode_S'[OF s_in, unfolded has_field_derivative_def]
      by (auto simp: mult.commute intro: has_derivative_at_withinI)
    have I_hd: "(I' has_derivative (\<lambda>h. h * (\<beta> * S' s * I' s - \<gamma> * I' s))) (at s within {0..b})"
      using ode_I'[OF s_in, unfolded has_field_derivative_def]
      by (auto simp: mult.commute intro: has_derivative_at_withinI)
    have R_hd: "(R' has_derivative (\<lambda>h. h * (\<gamma> * I' s))) (at s within {0..b})"
      using ode_R'[OF s_in, unfolded has_field_derivative_def]
      by (auto simp: mult.commute intro: has_derivative_at_withinI)
    have "(y has_derivative (\<lambda>h. h *\<^sub>R sir_vf \<beta> \<gamma> (y s))) (at s within {0..b})"
      unfolding has_derivative_componentwise_within
    proof
      fix b' :: "real^3" assume "b' \<in> Basis"
      then obtain i :: 3 where bi: "b' = axis i 1" by (auto simp: Basis_vec_def)
      show "((\<lambda>x. y x \<bullet> b') has_derivative (\<lambda>h. (h *\<^sub>R sir_vf \<beta> \<gamma> (y s)) \<bullet> b')) (at s within {0..b})"
      proof -
        have eq1: "\<And>x. y x \<bullet> axis i 1 = y x $ i"
          by (simp add: inner_axis)
        have eq2: "\<And>h. (h *\<^sub>R sir_vf \<beta> \<gamma> (y s)) \<bullet> axis i 1 = h * (sir_vf \<beta> \<gamma> (y s) $ i)"
          by (simp add: inner_axis)
        show ?thesis unfolding bi eq1 eq2
          using exhaust_3[of i] S_hd I_hd R_hd
          by (elim disjE; simp add: y_def sir_vf_def algebra_simps)
      qed
    qed
    then show "(y has_vector_derivative sir_vf \<beta> \<gamma> (y s)) (at s within {0..b})"
      by (simp add: has_vector_derivative_def)
  qed
  have t_in: "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x\<^sub>0" using seg assms(8) by auto
  have "sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 t = y t"
  proof (rule sir_c1.unique_solution[where U="{0..b}" and x="sir_c1.flow0 \<beta> \<gamma> x\<^sub>0" and y=y])
    show "(sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>)) {0..b} UNIV"
      using sir_flow_solves_ode' seg
      by (auto intro: solves_ode_on_subset)
    show "(y solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>)) {0..b} UNIV"
      using y_vderiv by (auto simp: solves_ode_def has_vderiv_on_def)
    show "(0::real) \<in> {0..b}" using assms(1) by auto
    show "{0..b} \<subseteq> UNIV" by simp
    show "is_interval {0..b}" by auto
    show "sir_c1.flow0 \<beta> \<gamma> x\<^sub>0 0 = y 0"
      using y0 by simp
    show "t \<in> {0..b}" by fact
  qed
  then show ?thesis
    unfolding S_sol_def I_sol_def R_sol_def y_def by simp
qed

end

end
