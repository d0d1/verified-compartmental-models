(*
  SIR_Existence.thy — Existence and uniqueness for the SIR ODE system.

  Uses the AFP Ordinary_Differential_Equations entry (Picard-Lindelöf) to prove:
    1. The SIR vector field is continuously differentiable (C¹) on all of ℝ³.
    2. Local existence and uniqueness of solutions (from c1_on_open).
    3. Global forward existence for nonnegative initial data via conservation
       and the continuation lemma (flow_in_compact_right_existence).
    4. Bridge to the scalar SIR_solution locale under the SIR_ODE locale
       assumptions and on each nontrivial interval [0,b].

  License: BSD-3-Clause
*)

theory SIR_Existence
  imports
    "VCM_Base.SIR_Defs"
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

lemma bounded_linear_sir_total:
  "bounded_linear (\<lambda>x :: real^3. x$1 + x$2 + x$3)"
  by (intro bounded_linear_add bounded_linear_vec_nth)


section \<open>Continuous Differentiability\<close>

text \<open>
  The SIR vector field is polynomial, hence $C^1$ on all of @{term "UNIV :: (real^3) set"}.
  We compute the Jacobian explicitly and prove differentiability.
\<close>

definition sir_vf_deriv_fun :: "real \<Rightarrow> real \<Rightarrow> real^3 \<Rightarrow> real^3 \<Rightarrow> real^3" where
  "sir_vf_deriv_fun \<beta> \<gamma> x h = (\<chi> i.
      if i = 1 then - \<beta> * (x$1 * h$2 + h$1 * x$2)
      else if i = 2 then \<beta> * (x$1 * h$2 + h$1 * x$2) - \<gamma> * h$2
      else \<gamma> * h$2)"

lemma bounded_linear_sir_vf_deriv_fun:
  "bounded_linear (sir_vf_deriv_fun \<beta> \<gamma> x)"
proof -
  have "bounded_linear (\<lambda>h. sir_vf_deriv_fun \<beta> \<gamma> x h \<bullet> b)" if "b \<in> Basis" for b
  proof -
    from that obtain i :: 3 where b: "b = axis i 1"
      by (auto simp: Basis_vec_def)
    show ?thesis
      unfolding b sir_vf_deriv_fun_def
      by (cases "i = 1"; cases "i = 2";
          simp add: inner_axis algebra_simps;
          intro bounded_linear_add bounded_linear_sub bounded_linear_minus
            bounded_linear_const_mult bounded_linear_mult_const bounded_linear_vec_nth)
  qed
  then show ?thesis
    by (subst bounded_linear_componentwise_iff) auto
qed

definition sir_vf_deriv :: "real \<Rightarrow> real \<Rightarrow> (real^3) \<Rightarrow> (real^3) \<Rightarrow>\<^sub>L (real^3)" where
  "sir_vf_deriv \<beta> \<gamma> x = Blinfun (sir_vf_deriv_fun \<beta> \<gamma> x)"

lemma sir_vf_nth1_has_derivative:
  "((\<lambda>y :: real^3. y$1) has_derivative (\<lambda>h :: real^3. h$1)) (at x)"
  using bounded_linear_imp_has_derivative[OF bounded_linear_vec_nth[where i="1::3"]]
  by auto

lemma sir_vf_nth2_has_derivative:
  "((\<lambda>y :: real^3. y$2) has_derivative (\<lambda>h :: real^3. h$2)) (at x)"
  using bounded_linear_imp_has_derivative[OF bounded_linear_vec_nth[where i="2::3"]]
  by auto


lemma sir_vf_prod_has_derivative:
  "((\<lambda>y :: real^3. y$1 * y$2) has_derivative
      (\<lambda>h :: real^3. x$1 * h$2 + h$1 * x$2)) (at x)"
  by (rule bounded_bilinear.FDERIV[OF bounded_bilinear_mult
        sir_vf_nth1_has_derivative sir_vf_nth2_has_derivative])


lemma sir_vf_beta_prod_has_derivative:
  "((\<lambda>y :: real^3. \<beta> * (y$1 * y$2)) has_derivative
      (\<lambda>h :: real^3. \<beta> * (x$1 * h$2 + h$1 * x$2))) (at x)"
proof -
  have mult_beta: "((*) \<beta> has_derivative (*) \<beta>) (at (x$1 * x$2))"
    by (intro derivative_intros)
  show ?thesis
    using has_derivative_compose[OF sir_vf_prod_has_derivative mult_beta]
    by simp
qed


lemma sir_vf_neg_beta_prod_has_derivative:
  "((\<lambda>y :: real^3. - \<beta> * (y$1 * y$2)) has_derivative
      (\<lambda>h :: real^3. - \<beta> * (x$1 * h$2 + h$1 * x$2))) (at x)"
proof -
  have "((\<lambda>y :: real^3. - (\<beta> * (y$1 * y$2))) has_derivative
      (\<lambda>h :: real^3. - (\<beta> * (x$1 * h$2 + h$1 * x$2)))) (at x)"
    by (rule has_derivative_minus[OF sir_vf_beta_prod_has_derivative])
  then show ?thesis by simp
qed


lemma sir_vf_gamma_y2_has_derivative:
  "((\<lambda>y :: real^3. \<gamma> * y$2) has_derivative (\<lambda>h :: real^3. \<gamma> * h$2)) (at x)"
proof -
  have mult_gamma: "((*) \<gamma> has_derivative (*) \<gamma>) (at (x$2))"
    by (intro derivative_intros)
  show ?thesis
    using has_derivative_compose[OF sir_vf_nth2_has_derivative mult_gamma]
    by simp
qed


lemma sir_vf_comp2_has_derivative:
  "((\<lambda>y :: real^3. \<beta> * (y$1 * y$2) - \<gamma> * y$2) has_derivative
      (\<lambda>h :: real^3. \<beta> * (x$1 * h$2 + h$1 * x$2) - \<gamma> * h$2)) (at x)"
  by (rule has_derivative_diff[OF sir_vf_beta_prod_has_derivative sir_vf_gamma_y2_has_derivative])


lemma sir_vf_component1_has_derivative:
  "((\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$1) has_derivative
      (\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$1)) (at x)"
proof -
  have f_eq: "(\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$1) = (\<lambda>y. - \<beta> * (y$1 * y$2))"
    by (simp add: fun_eq_iff sir_vf_components algebra_simps)
  have d_eq: "(\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$1) =
      (\<lambda>h. - \<beta> * (x$1 * h$2 + h$1 * x$2))"
    by (simp add: fun_eq_iff sir_vf_deriv_fun_def)
  show ?thesis
    unfolding f_eq d_eq
    by (rule sir_vf_neg_beta_prod_has_derivative)
qed

lemma sir_vf_component2_has_derivative:
  "((\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$2) has_derivative
      (\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$2)) (at x)"
proof -
  have f_eq: "(\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$2) =
      (\<lambda>y. \<beta> * (y$1 * y$2) - \<gamma> * y$2)"
    by (simp add: fun_eq_iff sir_vf_components algebra_simps)
  have d_eq: "(\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$2) =
      (\<lambda>h. \<beta> * (x$1 * h$2 + h$1 * x$2) - \<gamma> * h$2)"
    by (simp add: fun_eq_iff sir_vf_deriv_fun_def)
  show ?thesis
    unfolding f_eq d_eq
    by (rule sir_vf_comp2_has_derivative)
qed

lemma sir_vf_component3_has_derivative:
  "((\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$3) has_derivative
      (\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$3)) (at x)"
proof -
  have f_eq: "(\<lambda>y :: real^3. (sir_vf \<beta> \<gamma> y)$3) = (\<lambda>y. \<gamma> * y$2)"
    by (simp add: fun_eq_iff sir_vf_components)
  have d_eq: "(\<lambda>h :: real^3. (sir_vf_deriv_fun \<beta> \<gamma> x h)$3) = (\<lambda>h. \<gamma> * h$2)"
    by (simp add: fun_eq_iff sir_vf_deriv_fun_def)
  show ?thesis
    unfolding f_eq d_eq
    by (rule sir_vf_gamma_y2_has_derivative)
qed


lemma sir_vf_deriv_apply:
  "blinfun_apply (sir_vf_deriv \<beta> \<gamma> x) h = sir_vf_deriv_fun \<beta> \<gamma> x h"
  unfolding sir_vf_deriv_def
  by (simp add: bounded_linear_Blinfun_apply bounded_linear_sir_vf_deriv_fun)


lemma sir_vf_axis_has_derivative:
  "((\<lambda>y :: real^3. sir_vf \<beta> \<gamma> y \<bullet> axis i 1) has_derivative
      (\<lambda>h :: real^3. sir_vf_deriv_fun \<beta> \<gamma> x h \<bullet> axis i 1)) (at x)"
proof (cases "i = 1")
  case True
  then show ?thesis
    using sir_vf_component1_has_derivative by (simp add: inner_axis)
next
  case False
  show ?thesis
  proof (cases "i = 2")
    case True
    then show ?thesis
      using sir_vf_component2_has_derivative by (simp add: inner_axis)
  next
    case False2: False
    then have "i = 3" using False exhaust_3[of i] by auto
    then show ?thesis
      using sir_vf_component3_has_derivative by (simp add: inner_axis)
  qed
qed


lemma sir_vf_has_derivative_fun:
  "(sir_vf \<beta> \<gamma> has_derivative sir_vf_deriv_fun \<beta> \<gamma> x) (at x)"
proof -
  have "(sir_vf \<beta> \<gamma> has_derivative sir_vf_deriv_fun \<beta> \<gamma> x) (at x within UNIV)"
    by (subst has_derivative_componentwise_within)
      (auto simp: Basis_vec_def intro: has_derivative_at_withinI sir_vf_axis_has_derivative)
  then show ?thesis by simp
qed


lemma sir_vf_has_derivative:
  "(sir_vf \<beta> \<gamma> has_derivative blinfun_apply (sir_vf_deriv \<beta> \<gamma> x)) (at x)"
proof -
  have "blinfun_apply (sir_vf_deriv \<beta> \<gamma> x) = sir_vf_deriv_fun \<beta> \<gamma> x"
    by (rule ext) (simp add: sir_vf_deriv_apply)
  then show ?thesis
    by (simp add: sir_vf_has_derivative_fun)
qed


text \<open>Projection @{term "(\<lambda>x. x $ i)"} is bounded linear, hence continuous on any set.\<close>

lemma vec_nth_continuous_on [continuous_intros]:
  "continuous_on s (\<lambda>x :: real^('n::finite). x $ i)"
  using continuous_on_component[OF continuous_on_id] .

lemma continuous_on_scale_component [continuous_intros]:
  "continuous_on s (\<lambda>x :: real^('n::finite). c * x $ i)"
  by (rule continuous_on_mult_left) (rule vec_nth_continuous_on)

lemma continuous_on_neg_scale_component [continuous_intros]:
  "continuous_on s (\<lambda>x :: real^('n::finite). -(c * x $ i))"
  by (intro continuous_intros)

lemma continuous_on_scale_component_diff_const [continuous_intros]:
  "continuous_on s (\<lambda>x :: real^('n::finite). c * x $ i - d)"
  by (intro continuous_intros)

lemma continuous_on_sir_vf_deriv:
  "continuous_on UNIV (sir_vf_deriv \<beta> \<gamma>)"
proof (rule continuous_on_blinfun_componentwise[where f="sir_vf_deriv \<beta> \<gamma>" and s=UNIV])
  fix h :: "real^3"
  assume "h \<in> Basis"
  have eq: "(\<lambda>x. blinfun_apply (sir_vf_deriv \<beta> \<gamma> x) h) =
      (\<lambda>x. sir_vf_deriv_fun \<beta> \<gamma> x h)"
    by (simp add: fun_eq_iff sir_vf_deriv_apply)
  have "continuous_on UNIV (\<lambda>x. sir_vf_deriv_fun \<beta> \<gamma> x h)"
    unfolding sir_vf_deriv_fun_def
  proof (intro continuous_on_vec_lambda)
    fix i :: 3
    show "continuous_on UNIV
      (\<lambda>x. if i = 1 then - \<beta> * (x $ 1 * h $ 2 + h $ 1 * x $ 2)
            else if i = 2 then \<beta> * (x $ 1 * h $ 2 + h $ 1 * x $ 2) - \<gamma> * h $ 2
            else \<gamma> * h $ 2)"
    proof (cases "i = 1")
      case True
      then show ?thesis
        by simp (intro continuous_intros)
    next
      case not1: False
      show ?thesis
      proof (cases "i = 2")
        case True
        then show ?thesis
          by simp (intro continuous_intros)
      next
        case not2: False
        then show ?thesis
          using not1 by simp
      qed
    qed
  qed
  then show "continuous_on UNIV (\<lambda>x. blinfun_apply (sir_vf_deriv \<beta> \<gamma> x) h)"
    by (subst eq)
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
  have x0_in: "x0 \<in> (UNIV :: (real^3) set)" by simp
  from sir_c1.flow_solves_ode[OF UNIV_I x0_in]
  have "(sir_c1.flow0 \<beta> \<gamma> x0 solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>))
      (sir_c1.existence_ivl0 \<beta> \<gamma> x0) UNIV"
    by simp
  then show ?thesis
    using solves_odeD by blast
qed

lemma sir_flow_solves_ode':
  "(sir_c1.flow0 \<beta> \<gamma> x0 solves_ode (\<lambda>_. sir_vf \<beta> \<gamma>))
   (sir_c1.existence_ivl0 \<beta> \<gamma> x0) UNIV"
proof -
  have "x0 \<in> (UNIV :: (real^3) set)" by simp
  from sir_c1.flow_solves_ode[OF UNIV_I this] show ?thesis by simp
qed

lemma sir_segment_subset:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  shows "closed_segment 0 t \<subseteq> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  by (rule sir_c1.closed_segment_subset_existence_ivl[OF assms])

lemma sir_ivl_subset:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" "0 \<le> t"
  shows "{0..t} \<subseteq> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  using sir_segment_subset[OF assms(1)] assms(2)
  by (simp add: closed_segment_eq_real_ivl)

lemma sir_ivl_mem:
  assumes "t \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0" "0 \<le> s" "s \<le> t"
  shows "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
  using sir_ivl_subset[OF assms(1)] assms(2,3) by auto

lemma sir_flow_continuous_on:
  "continuous_on (sir_c1.existence_ivl0 \<beta> \<gamma> x0) (sir_c1.flow0 \<beta> \<gamma> x0)"
  by (rule vderiv_on_continuous_on[OF sir_flow_solves_ode])

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
  let ?seg = "closed_segment 0 t"
  let ?fl = "sir_c1.flow0 \<beta> \<gamma> x0"
  let ?total = "\<lambda>x :: real^3. x$1 + x$2 + x$3"
  let ?g = "\<lambda>s. ?total (?fl s)"
  have seg_subset: "?seg \<subseteq> ?E"
    by (rule sir_segment_subset[OF assms])
  have const: "\<exists>c. \<forall>s\<in>?seg. ?g s = c"
  proof (rule has_derivative_zero_constant)
    show "convex ?seg"
      by simp
  next
    fix s assume s_seg: "s \<in> ?seg"
    then have s_E: "s \<in> ?E"
      using seg_subset by auto
    have flow_vd: "(?fl has_vderiv_on (\<lambda>s. sir_vf \<beta> \<gamma> (?fl s))) ?E"
      by (rule sir_flow_solves_ode)
    have hvd_E: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s)) (at s within ?E)"
      using flow_vd s_E unfolding has_vderiv_on_def by blast
    have hvd_seg: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s)) (at s within ?seg)"
      using hvd_E seg_subset
      by (auto simp: has_vector_derivative_def intro: has_derivative_subset)
    have "(?g has_vector_derivative ?total (sir_vf \<beta> \<gamma> (?fl s))) (at s within ?seg)"
      using bounded_linear.has_vector_derivative[OF bounded_linear_sir_total hvd_seg] .
    then have "(?g has_vector_derivative 0) (at s within ?seg)"
      by (simp add: sir_vf_sum_zero)
    then show "(?g has_derivative (\<lambda>h. 0)) (at s within ?seg)"
      by (simp add: has_vector_derivative_def)
  qed
  then obtain c where c: "\<And>s. s \<in> ?seg \<Longrightarrow> ?g s = c"
    by blast
  have "?g t = ?g 0"
    using c[of t] c[of 0] by simp
  then show ?thesis
    by (simp add: sir_flow_initial)
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
  have hvd_within: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s))
      (at s within sir_c1.existence_ivl0 \<beta> \<gamma> x0)"
    using flow_vd assms unfolding has_vderiv_on_def by blast
  have hvd: "(?fl has_vector_derivative sir_vf \<beta> \<gamma> (?fl s)) (at s)"
    using hvd_within by (simp add: at_within_open[OF assms open_E])
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
    by (rule sir_ivl_subset[OF assms])
  show ?thesis
    by (rule continuous_on_subset[OF continuous_on_component[OF sir_flow_continuous_on] seg])
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
      using sir_ivl_mem[OF t_in _ _] that by auto
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
  proof (rule linear_ode_nonneg[where a=0 and b=t and X="?S" and f="?f" and t=t])
    show "0 < t" by fact
    show "continuous_on {0..t} ?f" by fact
    show "\<And>s. s \<in> {0..t} \<Longrightarrow> (?S has_real_derivative ?f s * ?S s) (at s)"
      by (rule S_ode)
    show "t \<in> {0..t}" using \<open>0 < t\<close> by simp
    show "0 \<le> ?S 0" using nonneg(1) by simp
  qed
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
      using sir_ivl_mem[OF t_in _ _] that by auto
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
  proof (rule linear_ode_nonneg[where a=0 and b=t and X="?I_comp" and f="?f" and t=t])
    show "0 < t" by fact
    show "continuous_on {0..t} ?f" by fact
    show "\<And>s. s \<in> {0..t} \<Longrightarrow> (?I_comp has_real_derivative ?f s * ?I_comp s) (at s)"
      by (rule I_ode)
    show "t \<in> {0..t}" using \<open>0 < t\<close> by simp
    show "0 \<le> ?I_comp 0" using nonneg(2) by simp
  qed
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
  let ?R = "\<lambda>s. ?fl s $ 3"
  let ?g = "\<lambda>s. \<gamma> * (?fl s $ 2)"
  have R_deriv: "\<And>s. s \<in> {0..t} \<Longrightarrow>
    (?R has_real_derivative ?g s) (at s)"
  proof -
    fix s assume "s \<in> {0..t}"
    then have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_ivl_mem[OF t_in] by auto
    have "((\<lambda>t. ?fl t $ 3) has_real_derivative (sir_vf \<beta> \<gamma> (?fl s)) $ 3) (at s)"
      by (rule sir_flow_component_deriv[OF s_in])
    then show "(?R has_real_derivative ?g s) (at s)"
      by (simp add: sir_vf_components)
  qed
  have g_nonneg: "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 \<le> ?g s"
  proof -
    fix s assume "s \<in> {0..t}"
    then have s_in: "s \<in> sir_c1.existence_ivl0 \<beta> \<gamma> x0"
      using sir_ivl_mem[OF t_in] by auto
    have "0 \<le> s" using \<open>s \<in> {0..t}\<close> by auto
    then show "0 \<le> \<gamma> * (?fl s $ 2)"
      using sir_flow_nonneg_I[OF assms(1-5) s_in] assms(2) by auto
  qed
  show ?thesis
  proof (rule nonneg_deriv_nonneg[where a=0 and b=t and X="?R" and g="?g" and t=t])
    show "0 < t" by fact
    show "\<And>s. s \<in> {0..t} \<Longrightarrow> (?R has_real_derivative ?g s) (at s)"
      by (rule R_deriv)
    show "\<And>s. s \<in> {0..t} \<Longrightarrow> 0 \<le> ?g s"
      by (rule g_nonneg)
    show "t \<in> {0..t}" using \<open>0 < t\<close> by simp
    show "0 \<le> ?R 0" using nonneg(3) by simp
  qed
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
  let ?box = "{0..(\<chi> i. N)} :: (real^3) set"
  let ?sum = "{x :: real^3. x$1 + x$2 + x$3 = N}"
  have simplex_eq: "sir_simplex N = ?box \<inter> ?sum"
  proof (rule equalityI; rule subsetI)
    fix x :: "real^3"
    assume "x \<in> sir_simplex N"
    then have h: "x$1 \<ge> 0" "x$2 \<ge> 0" "x$3 \<ge> 0" "x$1 + x$2 + x$3 = N"
      unfolding sir_simplex_def by auto
    have coords: "\<And>i :: 3. 0 \<le> x$i \<and> x$i \<le> N"
    proof -
      fix i :: 3
      have "i = 1 \<or> i = 2 \<or> i = 3"
        using exhaust_3[of i] by auto
      then show "0 \<le> x$i \<and> x$i \<le> N"
        using h by auto
    qed
    show "x \<in> ?box \<inter> ?sum"
      using h coords by (simp add: less_eq_vec_def)
  next
    fix x :: "real^3"
    assume "x \<in> ?box \<inter> ?sum"
    then show "x \<in> sir_simplex N"
      unfolding sir_simplex_def by (simp add: less_eq_vec_def)
  qed
  have compact_box: "compact ?box"
    by simp
  have closed_sum: "closed ?sum"
    by (intro closed_Collect_eq continuous_intros)
  have "compact (?box \<inter> ?sum)"
    by (rule compact_Int_closed[OF compact_box closed_sum])
  then show ?thesis
    by (simp add: simplex_eq)
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
  satisfy the scalar SIR ODEs, giving access to @{locale SIR_solution}
  results under the @{text SIR_ODE} assumptions.
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
  Bridge: under the @{locale SIR_ODE} assumptions and for any interval
  $[0, b]$ with $b > 0$, we get a valid @{locale SIR_solution}
  interpretation for the constructed flow.
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
    using sir_ivl_subset global_existence[of b] assms(1)
    by auto
  have y_vderiv: "(y has_vderiv_on (\<lambda>s. sir_vf \<beta> \<gamma> (y s))) {0..b}"
    unfolding has_vderiv_on_def
  proof
    fix s assume s_in: "s \<in> {0..b}"
    have S_at: "(S' has_derivative (*) (- \<beta> * S' s * I' s)) (at s)"
      using ode_S'[OF s_in] unfolding has_field_derivative_def .
    have S_hd: "(S' has_derivative (\<lambda>h. h * (- \<beta> * S' s * I' s))) (at s within {0..b})"
    proof (rule has_derivative_eq_rhs)
      show "(S' has_derivative (*) (- \<beta> * S' s * I' s)) (at s within {0..b})"
        by (rule has_derivative_at_withinI[OF S_at])
      show "(*) (- \<beta> * S' s * I' s) = (\<lambda>h. h * (- \<beta> * S' s * I' s))"
        by (simp add: fun_eq_iff mult.commute)
    qed
    have I_at: "(I' has_derivative (*) (\<beta> * S' s * I' s - \<gamma> * I' s)) (at s)"
      using ode_I'[OF s_in] unfolding has_field_derivative_def .
    have I_hd: "(I' has_derivative (\<lambda>h. h * (\<beta> * S' s * I' s - \<gamma> * I' s))) (at s within {0..b})"
    proof (rule has_derivative_eq_rhs)
      show "(I' has_derivative (*) (\<beta> * S' s * I' s - \<gamma> * I' s)) (at s within {0..b})"
        by (rule has_derivative_at_withinI[OF I_at])
      show "(*) (\<beta> * S' s * I' s - \<gamma> * I' s) =
        (\<lambda>h. h * (\<beta> * S' s * I' s - \<gamma> * I' s))"
        by (simp add: fun_eq_iff mult.commute)
    qed
    have R_at: "(R' has_derivative (*) (\<gamma> * I' s)) (at s)"
      using ode_R'[OF s_in] unfolding has_field_derivative_def .
    have R_hd: "(R' has_derivative (\<lambda>h. h * (\<gamma> * I' s))) (at s within {0..b})"
    proof (rule has_derivative_eq_rhs)
      show "(R' has_derivative (*) (\<gamma> * I' s)) (at s within {0..b})"
        by (rule has_derivative_at_withinI[OF R_at])
      show "(*) (\<gamma> * I' s) = (\<lambda>h. h * (\<gamma> * I' s))"
        by (simp add: fun_eq_iff mult.commute)
    qed
    have y_repr: "y = (\<lambda>u. S' u *\<^sub>R axis (1::3) (1::real) +
        I' u *\<^sub>R axis (2::3) 1 + R' u *\<^sub>R axis (3::3) 1)"
    proof (rule ext)
      fix u
      show "y u = S' u *\<^sub>R axis (1::3) (1::real) +
          I' u *\<^sub>R axis (2::3) 1 + R' u *\<^sub>R axis (3::3) 1"
        apply (simp add: y_def vec_eq_iff axis_def)
        using exhaust_3 by blast
    qed
    have y_deriv_raw:
      "(y has_derivative
        (\<lambda>h :: real. (h * (- \<beta> * S' s * I' s)) *\<^sub>R axis (1::3) (1::real) +
             (h * (\<beta> * S' s * I' s - \<gamma> * I' s)) *\<^sub>R axis (2::3) 1 +
             (h * (\<gamma> * I' s)) *\<^sub>R axis (3::3) 1)) (at s within {0..b})"
      unfolding y_repr
      by (intro derivative_intros S_hd I_hd R_hd)
    have "(y has_derivative (\<lambda>h. h *\<^sub>R sir_vf \<beta> \<gamma> (y s))) (at s within {0..b})"
    proof (rule has_derivative_eq_rhs[OF y_deriv_raw])
      show "(\<lambda>h :: real. (h * (- \<beta> * S' s * I' s)) *\<^sub>R axis (1::3) (1::real) +
             (h * (\<beta> * S' s * I' s - \<gamma> * I' s)) *\<^sub>R axis (2::3) 1 +
             (h * (\<gamma> * I' s)) *\<^sub>R axis (3::3) 1) =
        (\<lambda>h. h *\<^sub>R sir_vf \<beta> \<gamma> (y s))"
        apply (simp add: fun_eq_iff y_def sir_vf_def vec_eq_iff axis_def algebra_simps)
        using exhaust_3 by blast
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
