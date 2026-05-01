(*
  Compartmental_Model.thy — Reusable framework for compartmental ODE models.

  Provides:
    1. Conservation: if derivative sum is zero, total is constant
    2. Linear ODE solution formula: X' = f·X implies X(t) = X(a)·exp(∫f)
    3. Linear ODE nonnegativity: corollary of the solution formula
    4. Nonneg integral bound: X' = g ≥ 0 implies X nondecreasing
    5. Monotonicity from derivative sign

  License: BSD-3-Clause
*)

theory Compartmental_Model
  imports "HOL-Analysis.Analysis"
begin

section \<open>Compartmental ODE Framework\<close>

subsection \<open>Monotonicity from Sign of Derivative\<close>

corollary nonincreasing_from_nonpos_derivative:
  fixes f :: "real \<Rightarrow> real" and f' :: "real \<Rightarrow> real"
    and s t :: real
  assumes st: "s \<le> t"
    and df: "\<And>u. u \<in> {s..t} \<Longrightarrow> (f has_real_derivative f' u) (at u)"
    and sign: "\<And>u. u \<in> {s..t} \<Longrightarrow> f' u \<le> 0"
  shows "f t \<le> f s"
proof (rule DERIV_nonpos_imp_nonincreasing[OF st])
  fix u assume "s \<le> u" "u \<le> t"
  then have "u \<in> {s..t}" by auto
  from df[OF this] sign[OF this]
  show "\<exists>y. DERIV f u :> y \<and> y \<le> 0" by blast
qed

corollary nondecreasing_from_nonneg_derivative:
  fixes f :: "real \<Rightarrow> real" and f' :: "real \<Rightarrow> real"
    and s t :: real
  assumes st: "s \<le> t"
    and df: "\<And>u. u \<in> {s..t} \<Longrightarrow> (f has_real_derivative f' u) (at u)"
    and sign: "\<And>u. u \<in> {s..t} \<Longrightarrow> 0 \<le> f' u"
  shows "f s \<le> f t"
proof (rule DERIV_nonneg_imp_nondecreasing[OF st])
  fix u assume "s \<le> u" "u \<le> t"
  then have "u \<in> {s..t}" by auto
  from df[OF this] sign[OF this]
  show "\<exists>y. DERIV f u :> y \<and> y \<ge> 0" by blast
qed

subsection \<open>Three-Compartment Conservation\<close>

theorem three_compartment_conservation:
  fixes f g h :: "real \<Rightarrow> real"
    and f' g' h' :: "real \<Rightarrow> real"
    and a b t :: real
  assumes ab: "a < b"
    and df: "\<And>s. s \<in> {a..b} \<Longrightarrow> (f has_real_derivative f' s) (at s)"
    and dg: "\<And>s. s \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' s) (at s)"
    and dh: "\<And>s. s \<in> {a..b} \<Longrightarrow> (h has_real_derivative h' s) (at s)"
    and zero_sum: "\<And>s. s \<in> {a..b} \<Longrightarrow> f' s + g' s + h' s = 0"
    and t_in: "t \<in> {a..b}"
  shows "f t + g t + h t = f a + g a + h a"
proof -
  define N where "N \<equiv> \<lambda>s. f s + g s + h s"
  have N_deriv: "DERIV N s :> 0" if hs: "s \<in> {a..b}" for s
  proof -
    from df[OF hs] dg[OF hs] dh[OF hs]
    have "((\<lambda>x. f x + g x + h x) has_real_derivative (f' s + g' s + h' s)) (at s)"
      by (intro DERIV_add) auto
    with zero_sum[OF hs] show "DERIV N s :> 0" unfolding N_def by simp
  qed
  have cont: "continuous_on {a..b} N"
    by (rule DERIV_atLeastAtMost_imp_continuous_on)
       (use N_deriv in \<open>auto simp: atLeastAtMost_iff\<close>)
  have "N t = N a"
    by (rule DERIV_isconst2[OF ab cont])
       (use N_deriv t_in in \<open>auto simp: atLeastAtMost_iff\<close>)
  then show ?thesis unfolding N_def .
qed

subsection \<open>Linear ODE Solution Formula\<close>

text \<open>
  If $X' = f \cdot X$ with $f$ continuous on $[a,b]$, then
  $X(t) = X(a) \cdot \exp(\int_a^t f)$.
\<close>

theorem linear_ode_solution:
  fixes X :: "real \<Rightarrow> real" and f :: "real \<Rightarrow> real"
  assumes ab: "a < b"
    and cont_f: "continuous_on {a..b} f"
    and ode: "\<And>t. t \<in> {a..b} \<Longrightarrow> (X has_real_derivative (f t * X t)) (at t)"
    and t_in: "t \<in> {a..b}"
  shows "X t = X a * exp (integral {a..t} f)"
proof -
  define F where "F \<equiv> \<lambda>u. integral {a..u} f"
  define g where "g \<equiv> \<lambda>u. X u * exp (- F u)"

  have F_deriv_within: "(F has_real_derivative f u) (at u within {a..b})"
    if "u \<in> {a..b}" for u
    unfolding F_def using integral_has_real_derivative[OF cont_f that] .

  have F_deriv: "(F has_real_derivative f u) (at u)"
    if "a < u" "u < b" for u
    using F_deriv_within[of u] that by (simp add: at_within_Icc_at)

  have cont_F: "continuous_on {a..b} F"
    unfolding continuous_on_eq_continuous_within
  proof
    fix u assume u_in: "u \<in> {a..b}"
    from F_deriv_within[OF u_in]
    show "continuous (at u within {a..b}) F"
      by (rule DERIV_continuous)
  qed

  have g_deriv: "DERIV g u :> 0" if "a < u" "u < b" for u
  proof -
    have u_in: "u \<in> {a..b}" using that by auto
    have dX: "(X has_real_derivative (f u * X u)) (at u)"
      by (rule ode[OF u_in])
    have dF: "(F has_real_derivative f u) (at u)"
      by (rule F_deriv[OF that])
    have d_neg_F: "((\<lambda>u. - F u) has_real_derivative (- f u)) (at u)"
      by (rule DERIV_minus[OF dF])
    have d_exp: "((\<lambda>u. exp (- F u)) has_real_derivative (exp (- F u) * (- f u))) (at u)"
      by (rule DERIV_chain2[OF DERIV_exp d_neg_F])
    have d_prod: "((\<lambda>u. X u * exp (- F u)) has_real_derivative
           (f u * X u) * exp (- F u) + (exp (- F u) * (- f u)) * X u) (at u)"
      by (rule DERIV_mult[OF dX d_exp])
    moreover have "(f u * X u) * exp (- F u) + (exp (- F u) * (- f u)) * X u = 0"
      by (simp add: algebra_simps)
    ultimately show "DERIV g u :> 0" unfolding g_def by simp
  qed

  have cont_X: "continuous_on {a..b} X"
    by (rule DERIV_atLeastAtMost_imp_continuous_on)
       (use ode in \<open>auto simp: atLeastAtMost_iff\<close>)
  have cont_neg_F: "continuous_on {a..b} (\<lambda>u. - F u)"
    using cont_F by (rule continuous_on_minus)
  have cont_exp_neg_F: "continuous_on {a..b} (\<lambda>u. exp (- F u))"
    using cont_neg_F by (rule continuous_on_exp)
  have cont_g: "continuous_on {a..b} g"
    unfolding g_def using cont_X cont_exp_neg_F
    by (rule continuous_on_mult)

  have "g t = g a"
  proof (rule DERIV_isconst2[OF ab cont_g])
    fix u assume "a < u" "u < b"
    then show "DERIV g u :> 0" by (rule g_deriv)
  next
    from t_in show "a \<le> t" by auto
    from t_in show "t \<le> b" by auto
  qed
  moreover have "g a = X a"
  proof -
    have "F a = 0" unfolding F_def
      by (metis content_real_eq_0 has_integral_null_real integral_unique order_refl)
    then show ?thesis unfolding g_def by simp
  qed
  ultimately have eq: "X t * exp (- F t) = X a" unfolding g_def by simp
  then have "X t = X a * exp (F t)"
    using exp_gt_zero[of "- F t"]
    by (simp add: exp_minus field_simps)
  then show ?thesis unfolding F_def .
qed

corollary linear_ode_nonneg:
  fixes X :: "real \<Rightarrow> real" and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "\<And>t. t \<in> {a..b} \<Longrightarrow> (X has_real_derivative (f t * X t)) (at t)"
    and "t \<in> {a..b}"
    and "0 \<le> X a"
  shows "0 \<le> X t"
proof -
  have "X t = X a * exp (integral {a..t} f)"
    by (rule linear_ode_solution[OF assms(1-4)])
  also have "\<dots> \<ge> 0"
    using assms(5) by (intro mult_nonneg_nonneg) auto
  finally show ?thesis .
qed

corollary linear_ode_pos:
  fixes X :: "real \<Rightarrow> real" and f :: "real \<Rightarrow> real"
  assumes "a < b"
    and "continuous_on {a..b} f"
    and "\<And>t. t \<in> {a..b} \<Longrightarrow> (X has_real_derivative (f t * X t)) (at t)"
    and "t \<in> {a..b}"
    and "0 < X a"
  shows "0 < X t"
proof -
  have "X t = X a * exp (integral {a..t} f)"
    by (rule linear_ode_solution[OF assms(1-4)])
  also have "\<dots> > 0"
    using assms(5) by (intro mult_pos_pos) auto
  finally show ?thesis .
qed

subsection \<open>Nonneg Derivative Implies Nondecreasing\<close>

corollary nonneg_deriv_nonneg:
  fixes X :: "real \<Rightarrow> real" and g :: "real \<Rightarrow> real"
  assumes ab: "a < b"
    and ode: "\<And>t. t \<in> {a..b} \<Longrightarrow> (X has_real_derivative g t) (at t)"
    and nonneg_g: "\<And>t. t \<in> {a..b} \<Longrightarrow> 0 \<le> g t"
    and t_in: "t \<in> {a..b}"
    and init: "0 \<le> X a"
  shows "0 \<le> X t"
proof -
  have at: "a \<le> t" using t_in by auto
  have df: "\<And>u. u \<in> {a..t} \<Longrightarrow> (X has_real_derivative g u) (at u)"
    using ode t_in by auto
  have sg: "\<And>u. u \<in> {a..t} \<Longrightarrow> 0 \<le> g u"
    using nonneg_g t_in by auto
  have "X a \<le> X t"
    by (rule nondecreasing_from_nonneg_derivative[OF at df sg])
  with init show ?thesis by linarith
qed

end
