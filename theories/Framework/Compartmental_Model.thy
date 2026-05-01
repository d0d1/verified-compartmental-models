(*
  Compartmental_Model.thy — Reusable framework for compartmental ODE models.

  Provides the fundamental conservation theorem: if the sum of derivatives
  of compartments is zero at every time point, then the total is constant.

  License: BSD-3-Clause
*)

theory Compartmental_Model
  imports "HOL-Analysis.Analysis"
begin

section \<open>Compartmental ODE Framework\<close>

text \<open>
  A compartmental model partitions a population into compartments whose
  values evolve according to ODEs. The central structural property is
  \emph{conservation}: transitions move population between compartments
  without creating or destroying it, so the total is constant.

  We prove this from the assumption that the sum of all derivatives is
  identically zero on a time interval.
\<close>

subsection \<open>Three-Compartment Conservation\<close>

text \<open>
  The following theorem applies to any system of three differentiable
  functions whose derivative sum is zero on a closed interval.
  This covers classical three-compartment models (SIR, SIS, etc.).
\<close>

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
    have "((\<lambda>x. f x + g x + h x) has_real_derivative (f' s + g' s + h' s)) (at s)"
      using df[OF hs] dg[OF hs] dh[OF hs] by (auto intro!: derivative_intros)
    moreover have "f' s + g' s + h' s = 0" by (rule zero_sum[OF hs])
    ultimately show "DERIV N s :> 0" unfolding N_def by simp
  qed
  have cont: "continuous_on {a..b} N"
  proof (rule DERIV_atLeastAtMost_imp_continuous_on)
    fix s assume "a \<le> s" "s \<le> b"
    then have "s \<in> {a..b}" by auto
    from N_deriv[OF this] show "\<exists>y. DERIV N s :> y" by blast
  qed
  have "N t = N a"
  proof (rule DERIV_isconst2[OF ab cont])
    fix s assume "a < s" "s < b"
    then have "s \<in> {a..b}" by auto
    then show "DERIV N s :> 0" by (rule N_deriv)
  next
    from t_in show "a \<le> t" by auto
    from t_in show "t \<le> b" by auto
  qed
  then show ?thesis unfolding N_def .
qed

subsection \<open>Monotonicity from Sign of Derivative\<close>

text \<open>
  These are convenience wrappers around the standard MVT-based results.
  They express monotonicity in a form directly applicable to compartmental
  models where we know the sign of the derivative from the ODE structure.
\<close>

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

end
