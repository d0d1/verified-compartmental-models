theory SIR_Minimal_Diag
  imports
    "VCM_Base.SIR_Defs"
    "Ordinary_Differential_Equations.ODE_Analysis"
begin

ML_command \<open>
  val path = Path.explode "/home/david/repos/isabelle-projects/vcm-minimal-checkpoints.log"
  val _ = File.write path "MINIMAL_CHECKPOINT: begin\n"
\<close>

section \<open>Minimal Diagnostic Body\<close>

ML_command \<open>
  val path = Path.explode "/home/david/repos/isabelle-projects/vcm-minimal-checkpoints.log"
  val _ = File.append path "MINIMAL_CHECKPOINT: section reached\n"
\<close>

definition diag_const :: real where
  "diag_const = 0"

ML_command \<open>
  val path = Path.explode "/home/david/repos/isabelle-projects/vcm-minimal-checkpoints.log"
  val _ = File.append path "MINIMAL_CHECKPOINT: definition complete\n"
\<close>

lemma diag_const_zero: "diag_const = 0"
  unfolding diag_const_def by simp

ML_command \<open>
  val path = Path.explode "/home/david/repos/isabelle-projects/vcm-minimal-checkpoints.log"
  val _ = File.append path "MINIMAL_CHECKPOINT: lemma complete\n"
\<close>

end
