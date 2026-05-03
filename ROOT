session VCM_Base = Ordinary_Differential_Equations +
  description \<open>
    Stable base theories for verified compartmental models.
    Includes the reusable framework, SIR locale definitions, and all
    proven properties (forward invariance, conservation, monotonicity,
    threshold, peak, phase plane, simplex invariance).
    Build once with -b and cache as a heap image.
  \<close>
  options [timeout = 14400, document = false]
  directories
    "theories/Framework"
    "theories/SIR"
  theories
    SIR_Forward_Invariance
    SIR_Conservation
    SIR_Monotonicity
    SIR_Threshold
    SIR_Peak
    SIR_Phase_Plane
    SIR_Invariant

session Verified_Compartmental_Models in work = VCM_Base +
  description \<open>
    Active development session: existence/uniqueness proofs and main entry point.
    Extends VCM_Base with SIR_Existence (Picard-Lindelöf) and SIR_Main.
    Iterative builds should be fast after VCM_Base is cached.
  \<close>
  options [timeout = 7200, document = false]
  theories
    SIR_Existence
    SIR_Main
  document_files (in "../document")
    "root.tex"
    "root.bib"

session VCM_Minimal_Diag in work_diag = VCM_Base +
  description \<open>
    Diagnostic-only session for measuring minimal child-theory startup over VCM_Base.
  \<close>
  options [timeout = 7200, document = false, quick_and_dirty]
  theories
    SIR_Minimal_Diag
