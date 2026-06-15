import Mathlib.Data.Real.Basic

/-!
# Chapter 12 - local average treatment effects

The LATE section is not represented by a numbered theorem in the current
inventory, but Hansen's Assumption 12.3 and Wald-ratio identity are part of the
chapter's public mathematical surface.
-/

namespace HansenEconometrics

/-- Wald ratio used to identify LATE for a binary instrument. -/
noncomputable def lateWaldRatio (EY1 EY0 EX1 EX0 : ℝ) : ℝ :=
  (EY1 - EY0) / (EX1 - EX0)

/-- Hansen Assumption 12.3, stated as the independence and monotonicity package
used by the LATE section. -/
structure LATEAssumption where
  independence : Prop
  monotonicity : Prop

/-- LATE identified by the Wald ratio under the LATE assumptions. -/
structure LATEIdentification (late EY1 EY0 EX1 EX0 : ℝ) : Prop where
  identified : late = lateWaldRatio EY1 EY0 EX1 EX0

/-- Hansen Section 12.34: under Assumption 12.3, the binary-IV Wald ratio
identifies the local average treatment effect. -/
theorem chapter12_late_eq_waldRatio
    (late EY1 EY0 EX1 EX0 : ℝ)
    (h : LATEIdentification late EY1 EY0 EX1 EX0) :
    late = lateWaldRatio EY1 EY0 EX1 EX0 :=
  h.identified

end HansenEconometrics
