import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-- ℝ³ as the standard 3-dimensional Euclidean space -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/--
A parametrized differentiable curve is a differentiable map α : I → ℝ³
of an open interval I = (a, b) of the real line ℝ into ℝ³.

Reference: Do Carmo, *Differential Geometry of Curves & Surfaces*, §1-2.
-/
structure ParametrizedDifferentiableCurve where
  /-- Left endpoint of the open interval -/
  a : ℝ
  /-- Right endpoint of the open interval -/
  b : ℝ
  /-- The interval is non-degenerate -/
  hab : a < b
  /-- The curve map α : ℝ → ℝ³ (evaluated on (a, b)) -/
  toFun : ℝ → ℝ³
  /-- α is smooth (C^∞) on the open interval (a, b) -/
  contDiffOn : ContDiffOn ℝ ⊤ toFun (Set.Ioo a b)

/-- 
  A parametrized diffirentiable curve α: I → ℝ³ is said to be regular if α'(t) ≠ 0 for all t ∈ I. 
-/
def regularCurve (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, deriv α.toFun t ≠ 0

#check crossProduct 

/-- The arc length of α from a to t: s(t) = ∫_a^t ‖α'(u)‖ du -/
noncomputable def arcLength (α : ParametrizedDifferentiableCurve) (t : ℝ) : ℝ :=
  ∫ u in α.a..t, ‖deriv α.toFun u‖

/-- α is parametrized by arc length if ‖α'(t)‖ = 1 for all t ∈ (a, b) -/
def isArcLengthParametrized (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, ‖deriv α.toFun t‖ = 1

/-- Let α: I → ℝ³ be a curve parametrized by arc length s ∈ I. The number ‖α''(s)‖ = κ(s) is called the curvature of α at s. -/
noncomputable def Curvature (α : ParametrizedDifferentiableCurve) (t : ℝ) : ℝ :=
  ‖deriv (deriv α.toFun) t‖
