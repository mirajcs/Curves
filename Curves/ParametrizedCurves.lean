import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

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
  /-- α is differentiable on the open interval (a, b) -/
  differentiableOn : DifferentiableOn ℝ toFun (Set.Ioo a b)

/-- 
The Helix α(t) = (r cos t, r sin t, h t) is a parametrized differentiable curve on any open interval (left, right)
-/

noncomputable example (r h left right : ℝ) (hrl : left < right) : ParametrizedDifferentiableCurve where
  a := left
  b := right
  hab := hrl
  toFun t :=
    (r * Real.cos t) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (r * Real.sin t) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    (h * t)          • EuclideanSpace.basisFun (Fin 3) ℝ 2
  differentiableOn := by
    apply Differentiable.differentiableOn
    exact ((((differentiable_const r).mul Real.differentiable_cos).smul_const _).add
        (((differentiable_const r).mul Real.differentiable_sin).smul_const _)).add
        (((differentiable_const h).mul differentiable_id).smul_const _)
