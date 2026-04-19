import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped InnerProductSpace

namespace Curves

/-- `ℝ³` denotes `EuclideanSpace ℝ (Fin 3)`, the standard 3-dimensional real Euclidean space. -/
scoped notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A parametrized differentiable curve is a smooth map `α : I → ℝ³` of an open interval
`I = (a, b)` of the real line into `ℝ³`.

**Reference:** Do Carmo, *Differential Geometry of Curves & Surfaces*, §1-2. -/
structure ParametrizedDifferentiableCurve where
  /-- Left endpoint `a` of the open interval `(a, b)`. -/
  a : ℝ
  /-- Right endpoint `b` of the open interval `(a, b)`. -/
  b : ℝ
  /-- The interval is non-degenerate: `a < b`. -/
  hab : a < b
  /-- The curve map `α : ℝ → ℝ³`, evaluated on `(a, b)`. -/
  toFun : ℝ → ℝ³
  /-- `α` is smooth (`C^∞`) on the open interval `(a, b)`. -/
  contDiffOn : ContDiffOn ℝ ⊤ toFun (Set.Ioo a b)

/-- A parametrized differentiable curve `α : I → ℝ³` is **regular** if `α'(t) ≠ 0`
for all `t ∈ (a, b)`. -/
def regularCurve (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, deriv α.toFun t ≠ 0

/-- The arc length of `α` measured from `α.a` to `t`, defined by `s(t) = ∫_a^t ‖α'(u)‖ du`. -/
noncomputable def arcLength (α : ParametrizedDifferentiableCurve) (t : ℝ) : ℝ :=
  ∫ u in α.a..t, ‖deriv α.toFun u‖

/-- `α` is **parametrized by arc length** if `‖α'(t)‖ = 1` for all `t ∈ (a, b)`. -/
def isArcLengthParametrized (α : ParametrizedDifferentiableCurve) : Prop :=
  ∀ t ∈ Set.Ioo α.a α.b, ‖deriv α.toFun t‖ = 1

/-- The **curvature** `κ(t) = ‖α''(t)‖` of a curve `α` parametrized by arc length. -/
noncomputable def Curvature (α : ParametrizedDifferentiableCurve) (t : ℝ) : ℝ :=
  ‖deriv (deriv α.toFun) t‖

/-- The **unit tangent vector** `T(t) = α'(t)` of a curve `α` parametrized by arc length. -/
noncomputable def curveTangent (α : ParametrizedDifferentiableCurve)
    (_h : isArcLengthParametrized α) (t : ℝ) : ℝ³ :=
  deriv α.toFun t

/-- The **principal normal vector** `N(t) = α''(t) / κ(t)` of a curve `α` parametrized by arc length. -/
noncomputable def curveNormal (α : ParametrizedDifferentiableCurve)
    (_h : isArcLengthParametrized α) (t : ℝ) : ℝ³ :=
  (1 / Curvature α t) • deriv (deriv α.toFun) t

/-- The **binormal vector** `B(t) = T(t) × N(t)` of a curve `α` parametrized by arc length. -/
noncomputable def curveBinormal (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) : ℝ³ :=
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  e.symm (crossProduct (e (curveTangent α h t)) (e (curveNormal α h t)))


/-- The **torsion** `τ(t) = ‖B'(t)‖` of a curve `α` parametrized by arc length. -/
noncomputable def Torsion (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) : ℝ :=
  ‖deriv (curveBinormal α h) t‖

/-- The **Frenet trihedron** (moving frame) at a point on a curve, consisting of the
unit tangent `T`, principal normal `N`, and binormal `B` vectors. -/
structure FrenetFrame where
  /-- Unit tangent vector `T(t) = α'(t)`. -/
  tangent  : ℝ³
  /-- Principal normal vector `N(t) = α''(t) / κ(t)`. -/
  normal   : ℝ³
  /-- Binormal vector `B(t) = T(t) × N(t)`. -/
  binormal : ℝ³

/-- The **Frenet trihedron** `{T(t), N(t), B(t)}` of a curve `α` parametrized by arc length at `t`. -/
noncomputable def frenetTrihedron (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) : FrenetFrame where
  tangent  := curveTangent α h t
  normal   := curveNormal α h t
  binormal := curveBinormal α h t

/-! ## Frenet-Serret Formulas

For a curve `α` parametrized by arc length, the derivatives of the Frenet trihedron satisfy:
- `T'(t) = κ(t) · N(t)`
- `N'(t) = -κ(t) · T(t) + τ(t) · B(t)`
- `B'(t) = -τ(t) · N(t)`
-/

/-- **Frenet formula for T**: the derivative of the unit tangent is `κ(t) • N(t)`. -/
theorem deriv_tangent (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) (hκ : Curvature α t ≠ 0) :
    deriv (curveTangent α h) t = Curvature α t • curveNormal α h t := by
  -- T'(s) = d/ds(α'(s)) = α''(s) by definition of curveTangent
  have lhs : deriv (curveTangent α h) t = deriv (deriv α.toFun) t := rfl
  -- κ(s) · N(s) = ‖α''(s)‖ · (1/‖α''(s)‖ · α''(s)) = α''(s)
  have rhs : Curvature α t • curveNormal α h t = deriv (deriv α.toFun) t := by
    simp only [curveNormal, Curvature] at hκ ⊢
    simp only [smul_smul, mul_one_div_cancel hκ, one_smul]
  rw [lhs, rhs]

private lemma dot_tangent (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) (ht : t ∈ Set.Ioo α.a α.b) :
    ⟪curveTangent α h t, curveTangent α h t⟫_ℝ = 1 := by
  simp only [curveTangent]
  have h1 : ‖deriv α.toFun t‖ = 1 := h t ht
  rw [real_inner_self_eq_norm_sq, h1, one_pow]


private lemma orthogonality_tangent_normal (α : ParametrizedDifferentiableCurve)
      (h : isArcLengthParametrized α) (t : ℝ) (ht : t ∈ Set.Ioo α.a α.b) : 
    ⟪curveTangent α h t, curveNormal α h t⟫_ℝ = 0 := by 
    simp only [curveTangent, curveNormal]
    rw [real_inner_smul_right]
    apply mul_eq_zero_of_right 
    -- T is differentiable at t (from C^∞ of α)
    have hdiff : DifferentiableAt ℝ (curveTangent α h) t := by
      -- ContDiffOn ℝ ⊤ α implies ContDiffOn ℝ 1 (deriv α) on the open interval
      have hc : ContDiffOn ℝ 1 (deriv α.toFun) (Set.Ioo α.a α.b) :=
        α.contDiffOn.deriv_of_isOpen isOpen_Ioo le_top
      exact (hc.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)

    -- Product rule: d/dt ⟪T, T⟫ = ⟪T, T'⟫ + ⟪T', T⟫  (order from HasDerivAt.inner)
    have hexp : deriv (fun s => ⟪curveTangent α h s, curveTangent α h s⟫_ℝ) t =
        ⟪curveTangent α h t, deriv (curveTangent α h) t⟫_ℝ +
        ⟪deriv (curveTangent α h) t, curveTangent α h t⟫_ℝ :=
      (HasDerivAt.inner (𝕜 := ℝ) hdiff.hasDerivAt hdiff.hasDerivAt).deriv
    -- ⟪T, T⟫ = 1 near t, so its derivative is 0
    have hzero : deriv (fun s => ⟪curveTangent α h s, curveTangent α h s⟫_ℝ) t = 0 := by
      have heq : (fun s => ⟪curveTangent α h s, curveTangent α h s⟫_ℝ) =ᶠ[nhds t] (fun _ => 1) :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (dot_tangent α h)
      rw [heq.deriv_eq, deriv_const]
    -- So ⟪T, T'⟫ + ⟪T', T⟫ = 0
    have Dh : ⟪curveTangent α h t, deriv (curveTangent α h) t⟫_ℝ +
              ⟪deriv (curveTangent α h) t, curveTangent α h t⟫_ℝ = 0 := hexp ▸ hzero
    -- By symmetry ⟪T', T⟫ = ⟪T, T'⟫, so 2⟪T, T'⟫ = 0 → ⟪T, T'⟫ = 0
    have hsymm : ⟪deriv (curveTangent α h) t, curveTangent α h t⟫_ℝ =
                 ⟪curveTangent α h t, deriv (curveTangent α h) t⟫_ℝ := real_inner_comm _ _
    have hfun : curveTangent α h = deriv α.toFun := rfl
    simp only [hfun] at Dh hsymm
    linarith [Dh, hsymm]

private lemma binormal_cross (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ)
    (ht : t ∈ Set.Ioo α.a α.b) :
    curveNormal α h t =
      let e := EuclideanSpace.equiv (Fin 3) ℝ
      e.symm (crossProduct (e (curveBinormal α h t)) (e (curveTangent α h t))) := by
  -- Let e : EuclideanSpace ℝ (Fin 3) ≃ (Fin 3 → ℝ) be the equivalence.
  set e := EuclideanSpace.equiv (Fin 3) ℝ with he
  -- Step 1: B × T = T × (N × T)
  -- B = T × N by definition, so e(B) = e(T) × e(N).
  -- Then (e(T) × e(N)) × e(T) = e(T) × (e(N) × e(T)) - e(N) × (e(T) × e(T))
  --                             = e(T) × (e(N) × e(T)) - e(N) × 0
  --                             = e(T) × (e(N) × e(T)).   (by cross_cross and cross_self)
  have heB : e (curveBinormal α h t) =
      crossProduct (e (curveTangent α h t)) (e (curveNormal α h t)) := by
    have hdef : curveBinormal α h t =
        e.symm (crossProduct (e (curveTangent α h t)) (e (curveNormal α h t))) := rfl
    rw [hdef, e.apply_symm_apply]
  have hBT : crossProduct (e (curveBinormal α h t)) (e (curveTangent α h t)) =
      crossProduct (e (curveTangent α h t))
        (crossProduct (e (curveNormal α h t)) (e (curveTangent α h t))) := by
    rw [heB, cross_cross, cross_self, map_zero, sub_zero]
  -- Step 2: T × (N × T) = (T⬝T)·N − (N⬝T)·T = 1·N − 0·T = N  (BAC-CAB)
  -- Connect e v ⬝ᵥ e w with ⟪v, w⟫_ℝ via inner_eq_star_dotProduct
  -- e v = PiLp.ofLp v definitionally (PiLp.coe_continuousLinearEquiv is rfl),
  -- so EuclideanSpace.inner_eq_star_dotProduct v w : ⟪v,w⟫_ℝ = e w ⬝ᵥ star (e v)  by rfl
  have dot_e_eq : ∀ v w : ℝ³, e v ⬝ᵥ e w = ⟪v, w⟫_ℝ := fun v w => by
    have hstar : star (e v) = e v := by ext; simp
    calc e v ⬝ᵥ e w
        = e w ⬝ᵥ e v        := dotProduct_comm _ _
      _ = e w ⬝ᵥ star (e v) := by rw [hstar]
      _ = ⟪v, w⟫_ℝ          := (EuclideanSpace.inner_eq_star_dotProduct v w).symm
  have hTT : e (curveTangent α h t) ⬝ᵥ e (curveTangent α h t) = 1 :=
    (dot_e_eq _ _).trans (dot_tangent α h t ht)
  have hNT : e (curveNormal α h t) ⬝ᵥ e (curveTangent α h t) = 0 :=
    (dot_e_eq _ _).trans ((real_inner_comm _ _).trans (orthogonality_tangent_normal α h t ht))
  have hTNT : crossProduct (e (curveTangent α h t))
      (crossProduct (e (curveNormal α h t)) (e (curveTangent α h t))) =
      e (curveNormal α h t) := by
    rw [cross_cross_eq_smul_sub_smul', hTT, hNT, one_smul, zero_smul, sub_zero]
  calc curveNormal α h t
      = e.symm (e (curveNormal α h t))            := (e.symm_apply_apply _).symm
    _ = e.symm (crossProduct (e (curveTangent α h t))
          (crossProduct (e (curveNormal α h t)) (e (curveTangent α h t)))) := by rw [hTNT]
    _ = e.symm (crossProduct (e (curveBinormal α h t)) (e (curveTangent α h t))) := by rw [← hBT]

/-- **Frenet formula for N**: the derivative of the principal normal is `-κ(t) • T(t) + τ(t) • B(t)`. -/
theorem deriv_normal (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) :
    deriv (curveNormal α h) t =
      -(Curvature α t) • curveTangent α h t + Torsion α h t • curveBinormal α h t := by
  sorry

/-- **Frenet formula for B**: the derivative of the binormal is `-τ(t) • N(t)`. -/
theorem deriv_binormal (α : ParametrizedDifferentiableCurve)
    (h : isArcLengthParametrized α) (t : ℝ) :
    deriv (curveBinormal α h) t = -(Torsion α h t) • curveNormal α h t := by
  sorry

end Curves
