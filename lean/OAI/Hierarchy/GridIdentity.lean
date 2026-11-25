import OAI.Hierarchy.GridDiagonal
import OAI.Hierarchy.GridLens
import OAI.Hierarchy.GraphWireClass
import OAI.Hierarchy.WireProductPrice

namespace OAI
/-! # The exact benchmark and the selector scale on the exterior foci -/

namespace Hierarchy.GridDiagonal

open LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators Classical

variable {F : Type*} [Field F] {E : Type} [Fintype E] [Nonempty E] {k : ℕ}

noncomputable def focus (R : ℝ) (j : Fin k × Bool) : EuclideanSpace ℝ (Fin k) :=
  GridLens.point j.1 0 (if j.2 then R else -R)

theorem focus_injective {R : ℝ} (hR : 0 < R) : Function.Injective (focus (k:=k) R) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ h
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin k) => z i) h
  have ij : i=j := by
    by_contra ne
    cases s <;> cases t <;> simp [focus,ne] at hi <;> linarith
  subst j
  have sign : (if s then R else -R) = (if t then R else -R) := by
    simpa only [focus, GridLens.point_apply, ite_eq_left rfl, ite_true] using hi
  have side : s = t := by
    cases s <;> cases t
    · rfl
    · change -R = R at sign
      exfalso
      linarith
    · change R = -R at sign
      exfalso
      linarith
    · rfl
  rw [side]

/-- The identity has the price of one complete segment per rail, including
when distinct rails share both foci. -/
theorem identity_price (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (R : ℝ) (hR : 0 ≤ R) (dir : E → Fin k) :
    P.price (raw (identity F)) (fun u : Ends E => focus R (dir u.1,u.2)) =
      2 * R * Fintype.card E := by
  classical
  have wireClass : ofRaw (raw (identity F)) = ofRaw (equalityWireRaw E F 2) := by
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (fun _ => finTwoEquiv.symm)
    intro x
    change (Ends E → Bool) at x
    have both : (∀ i : E, x (i,false) = x (i,true)) ↔
        ∀ i : E, finTwoEquiv.symm (x (i,false)) = finTwoEquiv.symm (x (i,true)) :=
      ⟨fun h i => congrArg finTwoEquiv.symm (h i), fun h i => finTwoEquiv.symm.injective (h i)⟩
    have value : (if ∀ i : E, x (i,false) = x (i,true) then (1:F) else 0) =
        (if ∀ i : E, finTwoEquiv.symm (x (i,false)) = finTwoEquiv.symm (x (i,true)) then 1 else 0) := by
      by_cases hit : ∀ i : E, x (i,false) = x (i,true)
      · rw [ite_eq_left hit, ite_eq_left (both.mp hit)]
      · rw [ite_eq_right hit, ite_eq_right (mt both.mpr hit)]
    simp [raw,identity,equalityWireRaw,Fintype.prod_boole]
    exact value
  have wires := WirePrice.wires P (fun u : Ends E => focus R (dir u.1,u.2))
    (fun i : E => (i,false)) (fun i : E => (i,true)) 2 (by decide)
    (raw (identity F)) (wireClass.trans (ofRaw_equalityWireRaw E F 2))
  rw [wires]
  have eqn (e : E) : dist (focus R (dir e,false)) (focus R (dir e,true)) = 2*R := by
    simpa [focus,two_mul] using GridLens.dist_along (dir e) 0 (-R) R (by linarith)
  simp [eqn, mul_comm]

/-- Collapsing the binary diagonal to the origin costs one radius per focus. -/
theorem focus_scale (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (R : ℝ) (hR : 0 ≤ R) :
    P.price (Raw.diagonal (Fin k × Bool) F (Fin 2)) (focus R) ≤ 2 * k * R := by
  let D := Raw.diagonal (Fin k × Bool) F (Fin 2)
  have h := P.transport D (focus R) (fun _ => 0)
  rw [P.collapsed,Real.dist_eq,sub_zero] at h
  have d0 (j : Fin k × Bool) : dist (focus R j) 0 = R := by
    have center : (0 : EuclideanSpace ℝ (Fin k)) = GridLens.point j.1 0 0 := by
      ext i
      simp
    rw [center]
    rcases j with ⟨j,s⟩
    cases s
    · simpa [focus] using GridLens.dist_along j 0 (-R) 0 (by linarith)
    · rw [dist_comm]
      simpa [focus] using GridLens.dist_along j 0 0 R hR
  have dim (j : Fin k × Bool) : Fintype.card (D.Leg j) = 2 :=
    (Fintype.card_congr (show D.Leg j ≃ Fin 2 from Equiv.refl _)).trans (Fintype.card_fin 2)
  refine (le_abs_self _).trans (h.trans ?_)
  simp only [d0,dim,Nat.cast_ofNat,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2),
    mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  rw [mul_comm (k : ℝ) 2]

end Hierarchy.GridDiagonal

end OAI
