import OAI.LinearAlgebra.FiniteFourier.PrimeAuxiliarySlice
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointDual
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointGeometry
import OAI.LinearAlgebra.FiniteFourier.PrimeRectanglePairing

/-! # Local and common coordinates on routing rectangles

Choose the ordinary paired coordinates once per label. For a free rectangle,
each source can sum along the target span inside its auxiliary axes. Each
target can sum along the annihilator inside its own auxiliary axes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open Module

section CoordinateSubspace
variable {K E A C : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup A] [Module K A] [AddCommGroup C] [Module K C]
  (e : E ≃ₗ[K] A × C) (H : Submodule K E) (he : ∀ x, x ∈ H ↔ (e x).2 = 0)

/-- Identify an actual subspace with the coordinate block representing it. -/
def endpointAxisEquiv : H ≃ₗ[K] A where
  toFun u := (e u).1
  invFun a := ⟨e.symm (a,0), (he _).mpr (by simp)⟩
  left_inv u := by
    apply Subtype.ext
    apply e.symm_apply_eq.mpr
    exact Prod.ext rfl ((he _).mp u.property).symm
  right_inv a := by simp
  map_add' x y := by simp
  map_smul' a x := by simp

/-- Replacing the first block by the actual subspace makes the embedding
of the summation subspace independent of the chosen representatives. -/
def endpointSubspaceChart : (H × C) ≃ₗ[K] E :=
  ((endpointAxisEquiv e H he).prodCongr (LinearEquiv.refl K C)).trans e.symm

@[simp] theorem endpointSubspaceChart_zero (u : H) :
    endpointSubspaceChart e H he (u, 0) = u := by
  apply e.symm_apply_eq.mpr
  exact Prod.ext rfl ((he _).mp u.property).symm

@[simp] theorem endpointSubspaceChart_apply (u : H) (c : C) :
    e (endpointSubspaceChart e H he (u,c)) = ((e u).1,c) := by
  exact e.apply_symm_apply _

end CoordinateSubspace

namespace BitRoutingGeometry

variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)

abbrev Space := Fin G.D → ZMod ℓ
abbrev AuxSpace := Fin (G.D-1) → ZMod ℓ

/-- Ordinary coordinate maps for the two halves of a label. They use the
same distinguished vector and dual lists of auxiliary axes. -/
structure LabelCharts (v : BitLabel L b) where
  first : G.Space ≃ₗ[ZMod ℓ] ZMod ℓ × G.AuxSpace
  second : G.Space ≃ₗ[ZMod ℓ] ZMod ℓ × G.AuxSpace
  coordinate (x) : (first x).1 = G.form (G.vector v) x ∧ (second x).1 = G.form (G.vector v) x
  first_vector : first (G.vector v) = (1,0)
  second_vector : second (G.vector v) = (1,0)
  pair (x y) : G.form x y = (first x).1 * (second y).1 + ∑ i, (first x).2 i * (second y).2 i

/-- These choices depend on the label alone. -/
def labelCharts (v : BitLabel L b) : G.LabelCharts v := Classical.choice <| by
  have h := exists_primeEndpointLabelCharts G.form G.nondegenerate G.symm (G.vector v)
    (G.vector_self v)
  have hdim : finrank (ZMod ℓ) (Fin G.D → ZMod ℓ) = G.D := by simp
  rw [hdim] at h
  obtain ⟨p,q,h₁,h₂,h₃,h₄⟩ := h
  exact ⟨⟨p,q,h₁,h₂,h₃,h₄⟩⟩

/-- Select the first or the second ordinary half. -/
def halfChart (v : BitLabel L b) (second : Bool) : G.Space ≃ₗ[ZMod ℓ] ZMod ℓ × G.AuxSpace :=
  if second then (G.labelCharts v).second else (G.labelCharts v).first

theorem halfChart_coordinate (v : BitLabel L b) (second : Bool) (x : G.Space) :
    (G.halfChart v second x).1 = G.form (G.vector v) x := by
  cases second
  · exact ((G.labelCharts v).coordinate x).1
  · exact ((G.labelCharts v).coordinate x).2

/-- Local input coset coordinates, with the target span in the auxiliary axes. -/
def sourceSlice (R : BitRectangle L b) (hd : ¬ℓ ∣ bitCutDistance R.1) {v : BitLabel L b}
    (hv : v ∈ bitSources R) (second : Bool) : AuxiliarySlice (G.halfChart v second) (G.targetSpan R) :=
  auxiliarySlice _ _ fun x hx =>
    (G.halfChart_coordinate v second x).trans (G.targetSpan_le_sourceKer R hd hv hx)

/-- Transposed output coset coordinates, with the annihilator in the auxiliary axes. -/
def targetSlice (R : BitRectangle L b) {w : BitLabel L b} (hw : w ∈ bitTargets R)
    (second : Bool) : AuxiliarySlice (G.halfChart w second) ((G.targetSpan R).orthogonalBilin G.form) :=
  auxiliarySlice _ _ fun x hx =>
    (G.halfChart_coordinate w second x).trans (G.orthogonal_targetSpan_le_targetKer R hw hx)

/-- Common coordinates for the source and transposed target of a rectangle. -/
structure SharedCharts (R : BitRectangle L b) where
  c : ℕ
  primal : G.Space ≃ₗ[ZMod ℓ] (Fin (finrank (ZMod ℓ) (G.targetSpan R)) → ZMod ℓ) × (Fin c → ZMod ℓ)
  dual : G.Space ≃ₗ[ZMod ℓ] (Fin (finrank (ZMod ℓ) (G.targetSpan R)) → ZMod ℓ) × (Fin c → ZMod ℓ)
  dim_eq : finrank (ZMod ℓ) (G.targetSpan R) + c = G.D
  mem_primal (x) : x ∈ G.targetSpan R ↔ (primal x).2 = 0
  mem_dual (x) : x ∈ (G.targetSpan R).orthogonalBilin G.form ↔ (dual x).1 = 0
  pair (x s) : G.form x s = (∑ i, (primal x).1 i * (dual s).1 i) + ∑ i, (primal x).2 i * (dual s).2 i

/-- A shared basis and its dual realize both partial transform blocks. -/
def sharedCharts (R : BitRectangle L b) : G.SharedCharts R := Classical.choice <| by
  obtain ⟨c,e,e',hc,hH,hP,hB⟩ :=
    exists_primeEndpointDualCharts G.form G.nondegenerate G.symm (G.targetSpan R)
  exact ⟨⟨c,e,e',by simpa using hc,hH,hP,hB⟩⟩

namespace SharedCharts
variable {G} {R : BitRectangle L b} (S : G.SharedCharts R)

/-- Common coset representatives on the source side. -/
def source : (G.targetSpan R × (Fin S.c → ZMod ℓ)) ≃ₗ[ZMod ℓ] G.Space :=
  endpointSubspaceChart S.primal _ S.mem_primal

/-- Common coset representatives on the transposed output side. -/
def target : ((G.targetSpan R).orthogonalBilin G.form ×
    (Fin (finrank (ZMod ℓ) (G.targetSpan R)) → ZMod ℓ)) ≃ₗ[ZMod ℓ] G.Space :=
  endpointSubspaceChart (S.dual.trans (LinearEquiv.prodComm _ _ _)) _ S.mem_dual

@[simp] theorem source_zero (h : G.targetSpan R) : S.source (h,0) = h :=
  endpointSubspaceChart_zero _ _ _ _

@[simp] theorem target_zero (p : (G.targetSpan R).orthogonalBilin G.form) : S.target (p,0) = p :=
  endpointSubspaceChart_zero _ _ _ _

end SharedCharts
end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
