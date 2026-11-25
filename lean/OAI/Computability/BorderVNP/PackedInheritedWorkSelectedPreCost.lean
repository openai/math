import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedScanCost
import OAI.Computability.BorderVNP.PackedInheritedWorkPrep

/-! # Charging the actual grouped exterior directories and inherited subdivision gates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity Packing Packing.Inherited
open Packing.Inherited.WorkWords EnrichedOuter TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m np : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
variable {start : ℕ}

/-- The extra subdivision gates beyond the shared geometric compiler, as a polynomial
of its address length times the original epoch rectangle. -/
noncomputable def widthPreFactor := 1+fan S*32000*66^3*(2*interiors S+1)

variable {S} {P : Type} [Fintype P] {bits : P → ℕ} {T n r : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (C : Compiled bits deep budget cap (60*logWidth r n))

/-- A single copy of the original geometric pre-frame and the additional physical gates
of all of its children's work and extent directories, on the real selected rectangles. -/
theorem Compiled.widthPre_rowWork (p : WorkWords.Ports np) (base : np ≤ CoverScale.sites (Cube D) start)
    {t : ℕ} (ht : t<T) {den cut : Fin S.rounds → ℕ}
    (ranges : ∀ i : Fin S.rounds, Ranges S r n start t i (den i) (cut i)) (hL : 1 ≤ logWidth r n) :
    let A := C.atLevel t ht
    let shape := boundaryShape S start t
    (A.widthPre rfl (p.outer S start t) (boundary_fits S ranges).1).size ≤
      A.pre.size + rowWork (widthPreFactor S) (CoverScale.sites (Cube D) start) (logWidth r n) 3 shape := by
  intro A shape
  let next := before S start t 0
  let V := CoverScale.sites (Cube D) start
  let L := logWidth r n
  let w := 60*L
  let first : Fin S.rounds := ⟨0,S.rounds_pos⟩
  have fitE : next.edges ≤ 2^w :=
    (Nat.le_mul_of_pos_left _ S.positiveFanIn).trans (ranges first).words.2.2.2.2.1
  have ports : portCapacity S np t ≤ next.sites := widthPorts_le S base t 0
  have cost := widthCharge_cubic next.edges ports (boundary_fits S ranges).1 fitE rfl hL
  have raw := A.widthPre_size rfl (p.outer S start t) (boundary_fits S ranges).1
  rw [Nat.add_assoc] at raw
  have rows : next.sites+next.edges+1 ≤ (2*interiors S+1)*shape.volume V := by
    apply LE.le.trans (b := next.volume V)
    · dsimp only [Shape.volume]; omega
    · exact shape.subdivide_volume (interiors S) V
  have bump : 1 ≤ shape.volume V * L^3 := by
    have volume : 1 ≤ shape.volume V := by dsimp only [Shape.volume]; omega
    exact Nat.mul_pos volume (Nat.pow_pos hL)
  apply raw.trans
  apply Nat.add_le_add_left
  apply (Nat.add_le_add bump (Nat.mul_le_mul_left (fan S) cost)).trans
  apply (Nat.add_le_add_left (Nat.mul_le_mul_left (fan S) (Nat.mul_le_mul_right (L^3)
    (Nat.mul_le_mul_right (66^3) (Nat.mul_le_mul_left 32000 rows)))) _).trans_eq
  unfold rowWork widthPreFactor
  dsimp only [V,L]
  ring

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
