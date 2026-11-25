import OAI.ThreeFlat.Diagonal.PhysicalStateEnergy
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Uniform bounds for the selected output of the physical binary shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking PhysicalShrink
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F]

/-- Additive error per square of the old position count at a fixed pair of degrees. -/
def shrinkDegreeError (T : ShrinkMotif.Table F) (d D : ℕ) : ℝ :=
  let Q : ℝ := count (c := 2*d+1) (d := d)
  (64/127)*((63/32)*(d:ℝ)^2*(3/4)*Q + (d:ℝ)^2*Q*T.error) + (D:ℝ)^2/4

/-- The source degree used by the binary pass has exponent `s`. -/
def shrinkError (T : ShrinkMotif.Table F) (s D : ℕ) : ℝ := shrinkDegreeError T (2^s) D

theorem shrinkError_nonneg (T : ShrinkMotif.Table F) (s D : ℕ) : 0 ≤ shrinkError T s D := by
  have := T.error_nonneg
  dsimp only [shrinkError,shrinkDegreeError]
  positivity

/-- Both estimates compare the actual state before and after the same selected move. -/
def Move.ShrinkEstimate {d l D rem : ℕ} {A : State d l} (R : Move F A D rem) (C : ℝ) : Prop :=
  ∀ i, (R.next i).energy ≤ (126/127:ℝ)*A.energy + C*(A.positions:ℝ)^2 ∧
    4*(R.next i).positions ≤ A.positions

private theorem shrinkEstimate_degree {d l D D' rem : ℕ} {A : State d l} (h : D=D')
    (R : Move F A D rem) (C : ℝ) (H : R.ShrinkEstimate C) :
    (h ▸ R : Move F A D' rem).ShrinkEstimate C := by
  cases h
  exact H

private theorem shrinkEstimate_lanes {d l l' D rem : ℕ} (h : l=l') (A : State d l)
    (R : Move F (h ▸ A : State d l') D rem) (C : ℝ) (H : R.ShrinkEstimate C) :
    (Move.recastInputLanes h A R).ShrinkEstimate C := by
  cases h
  exact H

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Reindex the old arcs and normalize the new numbered slots in the energy
estimate for the same histogram that constructs the successor state. -/
theorem shrinkMove_estimate {d lanes rem hbits tags D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P = changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).ShrinkEstimate (shrinkDegreeError T d D) := by
  let c := 2*d+1
  let n := parallel c d D
  let pad := padding c d D
  let D₀ := usedDegree n c d + pad
  let V := Site A.Base (BitWord tags) (BitWord rem)
  let Old := Position A.Base (BitWord hbits) (BitWord tags) (BitWord rem) c
  let Edge := Numbered A.Base (BitWord tags) (BitWord rem) D₀
  have hc : 2 ≤ c := by dsimp [c]; omega
  have degree : D₀ = D := degree_eq hc hd hD
  let : Nonempty (Fin D₀) := ⟨⟨0,degree.symm ▸ hD⟩⟩
  have hcard : (Fintype.card Edge:ℝ) = (Fintype.card V:ℝ)*(D₀:ℝ) := by
    exact_mod_cast (show Fintype.card Edge = Fintype.card V * D₀ by
      dsimp only [Edge,V,Numbered,Site]
      simp only [Fintype.card_prod,Fintype.card_fin]
      ac_rfl)
  have oldPositions : Fintype.card Old = A.positions := A.positions_reindex (StageAddress.splitSite u).symm
  have oldEnergy : (∑ z, (oldWidth A u z:ℝ)^2/(1/((Fintype.card Old:ℝ)*d))) = A.energy := by
    rw [oldPositions]
    exact A.energy_reindex (StageAddress.splitEdge u).symm
  have shrinkPositions : 4*Fintype.card V ≤ A.positions := by
    rw [←oldPositions,show Fintype.card Old = Fintype.card V*(2^c*d) from position_count P]
    rw [Nat.mul_comm 4]
    apply Nat.mul_le_mul_left
    have power : 4 ≤ 2^c := Nat.pow_le_pow_right (by decide : 0<2) hc
    exact power.trans (Nat.le_mul_of_pos_right _ hd)
  unfold shrinkMove
  apply shrinkEstimate_degree
  intro i
  let terms := shrinkBranches T A u P hd code
  let x : terms := (Fintype.equivFin terms).symm i
  have h := PhysicalShrink.bound T P (oldWidth A u) code hc hd hD small binary_neg good order
    (Fintype.card_pos : 0<Fintype.card V) x
  dsimp only at h
  rw [hcard,oldEnergy,oldPositions] at h
  exact ⟨h,shrinkPositions⟩

theorem shrinkRaw_estimate (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small A).ShrinkEstimate (shrinkError T s D) := by
  unfold shrinkRaw
  apply shrinkMove_estimate

theorem shrinkBinary_estimate (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    (shrinkBinary T s D rem hD small A).ShrinkEstimate (shrinkError T s D) := by
  unfold shrinkBinary
  apply shrinkEstimate_lanes
  exact shrinkRaw_estimate T s D rem hD small _

theorem shrinkBinary_energy (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) (i) :
    ((shrinkBinary T s D rem hD small A).next i).energy ≤
      (126/127:ℝ)*A.energy + shrinkError T s D*(A.positions:ℝ)^2 :=
  (shrinkBinary_estimate T s D rem hD small A i).1

theorem shrinkBinary_positions (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) (i) :
    4*((shrinkBinary T s D rem hD small A).next i).positions ≤ A.positions :=
  (shrinkBinary_estimate T s D rem hD small A i).2

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
