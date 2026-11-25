import OAI.ThreeFlat.Diagonal.CompressorIncidentRows
import OAI.ThreeFlat.Diagonal.ShrinkChoiceNative
import OAI.ThreeFlat.Diagonal.ShrinkCrossings

namespace OAI
/-! # Trace incidence columns at the stored histogram and tile-choice addresses -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement MotifIntegerChoice RefreshDemandRows
open scoped Fin.NatCast Fin.CommRing Classical
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w t l N k : ℕ}
variable {S : Graph.Stage} (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (b : B ≃ Fin N) (ptr : F) (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
variable (hc : 2≤S.colors) (K : ℕ) (lay : Bool) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
variable (z : P.Motif)
local notation "V" => Formula.value data mem vs
local notation "f" => atField (Demand.formulaOps 1) ptr
local notation "D" => descriptor P b ptr data mem vs hc K lay s z
local notation "i" => Fin.val (denseMotifRow P b (tagOrdinal t) (tagOrdinal l) hc z)
local notation "motifKey" => Demand.key P (baseNat b) (Subtype.val z)

omit [Fintype B] [Fintype H] in
theorem descriptor_selected (counts choices : ℕ) (bases : Fin (k+1) → Fin 2 → ℕ)
    (size : Fin (k+1) → ℕ) (demand : Fin 2 → ℕ)
    (ct : V (f countTable)=(counts:Word w)) (ch : V (f choiceTable)=(choices:Word w))
    (span : choices+3*i+1<2^w) (stored : ∀ j : Fin 3,
      mem (choices+3*i+j.val)=(ShrinkStageNav.descriptor bases size demand j:Word w)) :
    D = fun j => ((![(motifKey:ℕ),counts+i*K,(tileNumber demand bases).val,
      score demand bases (tileNumber demand bases),pattern (edgeBits P lay s z),pattern (partyBits P lay s z)] :
        Fin 6 → ℕ) j : Word w) := by
  have row : (V (f choiceTable)+(i:Word w)*3).val=choices+3*i := by
    rw [ch,show (3:Word w)=(3:ℕ) from rfl,←Nat.cast_mul,←Nat.cast_add,Nat.mul_comm i 3,Fin.val_cast_of_lt (by omega)]
  have second : (V (f choiceTable)+(i:Word w)*3+1).val=choices+3*i+1 := by
    rw [ch,show (3:Word w)=(3:ℕ) from rfl,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_succ,
      Nat.mul_comm i 3,Fin.val_cast_of_lt span]
  have hs : mem (choices+3*i)=(score demand bases (tileNumber demand bases):Word w) := by
    simpa [ShrinkStageNav.descriptor] using stored (0:Fin 3)
  have ht : mem (choices+3*i+1)=((tileNumber demand bases).val:Word w) := by
    simpa [ShrinkStageNav.descriptor] using stored (1:Fin 3)
  funext j
  fin_cases j <;> simp [descriptor,row,second,ct,hs,ht,Nat.cast_add,Nat.cast_mul]

omit [Fintype B] [Fintype H] in
theorem histogram_read (counts : ℕ) (hist : Fin K → ℕ) (ct : V (f countTable)=(counts:Word w))
    (span : counts+i*K<2^w) (stored : ∀ u : Fin K,mem (counts+i*K+u.val)=(hist u:Word w))
    (u : Fin K) : mem ((D 1).val+u.val)=(hist u:Word w) := by
  change mem ((V (f countTable)+(i:Word w)*(K:Word w)).val+u.val)=_
  rw [ct,←Nat.cast_mul,←Nat.cast_add,Fin.val_cast_of_lt span,stored]

omit [Fintype B] [Fintype H] in
theorem absorbed_bit (fit : 8≤w) (j : Fin 8) :
    (D 4).val.testBit j.val=decide (partySite P lay z (ShrinkMotif.supplySrc j)=s ∧
      partySite P lay z (ShrinkMotif.supplyDst j)=s) := by
  change ((pattern (edgeBits P lay s z):Word w).val).testBit j.val=_
  rw [Fin.val_cast_of_lt ((pattern_lt _).trans_le (Nat.pow_le_pow_right (by decide) fit)),pattern_bit]
  simp [edgeBits,partyBits]

omit [Fintype B] [Fintype H] in
theorem absorbed_owner (fit : 8≤w) (j : Fin 8) :
    (D 4).val.testBit j.val = decide
      (MotifKernel.wireOwner supplyGraph.tail supplyGraph.head (partySite P lay z) j=some s) := by
  rw [absorbed_bit P b ptr data mem vs hc K lay s z fit j]
  by_cases eq : partySite P lay z (ShrinkMotif.supplySrc j)=partySite P lay z (ShrinkMotif.supplyDst j)
  · simp [MotifKernel.wireOwner,supplyGraph,eq]
  · by_cases hs : partySite P lay z (ShrinkMotif.supplySrc j)=s
    · have hd : partySite P lay z (ShrinkMotif.supplyDst j)≠s := fun e => eq (hs.trans e.symm)
      simp [MotifKernel.wireOwner,supplyGraph,hs,hd,Ne.symm hd]
    · simp [MotifKernel.wireOwner,supplyGraph,eq,hs]

omit [Fintype B] [Fintype H] in
theorem party_bit (fit : 6≤w) (j : Fin 6) :
    (D 5).val.testBit j.val=decide (partySite P lay z j=s) := by
  change ((pattern (partyBits P lay s z):Word w).val).testBit j.val=_
  rw [Fin.val_cast_of_lt ((pattern_lt _).trans_le (Nat.pow_le_pow_right (by decide) fit)),pattern_bit]
  rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
