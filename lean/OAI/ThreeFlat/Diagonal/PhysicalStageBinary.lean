import OAI.ThreeFlat.Diagonal.PhysicalRunRecasts
import OAI.ThreeFlat.Diagonal.PhysicalStageShrink
import OAI.ThreeFlat.Diagonal.PhysicalStageRefresh
import OAI.ThreeFlat.Diagonal.CompressorScanCost
import OAI.ThreeFlat.Diagonal.CompressorEdgeKey
import OAI.ThreeFlat.Diagonal.CompressorDemandOrdinal

namespace OAI
/-! # The two physical passes on a binary lane array, with their actual integer orderings -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking PhysicalShrink
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F]

def shrinkCharge (s : ℕ) := (2*(2^s)+1) + (s + CompressorPacking.tagBits (2^s))

private def finNat {a : ℕ} : Fin a ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩

/-- The deterministic greedy scan fixes old colors and offsets; mixed-radix old and rooted
edge ordinals fix all tie-breaking. No data remains to choose after the old state and the
fixed table are given. -/
def shrinkRaw (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) : Move F A D rem := by
  let d := 2^s
  let c := 2*d+1
  let t := CompressorPacking.tagBits d
  let P := Ordered.binaryPacking A.order.symm A.graph
  let u := laneSplit c s t rem
  have agree : StageAddress.packedGraph P=changeLanes A.graph u := rfl
  have hd : 0<d := Nat.two_pow_pos _
  have tagSize : 1<2^t := by
    have ht := CompressorPacking.tagBits_fit d
    rw [show Fintype.card (BitWord t) = 2^t by simp [BitWord]] at ht
    have : 1 ≤ 2*d*((d+1)+(d+1)^2) := by
      exact Nat.mul_pos (Nat.mul_pos (by decide : 0<2) hd) (by omega)
    omega
  let ord : A.Base ↪ ℕ := A.order.toEmbedding.trans finNat
  let code := demandOrdinal P ord (Native.tagOrdinal t).toEmbedding (Native.tagOrdinal rem).toEmbedding
  let n := parallel c d D
  let p := ∑ i : Fin 4,n i
  let root := edgeOrder P ord (Native.tagOrdinal t).toEmbedding n p
    (fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  exact shrinkMove T A u P agree (Ordered.binaryPacking_conditions A.order.symm A.graph) hd hD small tagSize code root

/-- Run a shrink when the total lane budget is supplied as an overhead plus the residual length. -/
def shrinkBinary (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) : Move F A D rem := by
  have h : shrinkCharge s+rem=(2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)) := by
    simp [shrinkCharge,Nat.add_assoc]
  exact Move.recastInputLanes h A (shrinkRaw T s D rem hD small _)

/-- Use the low contiguous degree-index bits as the refresh ports. -/
def refreshBinary {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ) : Move F A (1+h+pad) rem :=
  refreshMove T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows zero conn

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
