import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Base cardinality of every admitted successor of a binary shrinking move -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking PhysicalShrink
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

private theorem base_degree {d l D D' rem : ℕ} {A : State d l} (e : D=D') (R : Move F A D rem)
    {v : ℕ} (h : ∀ a,Fintype.card (R.next a).Base=v) :
    ∀ a,Fintype.card ((e ▸ R : Move F A D' rem).next a).Base=v := by cases e; exact h

private theorem base_input {d l l' D rem tags : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D rem)
    (h : ∀ a,Fintype.card (R.next a).Base=Fintype.card (e ▸ A : State d l').Base*2^tags) :
    ∀ a,Fintype.card ((Move.recastInputLanes e A R).next a).Base=Fintype.card A.Base*2^tags := by
  cases e
  exact h

set_option maxRecDepth 8192 in
private theorem shrinkMove_next_base {d lanes rem h t D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord h × BitWord t × BitWord rem)
    (P : PackingData A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^t) (code : Arc A.Base (BitWord h) (BitWord t) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    ∀ a,Fintype.card ((shrinkMove T A u P agree good hd hD small tagSize code order).next a).Base =
      Fintype.card A.Base*2^t := by
  unfold shrinkMove
  apply base_degree
  intro a
  change Fintype.card (A.Base × BitWord t) = _
  simp [BitWord]

theorem shrinkBinary_next_base (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    ∀ a,Fintype.card ((shrinkBinary T s D rem hD small A).next a).Base =
      Fintype.card A.Base*2^(tagBits (2^s)) := by
  unfold shrinkBinary
  apply base_input
  unfold shrinkRaw
  apply shrinkMove_next_base

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
