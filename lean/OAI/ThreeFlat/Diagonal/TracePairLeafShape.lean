import OAI.ThreeFlat.Diagonal.TracePairLeaf
import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.RAM.HistoryInitialSeed

namespace OAI
/-! # Exact physical sizes of each first trace or later relay leaf -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner TraceSuffix
open RAM RAM.TraceBucketAtom
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (L : Lane (q+1)) (copies raw dict masks ids : ℕ)
set_option quotPrecheck false
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "I" => bitIndex hF hw hp base st hs hf r k fit L
local notation "ln" => (finFunctionFinEquiv L).val

theorem pairLeaf_shape (T : ℕ) (extent : 2*T≤S) (pub : ℕ→Bool) :
    let A := pairLeaf hF hw hp base st hs hf r k fit L copies T extent pub
    A.cells=(B).relays+((B).gates+(B).tags+(B).lowRows*(B).shape.stride) ∧
    A.internal=(B).lowRows*(B).shape.stride ∧
    retained T low ln+BucketIndex.ports copies (I).t=2*pairs T low ln+2*(B).bank := by
  exact ⟨rfl,rfl,by rw [two_mul (B).bank]; rfl⟩

theorem relayLeaf_shape (stage : Fin (q+1)) :
    let A := RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask stage
    A.cells=(B).relays ∧ A.internal=0 ∧ BucketIndex.ports copies (I).t=2*(B).bank := by
  exact ⟨rfl,rfl,by rw [two_mul]; rfl⟩

theorem initialSite_sizes (A : HistoryInitialSeed.Layout) (a : HistoryInitialSeed.Site)
    (same : A.trace=B) (T : ℕ) (extent : 2*T≤S) (pub : ℕ→Bool) (stage : Fin (q+1))
    (time : a.stage=stage.val) :
    let first := pairLeaf hF hw hp base st hs hf r k fit L copies T extent pub
    let later := RelayNetwork.network (F:=F) (r:=copies) (I).tag (P).mask stage
    a.rows A=(if stage.val=0 then first.cells else later.cells) ∧
    a.bits A=(if stage.val=0 then first.internal else later.internal) := by
  intro first later
  obtain ⟨fr,fb,_⟩ := pairLeaf_shape hF hw hp base st hs hf r k fit L copies raw dict masks ids T extent pub
  obtain ⟨lr,lb,_⟩ := relayLeaf_shape hF hw hp base st hs hf r k fit L copies raw dict masks ids stage
  by_cases active : stage.val=0 <;>
    simp [HistoryInitialSeed.Site.rows,HistoryInitialSeed.Site.bits,HistoryInitialSeed.Layout.hidden,same,time,
      active,first,later,fr,fb,lr,lb]

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
