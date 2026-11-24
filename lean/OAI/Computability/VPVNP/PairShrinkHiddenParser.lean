import OAI.Computability.VPVNP.PairShrinkHiddenSlots

/-!
# The private hidden rows consumed by the selected shrinking kernel

At each site the hidden rows occur in the order of the native directory.
Their concatenated bit fields are the entire branch string consumed by the
kernel. The subsequent resident matrix checks contribute no choice bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenSlots

open Compression Compression.ShrinkMotif CompressorRecords ShrinkHistoryRows LocalHistory NetworkKernel
open scoped Classical

variable {a g : ℕ} (X : State a (packingLaneBits a g))

/-- Dense identifiers and little-endian bit fields in the site's scan order. -/
def rows (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v) :
    List (ℕ × List Bool) :=
  let o := residents (hiddenOrder X) (X.packingData.shrinkInternalOwner layout) v
  List.ofFn fun j =>
    let e := o.entries j
    (id X e.val, List.ofFn (RAMSerialization.wordBits _ (h e.val e.prop)))

private theorem order_member {U V : Type} (o : Order U) (f : U → V) (e : U) :
    f e ∈ List.ofFn (fun j => f (o.entries j)) :=
  List.mem_ofFn.mpr ⟨o.entries.symm e, congrArg f (o.entries.apply_symm_apply e)⟩

set_option maxHeartbeats 1500000 in
/-- The row for every absorbed edge at this site occurs in the scan. -/
theorem mem_rows (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v)
    (e : X.packingData.Motif × Fin 4) (hv : v = X.packingData.shrinkInternalOwner layout e) :
    (id X e, List.ofFn (RAMSerialization.wordBits _ (h e hv))) ∈ rows X layout widths v h := by
  exact order_member (residents (hiddenOrder X) (X.packingData.shrinkInternalOwner layout) v)
    (fun u => (id X u.val, List.ofFn (RAMSerialization.wordBits _ (h u.val u.prop)))) ⟨e,hv⟩

theorem rows_nodup (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v) :
    ((rows X layout widths v h).map Prod.fst).Nodup := by
  rw [rows, List.map_ofFn, List.nodup_ofFn]
  let o := residents (hiddenOrder X) (X.packingData.shrinkInternalOwner layout) v
  exact (id_injective X).comp (Subtype.val_injective.comp o.entries.injective)

open private fiber_encode from OAI.Computability.VPVNP.PairNodeArguments

private theorem bounded_encode {width : ℕ} (x : Fin (2 ^ width)) :
    (ChoiceReader.bounded width (2 ^ width) le_rfl).encode x = List.ofFn (RAMSerialization.wordBits _ x) := by
  change BurstRAM.wordBits (Fin.ofNat (2 ^ width) x.val) = BurstRAM.wordBits x
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt)

private theorem fiber_rows (layout : Bool) (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
    (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v) :
    let owner := X.packingData.shrinkInternalOwner layout
    (fiber owner v (residents (hiddenOrder X) owner v)
      (fun e => ChoiceReader.bounded (widths e.1 (!layout,e.2)) _ le_rfl)).encode h =
      ((rows X layout widths v h).map Prod.snd).flatten := by
  intro owner
  erw [fiber_encode]
  rw [rows, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  exact bounded_encode _

private theorem skip_empty (a b c : List Bool) (ha : a = c) (hb : b.length = 0) :
    a ++ b = c := by simp [ha, List.length_eq_zero_iff.mp hb]

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)

set_option maxHeartbeats 4000000 in
/-- Exact word-for-word agreement with the kernel of the scheduled pass. -/
theorem kernel_encode {g : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (s : X.ShrinkSelection B.shrink) (v old new)
    (x : (B.shrinkPassWitnesses f hf i rfl X s v old new).Choice) :
    let layout := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
    let widths := fun m => X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B.shrink m (s m)
    ((shrinkPassReaders B f hf i rfl X).kernel s v old new).encode x =
      ((rows X layout widths v x.1).map Prod.snd).flatten := by
  intro layout widths
  let owner := X.packingData.shrinkInternalOwner layout
  let o := residents (hiddenOrder X) owner v
  change (fiber owner v o (fun e => ChoiceReader.bounded (widths e.1 (!layout,e.2)) _ le_rfl)).encode x.1 ++ _ = _
  apply skip_empty
  · exact fiber_rows X layout widths v x.1
  · erw [Order.reader_length]
    simp only [motifEntryReader, listedEntryReader_length, Finset.sum_const_zero]

end PairSimulation.ShrinkHiddenSlots

end

end VPVNP
end Computability
end OAI
