import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.CompressorRecordsBundleWords
import OAI.Computability.VPVNP.CompressorRecordsShrinkGraph

/-!
# Reading the classifier inputs from the two preceding directories

The first probe follows the actual outgoing column of the old state. The
quotient of its value is the site index of the destination in the completed
shrinking scan. The source quotient is the corresponding source site index.
Thus the five placement lookups address the rows of the two typed endpoints.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM Compression
open scoped Fin.CommRing

variable {w a g : ℕ}

private theorem input_number (X : State a (packingLaneBits a g)) (e : BundleKeys.OldArc X.Base a g) :
    IncidenceDirectory.actualPort (w := w) X (packingInputEdges X.Base a g e) =
      ShrinkRAM.word w (BundleKeys.oldArcOrder X.baseIndex e).val := by
  rw [BundleKeys.oldArcOrder_val, Shrink.oldNumber_original]
  rfl

/-- Reassembling the typed arc preserves its actual destination and incoming slot. -/
theorem input_target (X : State a (packingLaneBits a g)) (e : BundleKeys.OldArc X.Base a g) :
    packingInputEdges X.Base a g (X.packingData.actual e) =
      X.slots.actualGraph.target (packingInputEdges X.Base a g e) := by
  let A := packingArcEquiv X.Base a g
  obtain ⟨z, rfl⟩ := A.surjective e
  have pack (v : (X.Base × Fin (2^a)) × BitWord (packingLaneBits a g)) :
      packingInputEdges X.Base a g (A v) = ((v.1.1,v.2),v.1.2) :=
    (packingInputEdges X.Base a g).apply_symm_apply ((v.1.1,v.2),v.1.2)
  rw [orderedDyadicPacking_actual X.slots X.baseIndex z, pack, pack]
  rfl

/-- Dividing a physical port number by the degree recovers its shrinking site index. -/
theorem site_quotient (X : State a (packingLaneBits a g)) (degree : Word w)
    (hd : degree.val = 2^a) (e : BundleKeys.OldArc X.Base a g) (v : Word w)
    (hv : v.val = (BundleKeys.oldArcOrder X.baseIndex e).val) :
    ShrinkRAM.div v degree = ShrinkRAM.word w (Shrink.oldNumber X.baseIndex (sourcePosition e)) := by
  change ShrinkRAM.word w (v.val / degree.val) = _
  rw [hd, hv, BundleKeys.oldArcOrder_val, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt e.1.2.isLt, Nat.add_zero]

private theorem word_eq {x : Word w} {v : ℕ} (h : x.val = v) : x = (v : Word w) := by
  subst v
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

/-- The source and destination words read by the classifier are the entries
computed by the typed placement scan, at the two ends of this old arc. -/
theorem ReadsPlacement.of_directory (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
    {p : Fin 11 → Word w} {shrPub : Fin 14 → Word w} {m : Memory w} {layout : Bool}
    (inc : T.ActualColumns X m)
    (placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex shrPub layout m)
    (hdegree : (p 0).val = 2^a) (hOut : p 5 = T.actualOut)
    (hThick : p 6 = shrPub 11) (hOwner : p 7 = shrPub 10) (hAssigned : p 8 = shrPub 12)
    (fit : Fintype.card X.Base * 2^(packingLaneBits a g) * 2^a ≤ 2^w)
    (e : BundleKeys.OldArc X.Base a g) {i : Word w} (hi : i.val = (BundleKeys.oldArcOrder X.baseIndex e).val) :
    ReadsPlacement p m i (BundleKeys.siteRow X.slots X.baseIndex layout (sourcePosition e))
      (BundleKeys.siteRow X.slots X.baseIndex layout (sourcePosition (X.packingData.actual e))) := by
  let src := sourcePosition e
  let dst := sourcePosition (X.packingData.actual e)
  let idx (x : Shrink.Old X.Base a g) := ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x)
  have hsrc : sourceSite p i = idx src := site_quotient X _ hdegree e _ hi
  have hid : i = IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e) := by
    rw [input_number]; exact word_eq hi
  have hm : m (p 5+i).val = ShrinkRAM.word w (BundleKeys.oldArcOrder X.baseIndex (X.packingData.actual e)).val := by
    rw [hOut, hid, inc.actualOut, ← input_target, input_number]
  have hdst : targetSite p m i = idx dst := by
    apply site_quotient X _ hdegree (X.packingData.actual e)
    rw [hm]
    exact Nat.mod_eq_of_lt ((BundleKeys.oldArcOrder X.baseIndex (X.packingData.actual e)).isLt.trans_le fit)
  let siteRow := BundleKeys.siteRow X.slots X.baseIndex layout
  have row (x : Shrink.Old X.Base a g) :
      (m (shrPub 10+idx x).val).val = (siteRow x).owner ∧
      (m (shrPub 11+idx x).val).val = (siteRow x).thick.toNat ∧
      (m (shrPub 12+idx x).val).val = (siteRow x).assigned := by
    have h := placement.atSite x
    exact ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h,
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h⟩
  constructor
  all_goals
    simp only [readValue, readAddress, Matrix.cons_val, hsrc, hdst, hThick, hOwner, hAssigned]
  · exact word_eq (row src).2.1
  · exact word_eq (row dst).2.1
  · exact word_eq (row src).1
  · exact word_eq (row src).2.2
  · exact word_eq (row dst).2.2

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
