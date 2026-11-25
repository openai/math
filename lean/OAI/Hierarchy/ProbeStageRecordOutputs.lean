import OAI.Hierarchy.ProbeStageEndpoint
import OAI.Hierarchy.ProbeStageRecordChoice

namespace OAI
/-! # The three native output words and their two actual lookup charges -/

namespace Hierarchy.ProbeStage.Record
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing

/-- The per-side prefix state consists of actual counter and advice words and an address
frame. The offset/clear directory is read in the physical order used by the scatter. -/
structure EndpointInput {B ℓ w : ℕ} (s : RankUpdate.Layout) (m : Memory w) (rank : ℕ)
    (strings : MaskIndex B → Fin ℓ → Fin B) (color : Fin B) (width : ℕ)
    (place : MaskIndex B → ℕ → Word w) (frozen : ℕ → Prop) : Prop where
  distinct : RankUpdate.Distinct s m
  previous : (m (RankUpdate.counter s m).val).val=rank
  quotaFit : s.quota<2^w
  rankFit : rank+1<2^w
  length : (RankUpdate.dirWord s.lengths s.chosen m).val=(PackedMask.occurrences strings color).length
  literal : RankUpdate.Directory s m (RankUpdate.edits strings color rank s.quota) width place frozen
  rankAddr : frozen s.rank
  counterAddr : frozen (RankUpdate.counter s m).val

/-- Both incidence ranks in a single actual memory image, as well as the exact scan and
scatter lengths responsible for this execution's charged time. -/
theorem physical_outputs {B ℓ w : ℕ} (a : Advice) (s : Scratch) (r : Row) (m : Memory w)
    (strings : MaskIndex B → Fin ℓ → Fin B) (idx : MaskIndex B) (L R good : Finset (Fin B))
    (pos : 0<B) (free : good.Nonempty) (choice : ChoiceInput a r s m (strings idx) L R good)
    (enter exit : ℕ) (places : Bool → MaskIndex B → ℕ → Word w) (frozen : Bool → ℕ → Prop)
    (left : EndpointInput (side a r s true) (leftInput a s r m) enter strings
      (maskedChoice pos (strings idx) good) a.width (places true) (frozen true))
    (right : EndpointInput (side a r s false) (rightInput a s r m) exit strings
      (maskedChoice pos (strings idx) good) a.width (places false) (frozen false))
    (protectChosen : ∀ b, frozen b r.chosen ∧ r.chosen∉RankUpdate.touched (side a r s b)
      (if b then leftInput a s r m else rightInput a s r m))
    (protectEnter : frozen false r.enterRank ∧ r.enterRank∉RankUpdate.touched (side a r s false) (rightInput a s r m)) :
    let color := maskedChoice pos (strings idx) good
    let out := image a s r m
    out r.chosen=(color.val:Word w) ∧ (out r.enterRank).val=enter ∧ (out r.exitRank).val=exit ∧
    scans a s r m=(if (freeBits (strings idx) good).Nonempty then 0 else B) ∧
    clears a s r m=(RankUpdate.edits strings color enter a.quota).length+
      (RankUpdate.edits strings color exit a.quota).length := by
  obtain ⟨scan,hcolor⟩ := physical_choice a s r m (strings idx) L R good pos free choice
  obtain ⟨went,_,nl,fl⟩ := RankUpdate.committed _ _ left.distinct enter left.previous left.quotaFit left.rankFit
    strings _ left.length a.width (places true) (frozen true) left.literal left.rankAddr left.counterAddr
  obtain ⟨wexit,_,nr,fr⟩ := RankUpdate.committed _ _ right.distinct exit right.previous right.quotaFit right.rankFit
    strings _ right.length a.width (places false) (frozen false) right.literal right.rankAddr right.counterAddr
  have cl := fl r.chosen (protectChosen true).1 (protectChosen true).2
  have cr := fr r.chosen (protectChosen false).1 (protectChosen false).2
  have er := fr r.enterRank protectEnter.1 protectEnter.2
  exact ⟨cr.trans (cl.trans hcolor),(congrArg Fin.val er).trans went,wexit,scan,congrArg₂ Nat.add nl nr⟩

end Hierarchy.ProbeStage.Record

end OAI
