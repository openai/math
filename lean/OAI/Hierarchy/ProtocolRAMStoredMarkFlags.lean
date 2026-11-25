import OAI.Hierarchy.ProtocolRAMPurchaseShelfRecords
import OAI.Hierarchy.ProtocolRAMPurchaseMarks

namespace OAI
/-! # Original signed purchase strata and their physical flag words -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical Fin.CommRing

/-- The same native tile is in at most one signed stratum, even when several
altimeters cross their thresholds. The stored first qualifying sign decides. -/
theorem actualMarks_unique {z d k : ℕ} (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen : Shelf.Mem z d) (s : StageAt z d) (c c' : Fin k×Bool) (r : Fin (2^z))
    (one : r∈actualMarks sh phase T kind frozen s c) (two : r∈actualMarks sh phase T kind frozen s c') : c=c' := by
  simp only [actualMarks,Shelf.marked,stage_key,axis_key] at one two
  by_contra different
  exact Finset.disjoint_left.mp
    (PurchaseMarks.strata_disjoint phase T kind sh.table (sh.stock s) frozen
      (fun equal => different ((PurchaseMarks.signedDirection k).symm.injective equal))) one two

variable {z d k : ℕ}
local notation "W" => Native.wordBits z d Native.copies

/-- The bits are the original CT measured decisions, at the actual contiguous
stage-sign-candidate addresses of the outer shelf. -/
def StoredFlags (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen after : Shelf.Mem z d) (k : ℕ) : Prop :=
  ∀ (key : Key z d k) (r : Fin (paths z S.degree depth)),
    after (sh.flagsBase S z d k depth+key.val*paths z S.degree depth+r.val) =
      MarkTape.encode W ((sh.decisions S π depth phase T kind frozen key)[r.val]'(by simp))

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
