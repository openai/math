import OAI.Computability.VPVNP.CompressorShrinkABResident
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch

/-! # The resident shrink tables on a legal term branch

The absolute-ID gather, term selection and selected geometry use the same
compact motif order. Their memory frames preserve the original demand columns
through the branch and the subsequent hidden-map writes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression BurstRAM ShrinkBlockInputs
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
variable (T : IncidenceDirectory w) (start : ℕ) (stride selectors : Word w) (cap : ℕ)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w
local notation "keepEnd" => SelectedFinish.stop X (ShrinkInput.termHead (w := w) X start) stride

set_option maxHeartbeats 1200000 in
/-- The legal native branch supplies every resident input for the allocated
AB, surviving-width and incidence-slot passes. -/
theorem resident_of_branch {m : Memory w} (p : ShrinkBranch.Prefix X T start cap m)
    (v : ShrinkBranch.Selected B X T start stride selectors cap m p sel)
    (fit : ShrinkBranch.PrefixFits B X T start stride cap) (width : ℕ) (input : Memory w)
    (hiddenFrame : ∀ x < keepEnd, input x = v.beforeOutput x) :
    Resident B i X sel term stride ids T start width input := by
  have room := fit.termRoom
  unfold ShrinkInput.termEnd at room
  have endRoom : ShrinkInput.stop X start < 2^w := by omega
  have stopTerm : ShrinkInput.stop X start ≤ (term).val := by
    change _ ≤ (_+_ : ℕ) % 2^w
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hbound := old_bounds i X term stride
  have stopEarly : ShrinkInput.stop X start ≤ keepEnd := by omega
  have frame (x : ℕ) (hx : x < ShrinkInput.stop X start) :
      input x = after p.input.post (eventLog p.absolute) x :=
    (hiddenFrame x (hx.trans_le stopEarly)).trans (v.lowerFrame x hx)
  have stored := p.input.keepAbsoluteFrame endRoom p.absoluteRun.frame
  have earlier := (ShrinkInput.termLayout X T start stride.val fit.termRoom).2.1
  have headLe : (ShrinkInput.demandHead (w := w) X start).val ≤ ShrinkInput.stop X start := Nat.mod_le ..
  apply resident_from_geometry B i X sel term stride ids T start width selectors
    (ShrinkInput.placementBank X T start) (after p.beforeTerm (eventLog v.terms)) input
    v.geometry.placed v.geometry.children fit.wide v.postTerm.geometry hiddenFrame
    (ShrinkDemandFrame.retain stored.stored earlier (fun x hx => frame x (hx.trans_le headLe)))
  exact p.absoluteRun.directory_after p.input frame

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
