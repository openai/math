import OAI.Computability.VPVNP.RAMTapeSitePostLink
import OAI.Computability.VPVNP.RAMTapeSiteEntryCPS

/-! # The sorter frame at entry for every generated choice stream -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM LiveProgram

variable {d e w k : ℕ} (r : ℕ) (expr : Fin k → PublicExpr) (x : SiteCutBank.Input d e w)
  {args : Fin k → Word w} {s : Stacks (Port r expr)}

/-- Prepare the post-pass input certificate at private-choice entry from a valid guard, the
initial frame, and blank sorter scratch. -/
noncomputable def PostReady.entry (hf : Frame r expr x args s) (hvalid : x.valid)
    (hblank : ∀ j : SitePost.Port, s (.inr (.inr j)) = []) (bs : List Bool) :
    PostReady r expr x (entryBank r expr x s bs) := by
  let hg := PostReady.ofGuarded r expr x (guardBank r expr x s) hvalid (guardBank_at r expr x s)
    (fun j => (installStacks_outside _ _ (by rintro (u|u) h <;> simp [cut, pub] at h)).trans (hblank j))
    ((guardBank_native r expr x s _).trans (hf.natives _))
  refine ⟨hg.previous,hg.sent,hg.previous_eq,hg.sent_eq,?_⟩
  refine Eq.trans ?_ hg.bank_eq
  funext j
  change entryBank r expr x s bs (postPorts r expr j) = guardBank r expr x s (postPorts r expr j)
  have h₁ : postPorts r expr j ≠ native r expr (.test .choices) := by
    intro h
    exact (show (SiteProcessor.Port.test .choices : SiteProcessor.Port r k) ≠ .record .output from nofun)
      ((postPorts_eq_call_iff r expr j (.test .choices)).mp h).2
  have h₂ : postPorts r expr j ≠ native r expr (.credit (.budget .globalLeft)) := by
    intro h
    exact (show (SiteProcessor.Port.credit (.budget .globalLeft) : SiteProcessor.Port r k) ≠ .record .output from nofun)
      ((postPorts_eq_call_iff r expr j (.credit (.budget .globalLeft))).mp h).2
  simp only [entryBank, zeroBank, Function.update_of_ne h₁, Function.update_of_ne h₂,
    Function.update_of_ne (postPorts_ne_budget r expr j)]

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
