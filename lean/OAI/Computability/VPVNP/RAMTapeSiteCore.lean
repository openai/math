import OAI.Computability.VPVNP.RAMTapeSiteValidated
import OAI.Computability.VPVNP.RAMTapeSitePostEntry
import OAI.Computability.VPVNP.RAMTapeSiteEntryView
import OAI.Computability.VPVNP.RAMTapeSiteChoiceCard

/-! # Exact private-path count of the site's fixed physical verifier -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM PrivateRAM LiveProgram
variable {p r k d e w : ℕ}

/-- Prepare the guarded site entry and then run the per-choice verifier for the fixed
instruction template. -/
def core (r : ℕ) (expr : Fin k → PublicExpr) (T : Template p r k) : FiniteRoutine (Port r expr) :=
  (prepareEntry r expr).followedBy (perChoice r expr T)

/-- Site-core step budget combining entry costs with the per-choice bound at the site’s fuel. -/
def coreSteps (r : ℕ) (x : SiteCutBank.Input d e w) :=
  perChoiceBudget d e w r (x.n^x.u) + entrySteps x

theorem core_spec (r : ℕ) (expr : Fin k → PublicExpr) (T : Template p r k) (x : SiteCutBank.Input d e w)
    (operands : Fin k → Word w) (s : Stacks (Port r expr)) (hf : Frame r expr x operands s)
    (hblank : ∀ j : SitePost.Port, s (.inr (.inr j)) = []) (t : ℕ) (ht : coreSteps r x ≤ t) :
    (∀ c, (core r expr T).body.count c t s = x.pathCard T operands) ∧
      (∀ c, (core r expr T).body.AllStops c t s) := by
  classical
  let rem := t - entrySteps x
  have hrem : perChoiceBudget d e w r (x.n^x.u) ≤ rem := by dsimp [coreSteps, rem] at *; omega
  have heq : t = rem + entrySteps x := by dsimp [coreSteps, rem] at *; omega
  have per (hv : x.valid) (bs : List Bool) :
      (∀ c, (perChoice r expr T).body.count c rem (entryBank r expr x s bs) = (x.accepts T operands bs).toNat) ∧
      (∀ c, (perChoice r expr T).body.AllStops c rem (entryBank r expr x s bs)) :=
    perChoice_complete r expr x T operands bs (entryBank r expr x s bs) hv (entry_view expr x T hf hv bs)
      (PostReady.entry r expr x hf hv hblank bs) rem hrem
  constructor
  · intro c
    change ((prepareEntry r expr).body.followedBy (perChoice r expr T).body).count c t s = _
    rw [Routine.count_followedBy, heq, prepare_count r expr x hf]
    by_cases hv : x.valid
    · rw [ite_eq_left hv]
      have hp := fun bs => (per hv bs).1 c
      simp only [hp, x.choiceCard]
    · rw [ite_eq_right hv, x.invalid_pathCard T operands hv]
  · intro c
    change ((prepareEntry r expr).body.followedBy (perChoice r expr T).body).AllStops c t s
    rw [Routine.allStops_followedBy, heq, prepare_allStops r expr x hf]
    exact fun hv bs _ => (per hv bs).2 c

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
