import OAI.Computability.VPVNP.RAMTapeSiteEntryFrame
import OAI.Computability.VPVNP.RAMTapeSiteEntryZero
import OAI.Computability.VPVNP.RAMProcessorChoices

/-!
# The guarded site entry and its continuation

The two successor fields are checked before the global credit is initialized. On a
valid site the choice routine exhausts its unary budget and enters the continuation
once for each permitted bit stream. All such streams leave the same residual clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

set_option synthInstance.maxSize 256

open BurstRAM LiveProgram

variable {k d e w : ℕ} (r : ℕ) (expr : Fin k → PublicExpr)

private def choices := ProcessorChoices.routine (pub r expr ProcessorPublic.budgetPort)
  (native r expr (.test .choices))

/-- Check the successor fields, initialize the global credit word, and generate the bounded
private choice string. -/
def prepareEntry : FiniteRoutine (Port r expr) :=
  (SiteCutBank.checked.onPorts (cut r expr)).followedBy
    ((zeroGlobal r expr).followedBy (.ofRoutine (choices r expr)))

variable (x : SiteCutBank.Input d e w)

/-- Steps for the successor scan and guards, zero-word initialization, and the complete bounded
choice pass. -/
def entrySteps : ℕ :=
  x.readSteps + 2 + (5*w+2) + (4*(2*2^e*(x.n^x.u+w))+1)

/-- Polynomial running time once the public width and bucket fit the physical input. -/
theorem entrySteps_le (hu : 1 ≤ x.u) (hH : 2^e ≤ 2*x.n) (hw : w ≤ x.n) :
    entrySteps x ≤ 400*(x.n+1)^(x.u+1) := by
  have hd : d ≤ x.n := (Nat.le_add_right d e).trans (x.hcap.le.trans hw)
  have read : x.readSteps ≤ 4*d+234*w+107 := Successors.steps_le _ _ _
  let M := (x.n+1)^x.u
  have hn : x.n+1 ≤ M := Nat.le_self_pow (by omega) _
  have hf : x.n^x.u ≤ M := Nat.pow_le_pow_left (by omega) _
  have hguess := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hH)
    (show x.n^x.u+w ≤ 2*M by omega)
  have hnom : 2*2^e*(x.n^x.u+w) ≤ 8*(x.n+1)^(x.u+1) := by
    calc
      _ ≤ (2*(2*x.n))*(2*M) := hguess
      _ = 8*(M*x.n) := by ring
      _ ≤ 8*(M*(x.n+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by rw [pow_succ]
  have hl : x.n+1 ≤ (x.n+1)^(x.u+1) := Nat.le_self_pow (by omega) _
  unfold entrySteps
  omega

variable {operands : Fin k → Word w} {s : Stacks (Port r expr)}
  (hf : Frame r expr x operands s)

include hf

private theorem guardZeroRuns :
    (zeroGlobal r expr).Runs (5*w+2) (guardBank r expr x s) (zeroBank r expr x s) := by
  apply zeroGlobal_runs
  · change guardBank r expr x s (cut r expr (.inl (.inl SiteSetup.zerosPort))) = _
    rw [guardBank_at, guarded_public_ne x _ (by decide)]
    conv_rhs => rw [x.width_eq]
    rfl
  · rw [guardBank_native]
    exact hf.natives _
  · change guardBank r expr x s (cut r expr (.inl (.inr (.scratch 2)))) = []
    rw [guardBank_at, guarded_public_ne x _ (by decide)]
    rfl

private theorem zeroBankChoices :
    Function.update (Function.update (zeroBank r expr x s) (pub r expr ProcessorPublic.budgetPort)
      (List.replicate (2*2^e*(x.n^x.u+w)) true)) (native r expr (.test .choices)) [] =
        zeroBank r expr x s := by
  have hb : zeroBank r expr x s (pub r expr ProcessorPublic.budgetPort) =
      List.replicate (2*2^e*(x.n^x.u+w)) true := by
    change Function.update (guardBank r expr x s) _ _ (cut r expr (.inl ProcessorPublic.budgetPort)) = _
    rw [Function.update_of_ne ((native_ne_cut r expr _ _).symm),
      guardBank_at, guarded_public_ne x _ (by decide)]
    rfl
  have hbits : zeroBank r expr x s (native r expr (.test .choices)) = [] := by
    change Function.update (guardBank r expr x s) (native r expr (.credit (.budget .globalLeft))) _
      (native r expr (.test .choices)) = []
    rw [Function.update_of_ne (by simp [native]), guardBank_native]
    exact hf.natives _
  rw [← hb, Function.update_eq_self, ← hbits, Function.update_eq_self]

private theorem choices_count (c : ℕ → Stacks (Port r expr) → ℕ) (t : ℕ) :
    (choices r expr).count c (t + 4*(2*2^e*(x.n^x.u+w)) + 1) (zeroBank r expr x s) =
      ((ProcessorChoices.words (2*2^e*(x.n^x.u+w))).map (fun bs => c t (entryBank r expr x s bs))).sum := by
  have h := ProcessorChoices.count (pub r expr ProcessorPublic.budgetPort)
    (native r expr (.test .choices)) (by simp [pub, native]) (zeroBank r expr x s)
    (List.replicate (2*2^e*(x.n^x.u+w)) true) c t
  simpa only [choices, entryBank, List.length_replicate, zeroBankChoices r expr x hf] using h

private theorem choices_allStops (c : ℕ → Stacks (Port r expr) → Prop) (t : ℕ) :
    (choices r expr).AllStops c (t + 4*(2*2^e*(x.n^x.u+w)) + 1) (zeroBank r expr x s) ↔
      ∀ bs : List Bool, bs.length ≤ 2*2^e*(x.n^x.u+w) → c t (entryBank r expr x s bs) := by
  have h := ProcessorChoices.allStops_iff (pub r expr ProcessorPublic.budgetPort)
    (native r expr (.test .choices)) (by simp [pub, native]) (zeroBank r expr x s)
    (List.replicate (2*2^e*(x.n^x.u+w)) true) c t
  simpa only [choices, entryBank, List.length_replicate, zeroBankChoices r expr x hf] using h

open scoped Classical in
/-- Invalid successor fields reject. Each valid bounded word enters the continuation
on the bank containing that word and with exactly the requested residual fuel. -/
theorem prepare_count (c : ℕ → Stacks (Port r expr) → ℕ) (t : ℕ) :
    (prepareEntry r expr).body.count c (t + entrySteps x) s =
      if x.valid then
        ((ProcessorChoices.words (2*2^e*(x.n^x.u+w))).map (fun bs => c t (entryBank r expr x s bs))).sum
      else 0 := by
  let a := SiteCutBank.checked.onPorts (cut r expr)
  let b := (zeroGlobal r expr).body.followedBy (choices r expr)
  let u := t + 4*(2*2^e*(x.n^x.u+w)) + 1
  have he : t + entrySteps x = (u + (5*w+2)) + 2 + x.readSteps := by dsimp [entrySteps, u]; omega
  change (a.body.followedBy b).count c _ _ = _
  rw [Routine.count_followedBy, he, FiniteRoutine.count_onPorts _ _ (cut_injective r expr),
    show s ∘ cut r expr = x.prepared from funext hf.cuts, SiteCutBank.checked_count]
  by_cases hv : x.valid
  · simp only [hv, ↓reduceIte]
    change ((zeroGlobal r expr).body.followedBy (choices r expr)).count c (u + (5*w+2))
      (guardBank r expr x s) = _
    rw [Routine.count_followedBy, (guardZeroRuns r expr x hf).count_eq]
    exact choices_count r expr x hf c t
  · simp [hv]

/-- The same clock covers all rejecting branches and leaves the same continuation fuel
on every valid branch. -/
theorem prepare_allStops (c : ℕ → Stacks (Port r expr) → Prop) (t : ℕ) :
    (prepareEntry r expr).body.AllStops c (t + entrySteps x) s ↔
      (x.valid → ∀ bs : List Bool, bs.length ≤ 2*2^e*(x.n^x.u+w) → c t (entryBank r expr x s bs)) := by
  let a := SiteCutBank.checked.onPorts (cut r expr)
  let b := (zeroGlobal r expr).body.followedBy (choices r expr)
  let u := t + 4*(2*2^e*(x.n^x.u+w)) + 1
  have he : t + entrySteps x = (u + (5*w+1)) + 3 + x.readSteps := by dsimp [entrySteps, u]; omega
  change (a.body.followedBy b).AllStops c _ _ ↔ _
  rw [Routine.allStops_followedBy, he, FiniteRoutine.allStops_onPorts _ _ (cut_injective r expr),
    show s ∘ cut r expr = x.prepared from funext hf.cuts, SiteCutBank.checked_allStops]
  apply imp_congr_right
  intro _
  change ((zeroGlobal r expr).body.followedBy (choices r expr)).AllStops c (u + (5*w+1)+1)
    (guardBank r expr x s) ↔ _
  rw [show u+(5*w+1)+1 = u+(5*w+2) by omega, Routine.allStops_followedBy,
    (guardZeroRuns r expr x hf).allStops_iff]
  exact choices_allStops r expr x hf c t

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
