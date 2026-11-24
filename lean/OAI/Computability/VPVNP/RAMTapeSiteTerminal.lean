import OAI.Computability.VPVNP.RAMTapeBoundary
import OAI.Computability.VPVNP.RAMTapeSuccessorDispatch
import OAI.Computability.VPVNP.StructuredStackCount
import OAI.Computability.VPVNP.StructuredStackTotal

/-!
# Terminal predecessor check on the actual sorted site tapes

The address selects the missing-edge cases. The record scan adds its verdict
to the list of flags produced by the sort. A final linear pass halts with the
conjunction of all of these flags, including after a failed comparison.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteTerminal

open BurstRAM Boundary RAMBoundary

variable {K : Type} [DecidableEq K]

private def branch (ports : Boundary.Port → K) (flags : K) (outgoing incoming : Bool) : FiniteRoutine K :=
  FiniteRoutine.ofRoutine ({
    entry := .start
    code
      | .done b => .push flags b none
      | q => (Boundary.code incoming outgoing q).rename ports some
  } : Routine K Boundary.Phase)

private noncomputable def after (ports : Boundary.Port → K) (s : Stacks K) (hp hs : Bool)
    {w : ℕ} (previous sent : RawSlot w) (xs : List (RawSlot w)) : Stacks K :=
  let last := (rows previous xs (hp || (recordBytes previous).all (!·))).1
  installStacks ports s (store [] (recordBytes (if hs then sent else last)) [] (List.replicate w true) [] [] [])

/-- Prepare the final sorted block, the predecessor and sent boundary records, a unary
word-width counter and one marker per slot for the boundary scan. -/
def inputs {w : ℕ} (previous sent : RawSlot w) (xs : List (RawSlot w)) : Stacks Boundary.Port :=
  store (blockBytes xs) (recordBytes previous) (recordBytes sent) (List.replicate w true) [] []
    (List.replicate xs.length true)

private theorem branch_runs (ports : Boundary.Port → K) (hi : Function.Injective ports) (flags : K)
    (hf : ∀ j, ports j ≠ flags) (hp hs : Bool) (s : Stacks K) {w : ℕ} (prev sent : RawSlot w)
    (xs : List (RawSlot w)) (hb : ∀ j, s (ports j) = inputs prev sent xs j) :
    (branch ports flags hs hp).Runs (Boundary.work hp hs xs.length w+1) s
      (Function.update (after ports s hp hs prev sent xs) flags
        (decision hp hs prev sent xs :: s flags)) := by
  let r := (branch ports flags hs hp).body
  have h := (Boundary.runs hp hs prev sent xs).lift ports hi some s (target := r.standalone)
    (by intro q hq; cases q <;> first | rfl | contradiction)
  have hin := installStacks_eq hi s (inputs prev sent xs) hb
  change StackRuns r.standalone _ (some .start) (installStacks ports s (inputs prev sent xs))
    (some (.done (decision hp hs prev sent xs))) (after ports s hp hs prev sent xs) at h
  rw [hin] at h
  have endFlag : after ports s hp hs prev sent xs flags = s flags := installStacks_outside _ _ hf
  have push := StackStep.push (s := after ports s hp hs prev sent xs) (code := r.standalone)
    (q := some (.done (decision hp hs prev sent xs)))
    (show r.standalone (some (.done _)) = .push flags (decision hp hs prev sent xs) none from rfl)
  rw [endFlag] at push
  exact h.trans (.cons push (.nil ..))

private def verdicts (flags : K) : FiniteRoutine K :=
  FiniteRoutine.ofRoutine ({
    entry := none
    code
      | none => .pop flags fun bit => some (if bit.isNone then some true else
          if bit = some true then none else some false)
      | some b => .halt b
  } : Routine K (Option Bool))

private theorem verdicts_count (flags : K) (c : ℕ → Stacks K → ℕ) (extra : ℕ)
    (xs : List Bool) (s : Stacks K) (hf : s flags = xs) :
    (verdicts flags).body.count c (extra+xs.length+2) s = (xs.all id).toNat := by
  induction xs generalizing s extra with
  | nil =>
    change (verdicts flags).body.countFrom c ((extra+1)+1) (some none) s = 1
    change (verdicts flags).body.countFrom c (extra+1) (some (if (s flags).head?.isNone then some true else
      if (s flags).head? = some true then none else some false)) _ = _
    rw [hf]; rfl
  | cons b xs ih =>
    rw [List.length_cons, show extra+(xs.length+1)+2 = (extra+xs.length+2)+1 by omega]
    change (verdicts flags).body.countFrom c ((extra+xs.length+2)+1) (some none) s = _
    change (verdicts flags).body.countFrom c (extra+xs.length+2) (some (if (s flags).head?.isNone then
      some true else if (s flags).head? = some true then none else some false))
      (Function.update s flags (s flags).tail) = _
    rw [hf]
    cases b with
    | false => rfl
    | true => exact ih extra (Function.update s flags xs) (Function.update_self ..)

private theorem verdicts_total (flags : K) (c : ℕ → Stacks K → Prop) (extra : ℕ)
    (xs : List Bool) (s : Stacks K) (hf : s flags = xs) :
    (verdicts flags).body.AllStops c (extra+xs.length+2) s := by
  induction xs generalizing s extra with
  | nil =>
    change (verdicts flags).body.AllStopsFrom c ((extra+1)+1) (some none) s
    change (verdicts flags).body.AllStopsFrom c (extra+1) (some (if (s flags).head?.isNone then some true else
      if (s flags).head? = some true then none else some false)) _
    rw [hf]; trivial
  | cons b xs ih =>
    rw [List.length_cons, show extra+(xs.length+1)+2 = (extra+xs.length+2)+1 by omega]
    change (verdicts flags).body.AllStopsFrom c ((extra+xs.length+2)+1) (some none) s
    change (verdicts flags).body.AllStopsFrom c (extra+xs.length+2) (some (if (s flags).head?.isNone then
      some true else if (s flags).head? = some true then none else some false))
      (Function.update s flags (s flags).tail)
    rw [hf]
    cases b with
    | false => trivial
    | true => exact ih extra (Function.update s flags xs) (Function.update_self ..)

/-- Use the site address to choose the endpoint checks, scan the sorted records, then halt with
the conjunction of the scan verdict and the accumulated sort flags. -/
def routine (ports : Boundary.Port → K) (addr tmp flags : K) : FiniteRoutine K :=
  (SuccessorEnds.dispatch addr tmp (branch ports flags)).followedBy (verdicts flags)

/-- Tick allowance for selecting the endpoint case, checking the sorted records and consuming
every accumulated verdict flag. -/
def steps (d w B : ℕ) (v : Word d) (flags : List Bool) : ℕ :=
  flags.length+3+(4*d+3+(Boundary.work (decide (0<v.val)) (decide (v.val+1<2^d)) B w+1))

theorem steps_le (d w B : ℕ) (v : Word d) (flags : List Bool) :
    steps d w B v flags ≤ flags.length + 4*d + 96*(B+1)*(w+1) + 7 := by
  have h := Boundary.work_le (decide (0<v.val)) (decide (v.val+1<2^d)) B w
  unfold steps
  omega

variable (ports : Boundary.Port → K) (hi : Function.Injective ports) (addr tmp flags : K)
  (hat : addr ≠ tmp) (hf : ∀ j, ports j ≠ flags) {w d : ℕ} (prev sent : RawSlot w)
  (xs : List (RawSlot w)) (v : Word d) (s : Stacks K)
  (ha : s addr = BurstRAM.wordBits v) (ht : s tmp = []) (hb : ∀ j, s (ports j) = inputs prev sent xs j)

include hi hat hf ha ht hb

theorem count (c : ℕ → Stacks K → ℕ) (extra : ℕ) :
    (routine ports addr tmp flags).body.count c (extra + steps d w xs.length v (s flags)) s =
      (decision (decide (0<v.val)) (decide (v.val+1<2^d)) prev sent xs && (s flags).all id).toNat := by
  let hp := decide (0<v.val)
  let hs := decide (v.val+1<2^d)
  let b := decision hp hs prev sent xs
  let out := Function.update (after ports s hp hs prev sent xs) flags (b :: s flags)
  have h := SuccessorEnds.dispatch_runs addr tmp hat (branch ports flags) s v ha ht
    (branch_runs ports hi flags hf hp hs s prev sent xs hb)
  rw [show extra+steps d w xs.length v (s flags) =
    (extra+(b::s flags).length+2)+(4*d+3+(Boundary.work hp hs xs.length w+1)) by simp [steps,hp,hs]; omega]
  change ((SuccessorEnds.dispatch addr tmp (branch ports flags)).body.followedBy (verdicts flags).body).count c _ s = _
  rw [Routine.count_followedBy, h.count_eq]
  exact verdicts_count flags c extra (b::s flags) out (Function.update_self ..)

theorem total (c : ℕ → Stacks K → Prop) (extra : ℕ) :
    (routine ports addr tmp flags).body.AllStops c (extra + steps d w xs.length v (s flags)) s := by
  let hp := decide (0<v.val)
  let hs := decide (v.val+1<2^d)
  let b := decision hp hs prev sent xs
  let out := Function.update (after ports s hp hs prev sent xs) flags (b :: s flags)
  have h := SuccessorEnds.dispatch_runs addr tmp hat (branch ports flags) s v ha ht
    (branch_runs ports hi flags hf hp hs s prev sent xs hb)
  rw [show extra+steps d w xs.length v (s flags) =
    (extra+(b::s flags).length+2)+(4*d+3+(Boundary.work hp hs xs.length w+1)) by simp [steps,hp,hs]; omega]
  change ((SuccessorEnds.dispatch addr tmp (branch ports flags)).body.followedBy (verdicts flags).body).AllStops c _ s
  rw [Routine.allStops_followedBy, h.allStops_iff]
  exact verdicts_total flags c extra (b::s flags) out (Function.update_self ..)

end RAMTape.SiteTerminal

end VPVNP
end Computability
end OAI
