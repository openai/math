import OAI.Computability.BorderVNP.TeamBurstProbeGuard
import OAI.Computability.VPVNP.AffinePinIndex

/-! # Validating a burst and initializing its physical countdown

The guard decides the two bounds before expanding the binary length. On a legal
interval the entry routine copies and decodes the length into one marker per probe.
An illegal interval reaches an explicit rejecting halt after one additional pop.
The cursor, requested length, public cap and empty private input remain available.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamBurstEntry

open VPVNP BurstRAM RAMTape

/-- Physical operands of the guard, the loop countdown, the decoder reversal scratch
and the private input stack that the loop will populate. -/
inductive Port
  | guard (p : TeamBurstGuard.Port)
  | marks
  | high
  | privateInput
  deriving DecidableEq, Fintype

/-- The guard scratch and the three additional ports are clean at callback entry. -/
structure Ready {w : ℕ} (a q c : Word w) (s : Stacks Port) : Prop where
  /-- Little-endian operands and empty comparison scratch. -/
  operands : TeamBurstGuard.Ready a q c (s ∘ Port.guard)
  /-- The old countdown has been consumed. -/
  marks : s .marks = []
  /-- The decoder starts with empty reversal scratch. -/
  high : s .high = []
  /-- The private submachine receives a fresh input buffer. -/
  input : s .privateInput = []

private def check := TeamBurstGuard.program.onPorts Port.guard
private abbrev flag := Port.guard .flag

private def marked (s : Stacks Port) (b : Bool) := Function.update s flag (b :: s flag)

private theorem check_runs {w : ℕ} {a q c : Word w} {s : Stacks Port} (h : Ready a q c s) :
    check.Runs (18*w+8) s (marked s (decide (q.val ≤ c.val ∧ a.val+q.val ≤ 2^w))) := by
  refine TeamBurstGuard.program.runs_onPorts_framed (ports := Port.guard) (fun _ _ he => Port.guard.inj he) (TeamBurstGuard.runs a q c _
    h.operands) (fun _ => rfl) ?_ ?_
  · intro k
    by_cases hk : k = .flag <;> simp [marked, flag, hk]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .flag)) ..

private def decodePorts : AffinePin.Index.Port → Port
  | .bits => .guard .lengthCopy
  | .high => .high
  | .index => .marks
  | .tmp => .guard .temp

private def load : FiniteRoutine Port :=
  (SuccessorFields.prependCopy (.guard .length) (.guard .lengthCopy) (.guard .temp)).followedBy
    (AffinePin.Index.decode.onPorts decodePorts)

/-- A single fixed physical entry, independent of word width, cap and burst length. -/
def program : FiniteRoutine Port :=
  check.followedBy (.ofRoutine (Routine.popCase flag (.halt false) (.halt false) load.body))

/-- Post-entry bank. The sole change is the installation of the unary countdown. -/
def prepared (s : Stacks Port) (q : ℕ) := Function.update s .marks (List.replicate q true)

private theorem load_runs {w : ℕ} {a q c : Word w} {s : Stacks Port} (h : Ready a q c s) :
    ∃ t ≤ 7*q.val+11*w+4, load.Runs t s (prepared s q.val) := by
  let mid := Function.update s (.guard .lengthCopy) (wordBits q)
  have hq : s (.guard .length) = wordBits q := h.operands.length
  have hcopy : s (.guard .lengthCopy) = [] := h.operands.lengthCopy
  have ht : s (.guard .temp) = [] := h.operands.temp
  have copy := SuccessorFields.prependCopy_runs (.guard .length) (.guard .lengthCopy) (.guard .temp)
    (by decide) (by decide) (by decide) s ht
  rw [hq, length_wordBits, hcopy, List.append_nil] at copy
  obtain ⟨k,hk,run⟩ := AffinePin.Index.decode_runs (wordBits q)
  rw [length_wordBits, TapeWord.value_wordBits] at hk
  rw [TapeWord.value_wordBits] at run
  have decode : (AffinePin.Index.decode.onPorts decodePorts).Runs k mid (prepared s q.val) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) run
    · intro i
      cases i <;> simp [mid, decodePorts, AffinePin.Index.bank, h.marks, h.high, ht]
    · intro i
      cases i <;> simp [prepared, decodePorts, AffinePin.Index.bank, hcopy, h.high, ht]
    · intro i hi
      exact (Function.update_of_ne (Ne.symm (hi .index)) ..).trans
        (Function.update_of_ne (Ne.symm (hi .bits)) ..).symm
  exact ⟨_, by omega, copy.followedBy decode⟩

private theorem pop_marked (s : Stacks Port) (b : Bool) :
    Function.update (marked s b) flag (s flag) = s := by
  simp [marked, Function.update_idem, Function.update_eq_self]

/-- A valid interval passes its bounds check and decodes its length in linear time
in the width and the number of requested words. -/
theorem runs {w : ℕ} {a q c : Word w} {s : Stacks Port} (h : Ready a q c s)
    (legal : q.val ≤ c.val ∧ a.val + q.val ≤ 2^w) :
    ∃ t ≤ 7*q.val+29*w+13, program.Runs t s (prepared s q.val) := by
  obtain ⟨k,hk,run⟩ := load_runs h
  have guard := check_runs h
  rw [decide_eq_true legal] at guard
  have branch := Routine.runs_popCase_true flag (.halt false) (.halt false) load.body
    (s := marked s true) (tail := s flag) (Function.update_self ..)
    (pop_marked s true ▸ run)
  rw [pop_marked] at branch
  exact ⟨_, by omega, guard.followedBy (b := .ofRoutine (Routine.popCase flag (.halt false) (.halt false) load.body)) branch⟩

/-- The invalid branch of the finite table contains a literal rejecting halt. -/
def rejection : program.State := .inr (.inr (.inr (.inl ())))

/-- The rejection occurs inside the routine and survives linking its normal return
to an arbitrary continuation. -/
theorem rejection_code : program.body.code rejection = .halt false := rfl

/-- For an over-cap or out-of-range interval, the guard reaches the rejecting label
after exactly the comparison and one flag pop. No unary expansion is performed. -/
theorem invalid_runs {w : ℕ} {a q c : Word w} {s : Stacks Port} (h : Ready a q c s)
    (bad : ¬ (q.val ≤ c.val ∧ a.val + q.val ≤ 2^w)) :
    StackRuns program.body.standalone (18*w+9) (some program.body.entry) s (some rejection) s := by
  have guard := check_runs h
  rw [decide_eq_false bad] at guard
  let branch := Routine.popCase flag (.halt false) (.halt false) load.body
  have lead := guard.link program.body Sum.inl (some (.inr branch.entry)) (fun _ => rfl)
  let dest : Option Bool → Option program.State
    | none => some (.inr (.inr (.inl ())))
    | some false => some rejection
    | some true => some (.inr (.inr (.inr (.inr load.body.entry))))
  have row : program.body.standalone (some (.inr branch.entry)) = .pop flag dest := by
    change StackOp.pop flag _ = StackOp.pop flag dest
    congr 1
    funext b
    rcases b with _ | (_ | _) <;> rfl
  have step : StackStep program.body.standalone (some (.inr branch.entry)) (marked s false)
      (some rejection) s := by
    simpa only [marked, Function.update_self, List.head?_cons, List.tail_cons, Function.update_idem,
      Function.update_eq_self, dest] using (StackStep.pop (s := marked s false) row)
  exact lead.trans (.cons step (.nil ..))

/-- Invalid inputs halt with no obligation on a subsequent routine. The clock includes
the rejecting instruction as well as the comparison and pop. -/
theorem invalid_allStops {w : ℕ} {a q c : Word w} {s : Stacks Port} (h : Ready a q c s)
    (bad : ¬ (q.val ≤ c.val ∧ a.val + q.val ≤ 2^w)) (cont : ℕ → Stacks Port → Prop) (fuel : ℕ) :
    program.body.AllStops cont (fuel+(18*w+10)) s := by
  have guard := check_runs h
  rw [decide_eq_false bad] at guard
  change (check.body.followedBy _).AllStops _ _ _
  rw [Routine.allStops_followedBy, show fuel+(18*w+10) = (fuel+2)+(18*w+8) by omega,
    guard.allStops_iff]
  change (Routine.popCase flag (.halt false) (.halt false) load.body).AllStops cont (fuel+2) (marked s false)
  simp [Routine.AllStops, Routine.AllStopsFrom, Routine.popCase, marked, Routine.halt,
    Routine.install, StackOp.rename]

end TeamBurstEntry

end BorderVNP
end Computability
end OAI
