import OAI.Computability.VPVNP.RAMTapeCeilLog
import OAI.Computability.VPVNP.RAMTapeSortOffsets
import OAI.Computability.VPVNP.RAMTapeSortSchedule
import OAI.Computability.VPVNP.RAMTapeValidatorSetup

/-! # Preparing the bitonic sorter from the site's public registers

The initialized site already holds its word width and its number of slots,
`4H`, in unary. Copy the latter and halve the copy until only one mark remains.
This writes the row width `h = log₂(4H)`. The phase loop receives `h+d` marks
from the row and site widths. Both original dimensions remain available to the
record reader, and the temporary stacks finish empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortStartup

/-- Registers for the site address width, slot count, logarithm calculation, row width, and
remaining phase count. -/
inductive Port where | address | slots | copy | tmp | rowWidth | remaining
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

private abbrev marks (n : ℕ) := List.replicate n true

private def counts (d N copy h rem : ℕ) : Tally.State Port
  | .address => d
  | .slots => N
  | .copy => copy
  | .rowWidth => h
  | .remaining => rem
  | .tmp => 0

/-- Encode the supplied dimensions, working copy, row width, and remaining phase count as unary
stacks. -/
def bank (d N copy h rem : ℕ) : Stacks Port := Tally.encode (counts d N copy h rem)

private def copyAdd (src dst : Port) : FiniteRoutine Port :=
  FiniteRoutine.ofRoutine (Tally.copyAdd src dst Port.tmp)

private def logPorts : CeilLog.Port → Port
  | .src => .copy
  | .tmp => .tmp
  | .out => .rowWidth

private def rowWidth : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (CeilLog.code 1) logPorts .scan (· == .done)

/-- A fixed control, with the slot count and both widths held on actual stacks. -/
def routine : FiniteRoutine Port :=
  (((copyAdd .slots .copy).followedBy rowWidth).followedBy
    (copyAdd .rowWidth .remaining)).followedBy (copyAdd .address .remaining)

/-- Number of startup steps for copying the slot count, computing its ceiling binary logarithm,
and assembling the phase count. -/
def cost (d N : ℕ) : ℕ := (5*N+2)+CeilLog.cost 1 N+(5*Nat.clog 2 N+2)+(5*d+2)

private theorem logarithm_run (d N : ℕ) :
    rowWidth.Runs (CeilLog.cost 1 N) (bank d N N 0 0) (bank d N 0 (Nat.clog 2 N) 0) := by
  apply FiniteRoutine.runs_ofStackCode_framed
    (by intro x y h; cases x <;> cases y <;> simp_all [logPorts]) rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) (CeilLog.runs 1 N [])
  · intro p; cases p <;> rfl
  · intro p; cases p <;> simp [logPorts, bank, Tally.encode, counts, CeilLog.store]
  · intro p hp; cases p <;> first | rfl | exact (hp .out rfl).elim | exact (hp .src rfl).elim

/-- Only the two new output registers change, even for a non-power-of-two slot count. -/
theorem runs (d N : ℕ) :
    routine.Runs (cost d N) (bank d N 0 0 0) (bank d N 0 (Nat.clog 2 N) (Nat.clog 2 N+d)) := by
  let h := Nat.clog 2 N
  have c₁ := Tally.copyAdd_runs Port.slots .copy .tmp (by decide) (by decide) (by decide)
    (counts d N 0 0 0) rfl
  have c₂ := Tally.copyAdd_runs Port.rowWidth .remaining .tmp (by decide) (by decide) (by decide)
    (counts d N 0 h 0) rfl
  have c₃ := Tally.copyAdd_runs Port.address .remaining .tmp (by decide) (by decide) (by decide)
    (counts d N 0 h h) rfl
  have e₁ : Function.update (counts d N 0 0 0) .copy (0+N) = counts d N N 0 0 := by
    funext p; cases p <;> simp [counts, Function.update]
  have e₂ : Function.update (counts d N 0 h 0) .remaining (0+h) = counts d N 0 h h := by
    funext p; cases p <;> simp [counts, Function.update]
  have e₃ : Function.update (counts d N 0 h h) .remaining (h+d) = counts d N 0 h (h+d) := by
    funext p; cases p <;> rfl
  change (copyAdd .slots .copy).Runs (5*N+2) _ (Tally.encode (Function.update (counts d N 0 0 0) .copy (0+N))) at c₁
  change (copyAdd .rowWidth .remaining).Runs (5*h+2) _ (Tally.encode (Function.update (counts d N 0 h 0) .remaining (0+h))) at c₂
  change (copyAdd .address .remaining).Runs (5*d+2) _ (Tally.encode (Function.update (counts d N 0 h h) .remaining (h+d))) at c₃
  rw [e₁] at c₁
  rw [e₂] at c₂
  rw [e₃] at c₃
  exact ((c₁.followedBy (logarithm_run d N)).followedBy c₂).followedBy c₃

theorem cost_le (d N : ℕ) : cost d N ≤ 43*N+5*d+39 := by
  have hc := CeilLog.cost_le 1 N
  have hw : Nat.clog 2 N ≤ N := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := N)).le
  unfold cost
  omega

/-- A caller can map the output registers directly to the stage counter and the row
enumerator. Every stack outside these two outputs is restored. -/
theorem runs_framed {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    (d N : ℕ) (s : Stacks K) (hin : ∀ p, s (ports p) = bank d N 0 0 0 p) :
    (routine.onPorts ports).Runs (cost d N) s
      (Function.update (Function.update s (ports .rowWidth) (marks (Nat.clog 2 N)))
        (ports .remaining) (marks (Nat.clog 2 N+d))) := by
  apply FiniteRoutine.runs_onPorts_framed _ hp (runs d N) hin
  · intro p; cases p <;> simp [Function.update, hp.eq_iff, hin, bank, Tally.encode, counts, marks]
  · intro k hk; simp [Function.update, Ne.symm (hk .rowWidth), Ne.symm (hk .remaining)]

/-- Two temporary sorter startup stacks for the slot-count copy and the logarithm calculation. -/
inductive Scratch where | copy | tmp
  deriving DecidableEq

instance : Fintype Scratch := derive_fintype% _

/-- Combined register bank for schedule control, site setup, startup scratch, and sorting
offsets. -/
abbrev Registers := SortSchedule.Port ((SiteSetup.Port ⊕ Scratch) ⊕ SortOffsets.Port)
set_option synthInstance.maxSize 1024

/-- Embed a site setup register into the combined sorter register bank. -/
def caller (p : SiteSetup.Port) : Registers := .inr (.inl (.inl p))

/-- Wire each startup port to its address-width, slot-count, scratch, row-width, or schedule
register. -/
def ports : Port → Registers
  | .address => caller (.inl InputReader.addressWidthPort)
  | .slots => caller SiteSetup.slotsPort
  | .rowWidth => .inr (.inr .width)
  | .remaining => .inl .remaining
  | .copy => .inr (.inl (.inr .copy))
  | .tmp => .inr (.inl (.inr .tmp))

private theorem ports_injective : Function.Injective ports := by
  intro x y he
  cases x <;> cases y <;> simp_all [ports, caller, SiteSetup.slotsPort]

/-- Install the prepared site stacks in the idle sorter with the given row width and remaining
phase count and zero phase and stride. -/
def ready (s : Stacks SiteSetup.Port) (h rem : ℕ) : Stacks Registers :=
  SortSchedule.bank (SortOffsets.idle (Sum.elim s (fun _ => [])) h) rem 0 0

/-- Preserve all bit fields, including the staged records, word width, and slot count.
Only the outer schedule and the inner row traversal receive new marks. -/
theorem startup_runs (d e : ℕ) (s : Stacks SiteSetup.Port)
    (hd : s (.inl InputReader.addressWidthPort) = marks d)
    (hs : s SiteSetup.slotsPort = marks (4*2^e)) :
    (routine.onPorts ports).Runs (cost d (4*2^e)) (ready s 0 0) (ready s (2+e) (2+e+d)) := by
  have hpow : 4*2^e = 2^(2+e) := by rw [pow_add]; rfl
  have hlog : Nat.clog 2 (4*2^e) = 2+e := hpow ▸ Nat.clog_pow 2 _ (by decide)
  apply FiniteRoutine.runs_onPorts_framed _ ports_injective (runs d (4*2^e))
  · intro p; cases p <;> first | rfl | exact hd | exact hs
  · intro p; cases p <;> first | rfl | exact hd | exact hs | simp [ready, ports, SortSchedule.bank,
      SortOffsets.idle, SortOffsets.store, SortOffsets.ones, bank, Tally.encode, counts, hlog]
  · rintro (c | (p | r)) hout
    · cases c <;> first | rfl | exact (hout .remaining rfl).elim
    · rfl
    · cases r <;> first | rfl | exact (hout .rowWidth rfl).elim

/-- On the initialized physical site, the sorter sees the same word and slot dimensions
as the record emitter, together with its own binary width and schedule length. -/
theorem from_prepared (d e : ℕ) (s : Stacks InputReader.Registers)
    (hd : s InputReader.addressWidthPort = marks d) :
    let state := SiteSetup.prepared s d (2^e)
    (routine.onPorts ports).Runs (cost d (4*2^e)) (ready state 0 0) (ready state (2+e) (2+e+d)) ∧
      ready state (2+e) (2+e+d) (caller SiteSetup.wordPort) = marks ((d+10)^4) ∧
      ready state (2+e) (2+e+d) (caller SiteSetup.slotsPort) = marks (4*2^e) :=
  ⟨startup_runs d e _ hd rfl, rfl, rfl⟩

end RAMTape.SortStartup

end VPVNP
end Computability
end OAI
