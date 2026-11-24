import OAI.Computability.VPVNP.RAMTapeSitePostBank
import OAI.Computability.VPVNP.RAMTapeSortStartup
import OAI.Computability.VPVNP.RAMTapeSortReplayInput

/-!
# Entering the sorting pass on a completed local record buffer

The site carries the public word and address widths, the unary slot count,
the completed block, the remaining incident suffix, and the two boundary
records. Two new unary counters initialize the sorting scheduler and its
row visits. All other data stay at their actual ports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

open BurstRAM RAMBoundary RAMSerialization RAMLayout Boundary

/-- Unary row-width counter holding the ceiling binary logarithm of the slot count. -/
def rowWidthPort : Port := .inl (.inr (.inl (.inr .width)))
/-- Unary count initialized to the sorting row width plus the site address width for the
schedule. -/
def remainingPort : Port := .inl (.inl .remaining)

/-- Connect sorting startup to the retained address width and slot count, its scratch ports,
and the two new scheduler counters. -/
def preparePorts : SortStartup.Port → Port
  | .address => addressWidthPort
  | .slots => slotsPort
  | .copy => .inl (.inl .phase)
  | .tmp => .inl (.inl .tmp)
  | .rowWidth => rowWidthPort
  | .remaining => remainingPort

/-- Initialize the local sorting scheduler and row-width counter on the physical post-pass
bank. -/
def prepare : FiniteRoutine Port := SortStartup.routine.onPorts preparePorts

variable {d h w : ℕ}

/-- Stack bank before initialization, immediately after the record block
has been closed and the two successor fields have been extracted. -/
def prestate (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) (tail : List Bool) : Stacks Port :=
  Function.update (Function.update (initialBank v prev sent x tail) rowWidthPort []) remainingPort []

theorem prepare_runs (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) (tail : List Bool) :
    prepare.Runs (SortStartup.cost d (2^h)) (prestate v prev sent x tail) (initialBank v prev sent x tail) := by
  have hlog : Nat.clog 2 (2^h) = h := Nat.clog_pow _ _ (by decide)
  apply FiniteRoutine.runs_onPorts_framed _ (by decide : Function.Injective preparePorts) (SortStartup.runs d (2^h))
  · intro p; cases p <;> rfl
  · intro p; cases p <;> first | rfl | (simp only [SortStartup.bank, Tally.encode, hlog]; rfl)
  · intro p hp
    have hr := Ne.symm (hp .remaining)
    have hw' := Ne.symm (hp .rowWidth)
    change p ≠ remainingPort at hr
    change p ≠ rowWidthPort at hw'
    simp only [prestate, Function.update_of_ne hr, Function.update_of_ne hw']

/-- The actual nonempty ports at the handoff. The initial block and two
boundary records may contain arbitrary raw words. -/
theorem prestate_ports (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) (tail : List Bool) :
    let s := prestate v prev sent x tail
    s blockPort = blockBytes (List.ofFn x.1) ∧ s flagPort = x.2 ∧
      s addressPort = BurstRAM.wordBits v ∧ s widthPort = List.replicate w true ∧
      s slotsPort = List.replicate (2^h) true ∧ s incidentPort = tail ∧
      s previousPort = recordBytes prev ∧ s sentPort = recordBytes sent ∧
      s addressWidthPort = List.replicate d true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An untyped view of the call-to-sort handoff, for installing these ports
into the surrounding processor. The other stacks start empty. -/
def rawBank (d w slots : ℕ) (address block tail flags prev sent : List Bool) : Stacks Port
  | .inl (.inr (.inl (.inl (.inl .current)))) => block
  | .inl (.inr (.inl (.inl (.inl .crossReceive)))) => tail
  | .inl (.inr (.inl (.inl (.inl .flags)))) => flags
  | .inl (.inr (.inl (.inl (.inl .width)))) => List.replicate w true
  | .inl (.inr (.inl (.inl (.inr .site)))) => address
  | .inl (.inr (.inr ())) => List.replicate slots true
  | .inr .previous => prev
  | .inr .sent => sent
  | .inr .addressWidth => List.replicate d true
  | _ => []

theorem prestate_eq_raw (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) (tail : List Bool) :
    prestate v prev sent x tail = rawBank d w (2^h) (BurstRAM.wordBits v)
      (blockBytes (List.ofFn x.1)) tail x.2 (recordBytes prev) (recordBytes sent) := by
  funext p
  rcases p with (c | (((r|e)|o)|u)) | extra
  · cases c <;> rfl
  · cases r <;> rfl
  · cases e <;> rfl
  · cases o <;> rfl
  · cases u; rfl
  · cases extra <;> rfl

/-- The sorter shares the predecessor and successor record ports with
the terminal scan through the surrounding bank. -/
def prepareSort : FiniteRoutine Port := prepare.followedBy (SortStages.program.onPorts Sum.inl)

theorem prepareSort_run {H : ℕ} (hw : 2 ≤ w) (hslots : 2^h = 4*H)
    (incident : Fin (width d H w) → Bool) (raw : ℕ → Bool) (hraw : ∀ j : Fin (width d H w), raw j.val = incident j)
    (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State h w) :
    ∃ t ≤ SortStartup.cost d (2^h)+SortStages.ticks h d w,
      prepareSort.Runs t (prestate v prev sent x ((List.ofFn incident).drop (16*w)))
        (finalBank v prev sent (SortStages.result raw v x)) := by
  obtain ⟨t, ht, hr⟩ := SortStages.run_incident hw hslots incident raw hraw v x
  have sort : (SortStages.program.onPorts Sum.inl).Runs t
      (initialBank v prev sent x ((List.ofFn incident).drop (16*w)))
      (finalBank v prev sent (SortStages.result raw v x)) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hr
    · intro k; rfl
    · intro k; rfl
    · rintro (i|e) he
      · exact (he i rfl).elim
      · rfl
  exact ⟨_, Nat.add_le_add_left ht _, (prepare_runs v prev sent x _).followedBy sort⟩

/-- Use exactly the five-word encodings left by the record emitter. -/
theorem prepareSort_emitted {e : ℕ} (hw : 2 ≤ w) (incident : Fin (width d (2^e) w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ j : Fin (width d (2^e) w), raw j.val = incident j)
    (v : Word d) (prev sent : RawSlot w) (records : List (WordRecord w)) (flags : List Bool) :
    let x : SortReplay.State (2+e) w := (SortReplay.emittedBlock hw e records, flags)
    ∃ t ≤ SortStartup.cost d (4*2^e)+SortStages.ticks (2+e) d w,
      prepareSort.Runs t (prestate v prev sent x ((List.ofFn incident).drop (16*w)))
        (finalBank v prev sent (SortStages.result raw v x)) := by
  intro x
  simpa only [record_width] using prepareSort_run hw (record_width e) incident raw hraw v prev sent x


open RAMSort

/-- Starting at the call-to-sort handoff, execute the scheduler and retain
the two physical boundary records for the final predecessor check. -/
theorem prepareSort_messages {e : ℕ} (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (b : SendArrays d (2^e) w) (v : Word d) (prev sent : RawSlot w) (x : SortReplay.State (2+e) w)
    (hcanon : SortReplay.CanonicalBlock hw x.1) :
    let incident := fun j => (incidentEquiv d (2^e) w b).val (v, (offset d (2^e) w).symm j)
    let ss := phases ((2+e)+d) ((2+e)+d) le_rfl
    let mem := (unpackMessages (parseMessages hw hc b)).memory
    ∃ t ≤ SortStartup.cost d (4*2^e) + SortStages.ticks (2+e) d w, ∃ y : SortReplay.State (2+e) w,
      prepareSort.Runs t (prestate v prev sent x ((List.ofFn incident).drop (16*w))) (finalBank v prev sent y) ∧
      y.2.length ≤ x.2.length + 2*2^(2+e)*(((2+e)+d+1).choose 2) ∧
      (y.2.all id = true ↔ x.2.all id = true ∧ SortCanonical hw hc b v ∧
        RAMSort.checks v ss (physicalFieldsEquiv.{0,0} (2+e) d _ mem.sortSends) (SortReplay.decoded hw x.1)) ∧
      (y.2.all id = true → (fun i => (parsedSlot hw (y.1 i)).record) =
        outputAt mem v (SortReplay.decoded hw x.1)) := by
  intro incident ss mem
  have hraw (k : Fin (width d (2^e) w)) : sortIncident b v k.val = incident k := readIncident_at _ k
  obtain ⟨t, ht, hr⟩ := prepareSort_run hw (record_width e) incident (sortIncident b v) hraw v prev sent x
  rw [record_width] at ht
  exact ⟨t, ht, SortStages.result (sortIncident b v) v x, hr, SortStages.result_flags_length _ _ _,
    SortReplay.fold_messages hw hc b v x hcanon, SortReplay.fold_messages_output hw hc b v x hcanon⟩

end RAMTape.SitePost

end VPVNP
end Computability
end OAI
