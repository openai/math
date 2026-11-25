import OAI.Computability.BorderVNP.RoutingISACallProof
import OAI.Computability.BorderVNP.CellStackTape
import OAI.Computability.BorderVNP.TeamPrivateClock

/-!
# Private cell bytecode at directory call sites

Slot zero runs the three-stack bytecode interpreter on the little-endian bits of
the words fetched at the owned row. Its finite multitape table uses two native
transitions per continuing stack instruction. A directory return retains a
bounded path of this table for every owned row, including zero-weight halts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM TeamPrivateTape TeamPrivateFragment

namespace PrivateCell

/-- One symbol tape per stack of the cell bytecode interpreter. -/
abbrev tapeCount := Fintype.card CellMacro.Port

/-- One bit plane for each of blank, zero and one in the one-hot encoding. -/
abbrev symbolWidth := Fintype.card (Option Bool)

/-- The physical tape numbers of the three stack ports. -/
noncomputable def ports := Fintype.equivFin CellMacro.Port

/-- Blank is distinct from both input digits. -/
noncomputable def alphabet : Alphabet (Option Bool) symbolWidth := Alphabet.ofFintype none

/-- The fixed native table decoding the signed bytecode. -/
noncomputable def table := CellMacro.StackTape.table ports CellMacro.code CellMacro.negative

/-- The interpreter starts at fetch with all guards passing and positive sign. -/
def start : CellMacro.StackTape.Control CellMacro.State tapeCount :=
  .ready (⟨true, false⟩, .fetch)

/-- The native clock pays twice the stack budget bound on the serialized word interval. -/
def fuel (w len : ℕ) := 2 * (5 * (len * w) + 2)

/-- A path accepted by the private compiler with these fixed tape dimensions. -/
abbrev CompilerPath (w : ℕ) :=
  TeamPrivateClock.Path (CellMacro.StackTape.Control CellMacro.State tapeCount)
    (Option Bool) tapeCount symbolWidth w

/-- The bit planes installed at native entry for a given RAM burst. -/
noncomputable def initial {w : ℕ} (words : List (Word w)) :=
  tracks alphabet (input alphabet.blank some (ports .stream) (TeamPrivateCall.inputBits words))

/-- Signed replay of the private routine on the words delivered by the call opcode. -/
noncomputable def interpret {w : ℕ} (words : List (Word w)) (bits : List Bool) : Option TeamRAM.Sign :=
  (TeamPrivateCall.evaluate (trackTable alphabet table) (fuel w words.length) start
    (initial words) bits).map fun result => TeamPrivateCall.sign result.1

/-- Install the cell validator in slot zero of the RAM's private routines. -/
noncomputable def install {w : ℕ} (routines : TeamOpcode.Macros w 8) : TeamOpcode.Macros w 8 :=
  Function.update routines 0 interpret

/-- On a burst of its declared length, the installed opcode is precisely the
finite-alphabet call with the clock computed from the actual width and length. -/
theorem advance {w : ℕ} {S : Type*} (a : Word w) (len : ℕ) (next : S)
    (words : List (Word w)) (bits : List Bool) :
    (TeamRAM.Instr.call a len interpret next).advance bits words =
      (TeamPrivateCall.call alphabet some (ports .stream) table start (fuel w len)
        a len next).advance bits words := by
  by_cases h : words.length = len <;>
    simp [TeamRAM.Instr.advance, TeamPrivateCall.call, interpret, initial, h]

/-- Slot zero returns exactly the sign of a native path on the supplied words. -/
theorem interpret_iff {w : ℕ} (words : List (Word w)) (bits : List Bool) (s : TeamRAM.Sign) :
    interpret words bits = some s ↔ ∃ t < fuel w words.length, ∃ o u,
      TeamPrivateFragment.Run (trackTable alphabet table) t start (initial words) bits o u ∧
        TeamPrivateCall.sign o = s := by
  have spec := TeamPrivateCall.call_advance_iff alphabet some (ports .stream) table start
    (fuel w words.length) (0 : Word w) words.length () words bits s
  rw [← advance] at spec
  simpa [TeamRAM.Instr.advance, initial] using spec

/-- On a burst containing a complete bytecode stream the native clock suffices
for all branches and the native signed multiplicity is the bytecode value. -/
theorem bytecode_value {w : ℕ} (words : List (Word w)) (ops : List CellMacro.Op)
    (encoding : TeamPrivateCall.inputBits words = CellMacro.stream ops) :
    TeamPrivateValue.Stops (trackTable alphabet table) (fuel w words.length) start (initial words) ∧
      paths (trackTable alphabet table) (fuel w words.length) start (initial words) =
        CellMacro.value ops ⟨true, false⟩ [] := by
  let clock := 5 * (words.length * w) + 2
  have budget : CellMacro.budget ops ≤ clock := by
    simpa only [← encoding, TeamPrivateCall.inputBits_length] using CellMacro.budget_le ops
  have vm := CellMacro.execute ops ⟨true, false⟩ [] clock budget
  let ts := input (none : Option Bool) some (ports .stream) (TeamPrivateCall.inputBits words)
  have stack : CellMacro.StackTape.values ports ts = CellMacro.bank (CellMacro.stream ops) [] [] := by
    rw [CellMacro.StackTape.values_input, encoding]
    funext k
    cases k <;> simp [CellMacro.bank]
  have sim := CellMacro.StackTape.simulation ports CellMacro.code CellMacro.negative clock
    (⟨true, false⟩, .fetch) ts
  rw [stack] at sim
  exact ⟨(TeamPrivateValue.track_stops_iff ..).2 (sim.1.2 vm.1),
    (track_paths alphabet table _ start ts).trans (sim.2.trans vm.2)⟩

end PrivateCell

variable {w : ℕ}

/-- A path starts on the increasing-address burst of its own directory row. -/
structure Frame.PrivatePath (f : Frame) (m : Memory w) (i : ℕ) where
  /-- Native transitions before the final halt check. -/
  time : ℕ
  /-- Time must leave one clock tick for that check. -/
  within : time < PrivateCell.fuel w (m (f.address i + 2)).val
  /-- Exact choices of this path, including guesses with equal successor states. -/
  choices : List Bool
  /-- Rejection or a signed accepting halt. -/
  sign : Option Bool
  /-- The binary tracks at the halt. -/
  finalTapes : Fin (PrivateCell.tapeCount * PrivateCell.symbolWidth) → Track
  /-- Execution of the fixed cell table on this row's live argument words. -/
  run : TeamPrivateFragment.Run (trackTable PrivateCell.alphabet PrivateCell.table) time
    PrivateCell.start (PrivateCell.initial (TeamRAM.previous m (f.burst m i))) choices sign finalTapes

/-- A native choice string fixes the running time, return sign and final tape state. -/
theorem unique_run {Q : Type*} {d : ℕ} {P : Table Q d} {t n q bs o u}
    (a : Run P n q t bs o u) {n' o' u'} (b : Run P n' q t bs o' u') :
    n = n' ∧ o = o' ∧ u = u' := by
  induction a generalizing n' o' u' with
  | stop h =>
    cases b <;> rename_i h' <;> simp_all
  | one h _ ih =>
    cases b with
    | stop h' => simp_all
    | one h' b =>
      rw [h] at h'
      cases h'
      exact (ih b).imp_left (congrArg Nat.succ)
    | two _ h' _ => simp_all
  | two bit h _ ih =>
    cases b with
    | one h' _ => simp_all
    | two _ h' b =>
      rw [h] at h'
      cases h'
      exact (ih b).imp_left (congrArg Nat.succ)

/-- Fixing the private choice string fixes the native time, signed halt and final tapes. -/
theorem Frame.PrivatePath.eq_of_choices {w : ℕ} {f : Frame} {m : Memory w} {i : ℕ}
    (a b : f.PrivatePath m i) (h : a.choices = b.choices) : a = b := by
  obtain ⟨n, hn, bs, o, u, ha⟩ := a
  obtain ⟨n', hn', bs', o', u', hb⟩ := b
  change bs = bs' at h
  subst bs'
  obtain ⟨rfl, rfl, rfl⟩ := unique_run ha hb
  rfl

/-- The exact private event payload recorded by the outer RAM. -/
def Frame.PrivatePath.outcome {f : Frame} {m : Memory w} {i : ℕ} (p : f.PrivatePath m i) : Outcome :=
  (p.choices, TeamPrivateCall.sign p.sign)

/-- The native path, with its read words, is also a replayable path of the
private two-tape compiler and carries its elementary replay cost. -/
noncomputable def Frame.PrivatePath.toPath {f : Frame} {m : Memory w} {i : ℕ}
    (p : f.PrivatePath m i) : PrivateCell.CompilerPath w :=
  ⟨PrivateCell.alphabet, some, PrivateCell.ports .stream, PrivateCell.table, PrivateCell.start,
    TeamRAM.previous m (f.burst m i), p.time, p.choices, p.sign, p.finalTapes, p.run⟩

/-- An owned row needs a fitting interval and a typed private execution on precisely
that interval. A nonowner skips the row. -/
theorem Frame.valid_private_iff (f : Frame) (m : Memory w) (routines : TeamOpcode.Macros w 8)
    (i : ℕ) (x : Option Outcome) :
    f.Valid m (PrivateCell.install routines) i x ↔
      if (m (f.address i)).val = f.team then
        (m (f.address i + 1)).val + (m (f.address i + 2)).val ≤ 2^w ∧
          ∃ p : f.PrivatePath m i, x = some p.outcome
      else x = none := by
  unfold Valid
  split
  · have len : (TeamRAM.previous m (f.burst m i)).length = (m (f.address i + 2)).val := by
      simp [burst, TeamRAM.previous]
    simp only [PrivateCell.install, Function.update_self, PrivateCell.interpret_iff, len]
    constructor
    · rintro ⟨⟨bits, s⟩, rfl, fits, t, ht, o, u, hr, hs⟩
      exact ⟨fits, ⟨t, ht, bits, o, u, hr⟩, congrArg (fun z => some (bits, z)) hs.symm⟩
    · rintro ⟨fits, p, rfl⟩
      exact ⟨p.outcome, rfl, fits, p.time, p.within, p.sign, p.finalTapes, p.run, rfl⟩
  · rfl

/-- Consecutive rows carry their own path types. Only the owning team can
construct a call, and a skipped row carries no private choices. -/
inductive Frame.PrivatePaths (f : Frame) (m : Memory w) : ℕ → List (Option Outcome) → Type
  | nil (i : ℕ) : f.PrivatePaths m i []
  | skip {i xs} (other : (m (f.address i)).val ≠ f.team) (tail : f.PrivatePaths m (i+1) xs) :
      f.PrivatePaths m i (none :: xs)
  | call {i xs} (owner : (m (f.address i)).val = f.team)
      (fits : (m (f.address i + 1)).val + (m (f.address i + 2)).val ≤ 2^w)
      (path : f.PrivatePath m i) (tail : f.PrivatePaths m (i+1) xs) :
      f.PrivatePaths m i (some path.outcome :: xs)

private theorem privatePaths_heq {w : ℕ} {f : Frame} {m : Memory w} {i : ℕ} {xs ys}
    (p : f.PrivatePaths m i xs) (q : f.PrivatePaths m i ys) (h : xs = ys) : HEq p q := by
  induction p generalizing ys with
  | nil =>
    cases q with
    | nil => rfl
    | skip | call => cases h
  | skip other tail ih =>
    cases q with
    | nil | call => cases h
    | skip _ tail' =>
      obtain ⟨_, he⟩ := List.cons.inj h
      cases he
      cases eq_of_heq (ih tail' rfl)
      rfl
  | call owner fits p tail ih =>
    cases q with
    | nil | skip => cases h
    | call _ _ p' tail' =>
      obtain ⟨he, htail⟩ := List.cons.inj h
      have hp := p.eq_of_choices p' (congrArg Prod.fst (Option.some.inj he))
      subst p'
      cases htail
      cases eq_of_heq (ih tail' rfl)
      rfl

/-- An outcome list fixes every private path, so typed replay introduces no multiplicity. -/
instance {w : ℕ} {f : Frame} {m : Memory w} {i : ℕ} {xs} : Subsingleton (f.PrivatePaths m i xs) :=
  ⟨fun p q => eq_of_heq (privatePaths_heq p q rfl)⟩

/-- The owned rows yield the list of private compiler paths in call order. -/
noncomputable def Frame.PrivatePaths.calls {f : Frame} {m : Memory w} {i : ℕ} {xs} :
    f.PrivatePaths m i xs → List (PrivateCell.CompilerPath w)
  | .nil _ => []
  | .skip _ tail => tail.calls
  | .call _ _ p tail => p.toPath :: tail.calls

/-- The replayable paths have exactly the payloads of the owned rows. -/
theorem Frame.PrivatePaths.calls_outcomes {f : Frame} {m : Memory w} {i : ℕ} {xs}
    (ps : f.PrivatePaths m i xs) :
    ps.calls.map (fun p => (p.choices, TeamPrivateCall.sign p.sign)) = xs.filterMap id := by
  induction ps with
  | nil => rfl
  | skip _ _ ih => exact ih
  | call _ _ p _ ih => exact congrArg (List.cons p.outcome) ih

/-- Directory admission at any starting index is equivalent to a row-indexed
list of paths of the actual native table. -/
theorem Frame.admitted_private_iff (f : Frame) (m : Memory w) (routines : TeamOpcode.Macros w 8)
    (i : ℕ) (xs : List (Option Outcome)) :
    f.Admitted m (PrivateCell.install routines) i xs ↔ Nonempty (f.PrivatePaths m i xs) := by
  induction xs generalizing i with
  | nil => exact ⟨fun _ => ⟨.nil i⟩, fun _ => trivial⟩
  | cons x xs ih =>
    rw [Admitted, f.valid_private_iff, ih]
    constructor
    · rintro ⟨valid, ⟨tail⟩⟩
      split at valid
      · rename_i owner
        obtain ⟨fits, p, rfl⟩ := valid
        exact ⟨.call owner fits p tail⟩
      · rename_i other
        subst x
        exact ⟨.skip other tail⟩
    · rintro ⟨ps⟩
      cases ps with
      | skip other tail => exact ⟨by simp [other], ⟨tail⟩⟩
      | call owner fits p tail => exact ⟨by simpa only [owner, ite_true] using And.intro fits ⟨p, rfl⟩, ⟨tail⟩⟩

/-- The native directory executable returns exactly the event histories of these
row-indexed paths on the live argument words. -/
theorem execute_private_directory_iff {pub : Arg → Word w} (routines : TeamOpcode.Macros w 8)
    {s : Bank w} {m : Memory w} (frameFit : (pub 0).val + 15 < 2^w)
    (space : (Frame.ofMemory pub m).base + 3*(Frame.ofMemory pub m).count ≤ 2^w) {bits es} :
    TeamRAM.execute (callOwnedCells.program.fetch pub (PrivateCell.install routines)) ⟨0,s⟩ m bits = some es ↔
      es.map TeamRAM.Event.choices = bits ∧ ∃! xs : List (Option Outcome),
        xs.length = (Frame.ofMemory pub m).count ∧ Nonempty ((Frame.ofMemory pub m).PrivatePaths m 0 xs) ∧
        es = setupTrace pub m ++ (Frame.ofMemory pub m).scanTrace m 0 xs := by
  simpa only [Frame.admitted_private_iff] using
    (execute_directory_iff (s := s) (macros := PrivateCell.install routines) (bits := bits) (es := es) frameFit space)

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
