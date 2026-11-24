import OAI.Computability.VPVNP.PairSimulationLeafCount
import OAI.Computability.VPVNP.PairSimulationStackNativeCalls
import OAI.Computability.VPVNP.PairSimulationHistory

/-!
# Native stack nominations at cursor leaves

The virtual validator first nominates a finite private stream, then checks
it. The binary instructions of this nomination program have their own
complete words. The reader below consumes those actual instruction choices.
At a leaf each accepted occurrence has exponent zero, so a bijection of
finite choices transports its contribution to the original cursor factor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape CompressorRecords

variable {K Q : Type*} [DecidableEq K]

private theorem consumed {code : StackCode K Q} {fuel : ℕ} {q : Q} {s : Stacks K}
    {bits rest : List Bool} (h : acceptPrefix code fuel q s bits = some rest) :
    acceptPrefix code fuel q s (bits.take (bits.length - rest.length)) = some [] ∧
      bits = bits.take (bits.length - rest.length) ++ rest := by
  obtain ⟨pre, hpre, rfl⟩ := (acceptPrefix_iff ..).mp h
  simp only [List.length_append, Nat.add_sub_cancel, List.take_left]
  exact ⟨(acceptPrefix_iff ..).mpr ⟨pre, hpre, (List.append_nil _).symm⟩, trivial⟩

/-- Parse the actual stack nomination bits and return the exact consumed
word as the occurrence, keeping the unconsumed suffix for the next leaf. -/
def completeReader (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K) :
    ChoiceReader (CompleteStreams code fuel q s) where
  encode x := x.val
  read bits :=
    match h : acceptPrefix code fuel q s bits with
    | none => none
    | some rest => some (⟨bits.take (bits.length - rest.length), (consumed h).1⟩, rest)
  read_iff bits x tail := by
    constructor
    · intro h
      split at h
      · contradiction
      · rename_i rest hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact (consumed hr).2
    · intro h
      have mem : x.val ∈ acceptedWords code fuel q s := by
        simpa [acceptPrefix_iff] using x.prop
      have read := (acceptPrefix_iff code fuel q s bits tail).mpr ⟨x.val, mem, h⟩
      split
      · rename_i fail
        rw [read] at fail
        contradiction
      · rename_i rest hit
        obtain rfl := Option.some.inj (hit.symm.trans read)
        apply congrArg some
        refine Prod.ext ?_ rfl
        apply Subtype.ext
        change bits.take (bits.length - rest.length) = x.val
        simp [h]

/-- Projecting away the occurrence recovers the stack interpreter's
actual remaining input. -/
theorem completeReader_suffix (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K)
    (bits : List Bool) :
    ((completeReader code fuel q s).read bits).map Prod.snd = acceptPrefix code fuel q s bits := by
  unfold completeReader
  dsimp only
  split <;> simp_all

private theorem reindex_suffix {α β : Type*} (C : ChoiceReader α) (e : α ≃ β) (bits : List Bool) :
    ((C.reindex e).read bits).map Prod.snd = (C.read bits).map Prod.snd := by
  cases h : C.read bits <;> simp [ChoiceReader.reindex, h]

theorem completeReader_length_lt (code : StackCode K Q) (fuel : ℕ) (q : Q) (s : Stacks K)
    (x : CompleteStreams code fuel q s) : ((completeReader code fuel q s).encode x).length < fuel := by
  have step {t : ℕ} {q : Q} {s : Stacks K} {bits : List Bool} {y : Exit K Q}
      (h : parse code t q s bits = some y) : bits.length + y.unused < y.rest.length + t := by
    induction t generalizing q s bits with
    | zero => simp [parse] at h
    | succ t ih =>
      cases op : code q with
      | push | pop | goto =>
        have := ih (by simpa only [parse, op] using h)
        omega
      | choose low high =>
        cases bits with
        | nil => simp [parse, op] at h
        | cons b bits =>
          have := ih (by simpa only [parse, op] using h)
          simp only [List.length_cons]
          omega
      | halt status =>
        simp only [parse, op, Option.some.injEq] at h
        subst y
        dsimp only
        omega
  have ok := x.prop
  unfold acceptPrefix haltPrefix at ok
  split at ok
  · contradiction
  · rename_i y hy
    have bound := step hy
    split at ok
    · simp only [Option.some.injEq] at ok
      rw [ok, List.length_nil, Nat.zero_add] at bound
      change x.val.length < fuel
      omega
    · contradiction

end PairSimulation.StackMachine

namespace PairSimulation.LeafStartup

open BurstRAM BurstRAM.PrivateRAM RAMTape CursorNetwork CursorRouting CompressorRecords
open StackMachine

set_option synthInstance.maxSize 10000

/-- The validator has direct accepting/rejecting halts. A normal fall-through
of this closed stack program rejects. -/
def auxiliaryProcessor : FiniteRoutine (Port 52 34) := processor 52 PrimedCounter.Program.table

/-- The closed stack program for the auxiliary validator, with rejection on ordinary
fall-through. -/
def auxiliaryCode : StackCode (Port 52 34) (Option auxiliaryProcessor.State) :=
  auxiliaryProcessor.body.close false

/-- The initial control state of the closed auxiliary stack program. -/
def auxiliaryEntry : Option auxiliaryProcessor.State := some auxiliaryProcessor.body.entry

variable {w d e : ℕ} [NeZero d] {L : PrimedInputRAM.Lengths} {n a H s : ℕ}
  {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q s)
  (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
  (v : Position d) (buf : Buffers d (2 ^ e) w)

/-- The auxiliary validator's initial stacks built from the cursor position, four supplied
buffers, and primed counter's public operands. -/
noncomputable abbrev auxiliaryBank := bank 52 (auxiliary D hw hc v buf) D.pub

theorem auxiliary_closed (hz : v.1 = 0) (routed : routeAccept (2 ^ e) w v (readBuffer buf) = true)
    (t : ℕ) (bound : steps 52 (auxiliary D hw hc v buf) ≤ t) :
    stackPaths auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v buf) =
      Nat.card {bs : List Bool // initialAccept D.machine D.fuel 0 (D.initial v.2) hw hc v buf bs = true} ∧
      StopsWithin auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v buf) := by
  have spec := auxiliary_count D hw hc v buf hz routed t bound
  exact ⟨(Routine.stackPaths_close auxiliaryProcessor.body false t auxiliaryEntry _).trans (spec.1 _),
    (Routine.stopsWithin_close_iff auxiliaryProcessor.body false t auxiliaryEntry _).mpr (spec.2 _)⟩

variable {W p r k : ℕ} {M : Machine W p r k} {pc : Option auxiliaryProcessor.State → Fin 7 → Fin p}
  {reg : StackMachine.Register (Port 52 34) ↪ Fin r} {done : Fin p} {storage : StackMachine.Layout (Port 52 34) W}

/-- Execution on the actual bank built from the auxiliary public operands
and four independent half-wire buffers. Every true halt goes to the
linked native continuation with its suffix and framed private memory. -/
theorem auxiliary_native (hz : v.1 = 0) (routed : routeAccept (2 ^ e) w v (readBuffer buf) = true)
    (t : ℕ) (bound : steps 52 (auxiliary D hw hc v buf) ≤ t)
    (linked : StackMachine.Linked M auxiliaryCode pc reg done) (hW : 0 < W)
    (fit : ∀ j, (auxiliaryBank D hw hc v buf j).length + t ≤ storage.capacity)
    (c : Config W p r) (atPC : c.pc = pc auxiliaryEntry 0)
    (rep : Represents storage reg c (auxiliaryBank D hw hc v buf))
    (extra : ℕ) (m : Memory W) (bits : List Bool) :
    NativeCall M storage reg done extra (4 * t) c m bits
      (parse auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v buf) bits) := by
  have stops := (auxiliary_closed D hw hc v buf hz routed t bound).2
  exact parse_native linked hW (fun _ _ path j => reachable_capacity stops fit path j) t extra (.inr stops) c atPC rep m bits

/-- The instantiated, accepting native burst counts exactly the choices
of the original cursor on these supplied buffers. -/
theorem auxiliary_native_card (hz : v.1 = 0) (routed : routeAccept (2 ^ e) w v (readBuffer buf) = true)
    (t : ℕ) (bound : steps 52 (auxiliary D hw hc v buf) ≤ t)
    (linked : StackMachine.Linked M auxiliaryCode pc reg done) (close : M.code done = .accept) (hW : 0 < W)
    (fit : ∀ j, (auxiliaryBank D hw hc v buf j).length + t ≤ storage.capacity)
    (c : Config W p r) (atPC : c.pc = pc auxiliaryEntry 0)
    (rep : Represents storage reg c (auxiliaryBank D hw hc v buf)) (extra : ℕ) (m : Memory W) :
    Nat.card {bs : List Bool // (execute M.program (extra + 4 * t) c m bs).isSome = true} =
      Nat.card {bs : List Bool // initialAccept D.machine D.fuel 0 (D.initial v.2) hw hc v buf bs = true} := by
  obtain ⟨count, stops⟩ := auxiliary_closed D hw hc v buf hz routed t bound
  exact (nativeStreams_card linked close hW (fun _ _ path j => reachable_capacity stops fit path j) t extra
    (.inr stops) c atPC rep m).trans count

variable (z : (validatorNetwork d e w).Half v)

/-- Occurrences at a leaf carry zero exponent. A finite bijection transfers
the validated stack nomination multiplicity to the initial cursor factor. -/
noncomputable def nominationEquiv (hz : v.1 = 0)
    (routed : routeAccept (2 ^ e) w v (readBuffer (halfBuffers v z)) = true) (t : ℕ)
    (bound : steps 52 (auxiliary D hw hc v (halfBuffers v z)) ≤ t) :
    CompleteStreams auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v (halfBuffers v z)) ≃
      initialChoices D.machine D.fuel 0 D.initial hw hc v z := by
  apply Fintype.equivOfCardEq
  rw [completeStreams_card, ← Nat.card_eq_fintype_card]
  exact (auxiliary_closed D hw hc v (halfBuffers v z) hz routed t bound).1.trans
    (Nat.card_congr (initialAcceptEquiv D.machine D.fuel 0 D.initial hw hc v z))

/-- At cursor zero read the actual stack program's choices. A valid transit
site uses the empty word and a failed routing test rejects before nomination. -/
noncomputable def nominationReader (t : ℕ) (bound : steps 52 (auxiliary D hw hc v (halfBuffers v z)) ≤ t) :
    ChoiceReader (initialChoices D.machine D.fuel 0 D.initial hw hc v z) :=
  if h : v.1 = 0 ∧ routeAccept (2 ^ e) w v (readBuffer (halfBuffers v z)) = true then
    (completeReader auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v (halfBuffers v z))).reindex
      (nominationEquiv D hw hc v z h.1 h.2 t bound)
  else LocalHistory.initialReader D.machine D.fuel 0 hw hc D.initial v z

/-- On every local input the reader returns exactly the suffix left by the
native nomination parser, the deterministic transit, or the failed guard. -/
theorem nominationReader_suffix (t : ℕ)
    (bound : steps 52 (auxiliary D hw hc v (halfBuffers v z)) ≤ t) (bits : List Bool) :
    ((nominationReader D hw hc v z t bound).read bits).map Prod.snd =
      if routeAccept (2 ^ e) w v (readBuffer (halfBuffers v z)) then
        if v.1 = 0 then
          acceptPrefix auxiliaryCode t auxiliaryEntry (auxiliaryBank D hw hc v (halfBuffers v z)) bits
        else some bits
      else none := by
  unfold nominationReader
  by_cases route : routeAccept (2 ^ e) w v (readBuffer (halfBuffers v z)) = true
  · by_cases zero : v.1 = 0
    · simp only [route, zero, and_self, ↓reduceDIte, ↓reduceIte, StackMachine.reindex_suffix,
        completeReader_suffix]
    · simp only [route, zero, false_and, ↓reduceDIte, ↓reduceIte, LocalHistory.initialReader,
        StackMachine.reindex_suffix, LocalHistory.bufferReader, ChoiceReader.single, Option.map_some]
  · simp only [route, Bool.false_eq_true, and_false, ↓reduceDIte, ↓reduceIte, LocalHistory.initialReader,
      StackMachine.reindex_suffix, LocalHistory.bufferReader, Option.map_none]

theorem nominationReader_length_le (t : ℕ) (bound : steps 52 (auxiliary D hw hc v (halfBuffers v z)) ≤ t)
    (x : initialChoices D.machine D.fuel 0 D.initial hw hc v z) :
    ((nominationReader D hw hc v z t bound).encode x).length ≤ t := by
  unfold nominationReader
  split
  · exact (completeReader_length_lt _ _ _ _ _).le
  · unfold LocalHistory.initialReader ChoiceReader.reindex
    dsimp only
    apply (LocalHistory.bufferReader_length_le D.machine D.fuel 0 hw hc (D.initial v.2) v (halfBuffers v z) _).trans
    apply Nat.le_trans _ bound
    unfold steps choiceBound
    change 2 * 2^e * (D.fuel + w) ≤ _ + (4 * (2 * 2^e * (D.fuel + w)) + 1) + 3 + _
    omega

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
