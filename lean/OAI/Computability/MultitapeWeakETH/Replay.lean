import OAI.Computability.MultitapeWeakETH.PhysicalPaths
import OAI.Computability.MultitapeWeakETH.ReaderEnumeration
import OAI.Computability.VPVNP.CompressorExecutionTrace
import OAI.Computability.MultitapeWeakETH.FrameDecoding

/-! # Deterministic replay of the outer sum from binary branch tapes -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords BurstRAM BranchSegments Algorithms.SubexponentialSAT
open scoped Classical
noncomputable section

variable {w : ℕ} {Q : Type} (P : BurstRAM.Program w Q) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)

/-- Decode actual call tapes, require canonical zero padding, execute the
fixed table on those tapes, and retain its halting reports. -/
def replay (input : List Bool) : Option (List (Report w)) := do
  let (tapes, tail) ← ProgramEncoding.readRecords input
  if tail ≠ List.replicate tail.length false then none else
  let logs ← runSegment P fuel st m tapes
  if endState st logs = none then some logs else none

/-- The physical reader supplies exactly the tapes consumed by replay on every candidate. -/
theorem replay_padded (input : List Bool) :
    replay P fuel st m input =
      (bif (FrameProgram.padded input).1 then do
        let logs ← runSegment P fuel st m (FrameProgram.padded input).2
        if endState st logs = none then some logs else none
       else none) := by
  cases hr : FrameProgram.padded input with
  | mk ok rows =>
    cases ok with
    | true =>
      obtain ⟨d,rfl⟩ := (FrameProgram.padded_iff _ _).mp hr
      simp [replay,ProgramEncoding.readRecords_encodeList_append]
    | false =>
      cases h : ProgramEncoding.readRecords input with
      | none => simp [replay,h]
      | some r =>
        obtain ⟨rs,t⟩ := r
        have bad : t ≠ List.replicate t.length false := by
          intro z
          have e := (FrameProgram.padded_iff input rs).mpr
            ⟨t.length,(ProgramEncoding.readRecords_sound h).trans (congrArg _ z)⟩
          rw [hr] at e
          cases e
        simp [replay,h,bad]

private abbrev Paths := LiveProgram.PathsFrom P fuel st m (fun _ => True)

private def admit (tapes : List (List Bool)) : Option (Paths P fuel st m) :=
  if h : ∃ logs, runSegment P fuel st m tapes = some logs ∧ endState st logs = none ∧ True
    then some ⟨tapes,h⟩ else none

private theorem admit_iff (bs : List (List Bool)) (path : Paths P fuel st m) :
    admit P fuel st m bs = some path ↔ bs = path.val := by
  constructor
  · unfold admit
    split <;> simp
    exact fun h => congrArg Subtype.val h
  · rintro rfl
    rw [admit,dite_eq_left path.property]

private def reader : ChoiceReader (Paths P fuel st m) where
  encode p := pathCode p.val
  read b := do
    let (bs,t) ← ProgramEncoding.readRecords b
    let p ← admit P fuel st m bs
    return (p,t)
  read_iff b p t := by
    constructor
    · intro read
      simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at read
      obtain ⟨⟨bs,rest⟩,hb,path,ad,eq⟩ := read
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eq)
      exact (admit_iff P fuel st m bs path).mp ad ▸ ProgramEncoding.readRecords_sound hb
    · rintro rfl
      simp [pathCode, ProgramEncoding.readRecords_encodeList_append, (admit_iff P fuel st m p.val p).mpr rfl]

private def pathLogs (p : Paths P fuel st m) := Classical.choose p.property

private theorem replay_eq (bits : List Bool) :
    replay P fuel st m bits = (ReaderEnumeration.decode (reader P fuel st m) bits).map (pathLogs P fuel st m) := by
  unfold replay ReaderEnumeration.decode reader
  cases rb : ProgramEncoding.readRecords bits with
  | none => simp [rb]
  | some pair =>
    obtain ⟨bs,rest⟩ := pair
    simp only [Option.bind_eq_bind, rb, Option.bind_some, Option.pure_def]
    cases run : runSegment P fuel st m bs with
    | none => simp [admit,run]
    | some logs =>
      by_cases halt : endState st logs=none
      · let path : Paths P fuel st m := ⟨bs,logs,run,halt,trivial⟩
        have hl : pathLogs P fuel st m path = logs :=
          Option.some.inj ((Classical.choose_spec path.property).1.symm.trans run)
        have ad := (admit_iff P fuel st m bs path).mpr rfl
        by_cases pad : rest=List.replicate rest.length false
        · simp only [ad,Option.bind_some,halt,ite_eq_left pad,ite_eq_right (not_not_intro pad),Option.map_some,hl,reduceIte]
        · simp only [ad,Option.bind_some,ite_eq_right pad,ite_eq_left pad,Option.map_none]
      · simp [admit,run,halt]

variable {R V : Type} [CommSemiring R] [AddCommMonoid V] {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X}

/-- A fixed-length binary search visits every complete sequence of native reports
with its branch multiplicity. The callback may use the entire write history. -/
theorem report_sum (trace : ExecutionTrace P fuel E st m) [Fintype E.Choices]
    (L : ℕ) (cost : ∀ z, (pathCode (trace.cut.part z).bits).length ≤ L) (value : List (Report w) → V) :
    ReaderEnumeration.treeSum (fun bits => (replay P fuel st m bits).elim 0 value) L [] = ∑ z, value (trace.cut.part z).logs := by
  let e := trace.allEquiv (fun _ => True) (fun _ => trivial)
  let _ := Fintype.ofEquiv E.Choices e
  let read := reader P fuel st m
  let v (p : Paths P fuel st m) := value (pathLogs P fuel st m p)
  have term (bits : List Bool) :
      ((replay P fuel st m bits).elim 0 value) =
        (ReaderEnumeration.decode read bits).elim 0 v := by
    rw [replay_eq]
    cases ReaderEnumeration.decode read bits <;> rfl
  simp_rw [term]
  rw [ReaderEnumeration.sum_decode _ _ (fun p => by obtain ⟨z,rfl⟩ := e.surjective p; exact cost z),
    ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  have eq := (Classical.choose_spec (e z).property).1
  change runSegment P fuel st m (trace.cut.part z).bits = some (pathLogs P fuel st m (e z)) at eq
  rw [(trace.cut.part z).run] at eq
  exact congrArg (value) (Option.some.inj eq).symm

/-- Replaying and summing the padded binary candidates visits every
mathematical branch once, even when different branches end in the same
memory. The callback sees only the native post-memory. -/
theorem replay_sum (trace : ExecutionTrace P fuel E st m) [Fintype E.Choices]
    (L : ℕ) (cost : ∀ z, (pathCode (trace.cut.part z).bits).length ≤ L) (value : Memory w → V) :
    ReaderEnumeration.treeSum (fun bits => (replay P fuel st m bits).elim 0 fun logs =>
      value (after m (eventLog logs))) L [] = ∑ z, value (trace.cut.part z).memory :=
  report_sum P fuel st m trace L cost (fun logs => value (after m (eventLog logs)))

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
