import OAI.Computability.BorderVNP.RoutingISACompactBatchMemory
import OAI.Computability.BorderVNP.RoutingISACompactBatchScan
import OAI.Computability.BorderVNP.RoutingISASparseCells
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Chronological histories of the combined sparse-command preparation and dispatch

The preparation prefix is a genuine execution of the fixed word-level batch scan. It is
deterministic and has positive sign at every instruction. Each subsequent private call
uses its assigned burst in the memory produced by the scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactBatch

open VPVNP.BurstRAM CellDispatch CompactMachine CellMacro.Generator

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Native preparation of the physical bursts followed by signed execution of the cell rows. -/
def prepareDispatch : Code := .seq scan callOwnedCells

private def appendPrefix (pre : List (TeamRAM.Event w)) :
    List (TeamRAM.Event w) ↪ List (TeamRAM.Event w) :=
  ⟨(pre ++ ·), fun _ _ h => List.append_cancel_left h⟩

/-- All complete chronological histories, including the actual deterministic preparation. -/
noncomputable def preparedHistories (pre : List (TeamRAM.Event w)) (f : Frame)
    (pub : Arg → Word w) (mt : Memory w) (choices : List (Word w) → Finset Outcome) :
    Finset (List (TeamRAM.Event w)) :=
  (f.histories pub mt choices).map (appendPrefix pre)

/-- Membership in the finite set is exact acceptance by the combined assembled program,
with its full choice tape and the true memory after preparation. -/
theorem mem_prepared_iff_of {c : Code} (det : c.deterministic = true) (normal : c.withoutAccept = true) {s t : Bank w} {m mt : Memory w} {pre : List (TeamRAM.Event w)}
    (prep : Runs pub macros c s m pre t mt)
    {choices : List (Word w) → Finset Outcome} (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w)
    (room : (Frame.ofMemory pub mt).base+3*(Frame.ofMemory pub mt).count ≤ 2^w)
    {es : List (TeamRAM.Event w)} {bits : List (List Bool)} :
    TeamRAM.execute ((c.seq callOwnedCells).program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      es ∈ preparedHistories pre (Frame.ofMemory pub mt) pub mt choices ∧ es.map TeamRAM.Event.choices = bits := by
  rw [Code.execute_iff_runs (by simp only [Code.withoutAccept,normal,show callOwnedCells.withoutAccept = true by decide,Bool.and_self] : (c.seq callOwnedCells).withoutAccept = true)]
  apply and_congr_left
  intro _
  unfold preparedHistories
  rw [Finset.mem_map]
  constructor
  · rintro ⟨z,mz,r⟩
    obtain ⟨u,mu,xs,ys,rfl,first,rest⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := prep.unique_of_deterministic det first
    exact ⟨ys,(Frame.mem_histories spec frameFit room ys).2 rest.execute,rfl⟩
  · rintro ⟨ys,mem,rfl⟩
    have e := (Frame.mem_histories (s := t) spec frameFit room ys).1 mem
    obtain ⟨⟨u,mu,rest⟩,_⟩ := (Code.execute_iff_runs (by decide : callOwnedCells.withoutAccept = true)).1 e
    exact ⟨u,mu,prep.seq rest⟩

/-- Membership in the finite set is exact acceptance by the combined assembled program,
with its full choice tape and the true memory after preparation. -/
theorem mem_prepared_iff {s t : Bank w} {m mt : Memory w} {pre : List (TeamRAM.Event w)}
    (prep : Runs pub macros scan s m pre t mt)
    {choices : List (Word w) → Finset Outcome} (spec : ∀ v o, o ∈ choices v ↔ macros 0 v o.1 = some o.2)
    (frameFit : (pub 0).val+15 < 2^w)
    (room : (Frame.ofMemory pub mt).base+3*(Frame.ofMemory pub mt).count ≤ 2^w)
    {es : List (TeamRAM.Event w)} {bits : List (List Bool)} :
    TeamRAM.execute (prepareDispatch.program.fetch pub macros) ⟨0,s⟩ m bits = some es ↔
      es ∈ preparedHistories pre (Frame.ofMemory pub mt) pub mt choices ∧ es.map TeamRAM.Event.choices = bits :=
  mem_prepared_iff_of (by decide) (by decide) prep spec frameFit room

/-- Including the physical preparation in every history preserves the sum of its signed weights. -/
theorem sum_prepared_of {c : Code} (unsigned : c.unsigned = true) {s t : Bank w} {m mt : Memory w} {pre : List (TeamRAM.Event w)}
    (prep : Runs pub macros c s m pre t mt) (f : Frame) (choices : List (Word w) → Finset Outcome) :
    ∑ es ∈ preparedHistories pre f pub mt choices, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ∑ es ∈ f.histories pub mt choices, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod := by
  have pos : (pre.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod = 1 := by
    apply List.prod_eq_one
    intro n hn
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hn
    simp [(prep.unsigned_events unsigned e he).2, TeamRAM.Sign.value]
  rw [preparedHistories, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro es _
  change ((pre ++ es).map _).prod = _
  rw [List.map_append, List.prod_append, pos, one_mul]

/-- Including the physical preparation in every history preserves the sum of its signed weights. -/
theorem sum_prepared {s t : Bank w} {m mt : Memory w} {pre : List (TeamRAM.Event w)}
    (prep : Runs pub macros scan s m pre t mt) (f : Frame) (choices : List (Word w) → Finset Outcome) :
    ∑ es ∈ preparedHistories pre f pub mt choices, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ∑ es ∈ f.histories pub mt choices, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod :=
  sum_prepared_of (by decide) prep f choices

/-- Per-owned-row relation between the physical batch task and the sparse-command generator
input. The suffix carries the serialized sparse statement, whose body is already placed. -/
structure SparseRows (f : Frame) (m : Memory w) (tasks : ℕ → Task) (count d h n : ℕ)
    (cells : ℕ → CellInput) : Prop where
  /-- A live row points to the output of a task that contains its true boundary bits and
  its serialized sparse-command suffix. -/
  task : ∀ i < f.count, (m (f.address i)).val = f.team → ∃ j < count,
    (m (f.address i+1)).val = (tasks j).dest ∧
    (m (f.address i+2)).val = (CompactFrame.pack w (tasks j).payload).length ∧
    (tasks j).external = (cells i).external ∧
    (tasks j).suffix = serialized d ((cells i).directory.program (cells i).privateWires)
  /-- Every owned row fits the native square-root burst allowance. -/
  cap : ∀ i < f.count, (m (f.address i)).val = f.team → (m (f.address i+2)).val ≤ TeamScales.width n (1/2)
  /-- Every serialized body fits the fixed finite generator. -/
  depth : ∀ i < f.count, (m (f.address i)).val = f.team →
    ((cells i).directory.program (cells i).privateWires).FitsDepth d h
  /-- All native private executions fit the paper's clock. -/
  clock : ∀ i < f.count, (m (f.address i)).val = f.team → 2*(cells i).allowance w d ≤ n^25

/-- The combined native program computes the product of the sparse signed cell values.
The word arguments are produced by the real preparation run and remain live at each call. -/
theorem native_sparse_sum {table count d h n : ℕ} (s : Bank w) (m : Memory w) (tasks : ℕ → Task)
    (five : 5 < 2^w) (width : (s 2).val = w) (base : (s 32).val = table) (len : (s 33).val = count)
    (space : table+5*count ≤ 2^w) (alloc : Allocation w table count tasks)
    (init : ∀ j < count, (tasks j).Stored m table j ∧ (tasks j).Input m ∧ (tasks j).Fits w)
    (frame : ∀ j < count, (tasks j).Apart w (pub 0).val 16)
    (rows : ∀ j < count, (tasks j).Apart w (Frame.ofMemory pub m).base (3*(Frame.ofMemory pub m).count))
    (frameFit : (pub 0).val+15 < 2^w) (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (cells : ℕ → CellInput) (layout : SparseRows (Frame.ofMemory pub m) m tasks count d h n cells)
    (routines : TeamOpcode.Macros w 8) :
    let mt := written m tasks count
    let f := Frame.ofMemory pub m
    let mac := install (generate d h) n routines
    let cs := choices (generate d h) n
    ∃ pre t, Runs pub mac scan s m pre t mt ∧
      traceCost pre ≤ setup.slots+(∑ j ∈ Finset.range count, ((tasks j).cost+1))+1 ∧
      (∀ bits es, TeamRAM.execute (prepareDispatch.program.fetch pub mac) ⟨0,s⟩ m bits = some es ↔
        es ∈ preparedHistories pre f pub mt cs ∧ es.map TeamRAM.Event.choices = bits) ∧
      ∑ es ∈ preparedHistories pre f pub mt cs, (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
        ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  intro mt f mac cs
  obtain ⟨pre,t,prep,cost,_⟩ := scan_run (pub := pub) (macros := mac) s m tasks five width base len space
    (alloc.ready m init)
  obtain ⟨ff,fields⟩ := preserve_directory m pub frame rows
  have owner (i : ℕ) (hi : i < f.count) : mt (f.address i) = m (f.address i) :=
    fields i hi 0 (by decide)
  have hw : 0 < w := by cases w with | zero => contradiction | succ w => exact Nat.succ_pos _
  have words (i : ℕ) (hi : i < f.count) (own : (mt (f.address i)).val = f.team) :
      TeamRAM.previous mt (f.burst mt i) = CompactFrame.pack w (serialized d (cells i).stmt) := by
    obtain ⟨j,hj,ptr,size,ext,suff⟩ := layout.task i hi ((owner i hi) ▸ own)
    have h := alloc.row_result m pub frame rows hi hj ptr size
    rw [ff, Task.payload, ext, suff] at h
    simpa only [CellInput.stmt, serialized_withExternal] using h
  have span (i : ℕ) (hi : i < f.count) (own : (mt (f.address i)).val = f.team) :
      (mt (f.address i+1)).val+(mt (f.address i+2)).val ≤ 2^w := by
    obtain ⟨j,hj,ptr,size,_,_⟩ := layout.task i hi ((owner i hi) ▸ own)
    rw [show mt (f.address i+1) = m (f.address i+1) from fields i hi 1 (by decide),
      show mt (f.address i+2) = m (f.address i+2) from fields i hi 2 (by decide),ptr,size]
    exact (init j hj).2.2.dest
  refine ⟨pre,t,prep,cost,?_,?_⟩
  · intro bits es
    have finalRoom : (Frame.ofMemory pub mt).base+3*(Frame.ofMemory pub mt).count ≤ 2^w := ff ▸ room
    simpa only [ff] using (mem_prepared_iff prep (mem_choices (generate d h) n routines) frameFit finalRoom
      (es := es) (bits := bits))
  · have bound (i : ℕ) (hi : i < f.count) (own : (mt (f.address i)).val = f.team) :
        (mt (f.address i+2)).val ≤ TeamScales.width n (1/2) := by
      rw [show mt (f.address i+2) = m (f.address i+2) from fields i hi 2 (by decide)]
      exact layout.cap i hi ((owner i hi) ▸ own)
    rw [sum_prepared prep, sparse_directory_sum pub cells hw span bound words
      (fun i hi own => layout.depth i hi ((owner i hi) ▸ own))
      (fun i hi own => layout.clock i hi ((owner i hi) ▸ own))]
    have same : f.ownedRows mt 0 f.count = f.ownedRows m 0 f.count := by
      apply List.filter_congr
      intro i hi
      have lt : i < f.count := by simpa using hi
      rw [owner i lt]
    rw [same]

end RoutingISA.CompactBatch

end BorderVNP
end Computability
end OAI
