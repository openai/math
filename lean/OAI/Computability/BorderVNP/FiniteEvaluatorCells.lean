import OAI.Computability.BorderVNP.FiniteEvaluatorCellWeight
import OAI.Computability.BorderVNP.FiniteEvaluatorCellCodec
import OAI.Computability.BorderVNP.FiniteEvaluatorHistories
import OAI.Computability.BorderVNP.RoutingISAFiniteScalarPrepared

/-! # Chronological field contraction of a team's prepared sparse cells

The team prepares its real compact packets, validates the owned rows at opcode
zero, and reads the surviving bit-major reports at opcode one. The complete
signed-path sum of the first stage and the physical scalar product of the second
stage use the same native program, memory and clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Cells

open VPVNP.BurstRAM RoutingISA FieldProcessor TeamContraction TeamRAM
open TypedTaskBuilder FiniteScalarRounds FiniteScalarLibrary
open scoped BigOperators Classical

variable {w n : ℕ} {F : Type*} [Field F] [Fintype F]

/-- The two consecutive fixed code fragments of a finite team's cell evaluator. -/
def code := Code.seq TypedBatch.runCells FiniteScalarBatch.code

/-- The true shared scalar library and signed translator installed at this team. -/
noncomputable def library (F : Type*) [Field F] [Fintype F] (codec : Codec := .dense) :=
  combine F (CompactMachine.siteLibrary codec.driver)

/-- The signed routine carries its terminal sign and the scalar routine carries its
actual field result read from the report words. -/
noncomputable def terminals (F : Type*) [Field F] [Fintype F] (codec : Codec := .dense) :=
  returns F (CompactMachine.siteLibrary codec.driver) (fun _ => signedReturn)

/-- All data words and local field reports consumed at the stage boundary. -/
structure Inputs (F : Type*) [Fintype F] where
  /-- Shared frame, table and arena addresses. -/
  layout : Layout
  /-- Numerical public image used to enumerate owned cells. -/
  publicMem : ℕ → ℕ
  /-- Owned packet tasks with their bit-major scalar reports. -/
  rows : ℕ → FiniteScalarBatch.Row
  /-- Sparse validator inputs indexed by the global call row. -/
  cells : ℕ → CompactMachine.CellInput
  /-- Binary digit width of the count word for each owned row. -/
  digits : ℕ → ℕ
  /-- Bits actually supplied for each local field-element count. -/
  claim : (i : ℕ) → Index F → Fin (digits i) → Bool

variable (X : Inputs F)

/-- Number of owned rows. -/
def Inputs.count := X.layout.before X.publicMem X.layout.cells
/-- The physically supplied signed validator task at one row. -/
def Inputs.tasks (i : ℕ) := (X.rows i).task

/-- The physical assertions on a prepared shared-memory image, covering actual
sparse source intervals, reported field bits, ownership, word cap and private clock. -/
structure Prepared (pub : Arg → Word w) (mem : Memory w) (n : ℕ) (codec : Codec := .dense) : Prop where
  pointer : (pub 0).val=X.layout.frame
  fields : X.layout.Fields (readings mem)
  width : (mem (X.layout.frame+30)).val=w
  countWord : (mem (X.layout.frame+90)).val=X.count
  room : X.layout.Room X.publicMem w
  arenas : X.layout.Arenas X.publicMem w X.tasks
  control : X.layout.SourceRange X.layout.control 8
  tails : X.layout.SourceRange X.layout.tails X.layout.cells
  ids : ∀ i < X.count, (X.rows i).cell=globalCell X.layout X.publicMem i
  stored : ∀ i < X.count, (X.tasks i).Stored mem X.layout.tasks i
  data : ∀ i < X.count, (X.tasks i).cell.Stored mem
  bank : ∀ i < X.count, (X.tasks i).cell.external=(X.rows i).supplied++(X.rows i).claims
  tail : ∀ i < X.count, (mem (X.layout.tails+(X.rows i).cell)).val=(X.rows i).claims.length
  stream : ∀ i < X.count, (X.rows i).claims=FiniteScalarRounds.stream F (X.claim i)
  scalarClock : ∀ i < X.count, 2*X.digits i*Fintype.card F < CompactMachine.nativeClock n
  placed : TypedBatch.PlacedRows pub mem X.tasks X.count n (codec.physical X.cells)
  privateClock : ∀ i < (CellDispatch.Frame.ofMemory pub mem).count,
    (mem ((CellDispatch.Frame.ofMemory pub mem).address i)).val=(CellDispatch.Frame.ofMemory pub mem).team →
      codec.Valid w n (X.cells i) i

/-- Native upper bound for packet preparation and all actual signed cell calls. -/
def Inputs.validatorCost (pub : Arg → Word w) (mem : Memory w) :=
  let f := CellDispatch.Frame.ofMemory pub mem
  let after := TypedBatch.written mem X.tasks X.count
  (TypedBatch.loadDirectory.slots+TypedBatch.setup.slots+
    (∑ i ∈ Finset.range X.count, TypedBatch.rowCharge (fun j => (X.tasks j).cell.cost w) i)+1)+
    (17+7*f.count+4*(f.ownedRows after 0 f.count).length+∑ i ∈ Finset.range X.count, ((X.tasks i).cell.burst w).length)

/-- Native upper bound for physically packing and reading just the report tails. -/
def Inputs.scalarCost :=
  FiniteScalarBatch.setup.slots+1+(FiniteScalarBatch.locate.slots+CompactWrite.setup.slots+FiniteScalarCall.count.slots+6)*X.count +
    (CompactWrite.step.slots+3)*(∑ j ∈ Finset.range X.count, (X.rows j).claims.length)

/-- The complete true field-return list, in physical owned-cell order. -/
noncomputable def Inputs.outputs : List F :=
  (List.range X.count).map fun j => ∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (X.claim j i))

/-- The fixed team code on the actual allocated field/cell data yields a finite
dictionary of *all* native histories, with exactly the product of the real sparse
validator weights and the finite-field reports, including zero-weight paths. -/
theorem prepared_value_for (codec : Codec) (pub : Arg → Word w) (s : Bank w) (mem : Memory w) (n : ℕ) (h : Prepared X pub mem n codec) :
    let fuel := CompactMachine.nativeClock n
    let mac := TeamSiteEvents.macros (library F codec) fuel
    let f := CellDispatch.Frame.ofMemory pub mem
    ∃ paths : Finset (List (TeamRAM.Event w)),
      (∀ bits es, execute (code.program.fetch pub mac) ⟨0,s⟩ mem bits = some es ↔ es∈paths ∧ es.map TeamRAM.Event.choices=bits) ∧
      (∀ es ∈ paths, Within (X.validatorCost pub mem+X.scalarCost) (TeamScales.width n (1/2)) (n^25) es) ∧
      (∑ es ∈ paths, weight pub (library F codec) (terminals F codec) fuel code s es) =
        ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod := by
  intro fuel mac f
  let after := TypedBatch.written mem X.tasks X.count
  have ff : f = ⟨X.layout.team,X.layout.calls,X.layout.cells⟩ := by
    have fo := h.fields.outer
    change readings mem X.layout.frame = _ ∧ _ at fo
    change CellDispatch.Frame.mk _ _ _ = _
    rw [h.pointer]
    exact (congrArg (fun t => CellDispatch.Frame.mk t _ _) fo.1).trans (congrArg₂ (CellDispatch.Frame.mk _) fo.2.2.1 fo.2.2.2.1)
  have froom : f.base+3*f.count ≤ 2^w := by rw [ff]; exact h.room.calls.le
  have fits : (pub 0).val+90 < 2^w := by rw [h.pointer]; have := h.room.frame; omega
  have table : (mem ((pub 0).val+89)).val = X.layout.tasks := h.pointer ▸ h.fields.outer.2.2.2.2.2.2.1
  have width : (mem ((pub 0).val+30)).val = w := h.pointer ▸ h.width
  have len : (mem ((pub 0).val+90)).val = X.count := h.pointer ▸ h.countWord
  have space : X.layout.tasks+7*X.count ≤ 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (X.layout.before_le X.publicMem X.layout.cells)) _).trans h.room.tasks.le
  have alloc := allocated X.layout X.publicMem h.room h.arenas
  have ctrl := control X.layout X.publicMem h.room h.arenas h.pointer ff
  have rooms (i : ℕ) (hi : i<X.count) : (X.tasks i).callRow+2 < 2^w ∧ (X.tasks i).cell.Room w := by
    constructor
    · rw [(h.arenas.starts i hi).1,Layout.call]
      have one := (global_spec X.layout X.publicMem hi).1
      have total := h.room.calls
      omega
    · exact task_room X.layout X.publicMem h.room h.arenas hi
  obtain ⟨pre,t,prep,cost,accept,bound,ival⟩ := codec.team_value pub s mem X.tasks X.cells mac
    fits width table len space alloc (fun i hi => ⟨h.stored i hi,h.data i hi⟩) rooms ctrl h.placed froom h.privateClock
  have install : CompactMachine.install codec.driver n mac = mac := install_combined F codec.driver n
  rw [install] at prep accept
  let old := CompactBatch.preparedHistories pre f pub after (CompactMachine.choices codec.driver n)
  have admit (es) : es∈old ↔ ∃ z mz, Runs pub mac TypedBatch.runCells s mem es z mz := by
    constructor
    · intro yes
      have run := (accept (es.map TeamRAM.Event.choices) es).mpr ⟨yes,rfl⟩
      exact ((Code.execute_iff_runs (by decide : TypedBatch.runCells.withoutAccept=true)).mp run).1
    · rintro ⟨z,mz,r⟩
      exact ((accept _ es).mp r.execute).1
  have budget (es) (yes : es ∈ old) : Within (X.validatorCost pub mem) (TeamScales.width n (1/2)) (n^25) es := by
    have small := bound es yes
    exact ⟨small.cost.trans (Nat.add_le_add_right cost _),small.length,small.choices⟩
  have decompose {es z mz} (r : Runs pub mac TypedBatch.runCells s mem es z mz) :
      ∃ fs, Runs pub mac callOwnedCells t after fs z mz := by
    obtain ⟨v,mv,xs,ys,_,first,second⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := prep.unique_of_deterministic (by decide : TypedBatch.entry.deterministic=true) first
    exact ⟨ys,second⟩
  have same {es z mz gs v mv} (r : Runs pub mac TypedBatch.runCells s mem es z mz) (q : Runs pub mac TypedBatch.runCells s mem gs v mv) : z=v ∧ mz=mv := by
    obtain ⟨_,first⟩ := decompose r
    obtain ⟨_,second⟩ := decompose q
    exact CellDispatch.same_post first second
  have suffix {es z mz} (r : Runs pub mac TypedBatch.runCells s mem es z mz) :
      ∃ gs v mv, Runs pub mac FiniteScalarBatch.code z mz gs v mv ∧ Within X.scalarCost (TeamScales.width n (1/2)) (n^25) gs ∧
        weight pub (library F codec) (terminals F codec) fuel FiniteScalarBatch.code z gs = X.outputs.prod ∧
        ∀ fs u mu, Runs pub mac FiniteScalarBatch.code z mz fs u mu → fs=gs := by
    obtain ⟨_,dispatch⟩ := decompose r
    have preserved : CellDispatch.Frame.ofMemory pub after = f := ctrl.survives.1
    have sp : (CellDispatch.Frame.ofMemory pub after).base+3*(CellDispatch.Frame.ofMemory pub after).count ≤ 2^w := by rw [preserved]; exact froom
    obtain ⟨_,_,_,_,_,rfl⟩ := CellDispatch.directory_decode (by omega) sp dispatch
    obtain ⟨gs,v,run,small,_,reads,clean,unique⟩ := FiniteScalarBatch.prepared_field F (CompactMachine.siteLibrary codec.driver)
      (fun _ => signedReturn) pub z mem X.layout X.publicMem X.rows X.digits X.claim h.pointer h.fields h.width h.countWord h.room
      h.arenas h.control h.tails h.ids h.stored h.data h.bank h.tail h.stream h.scalarClock h.placed.cap
    refine ⟨gs,v,_,run,small,?_,fun fs u mu q => (unique fs u mu q).1⟩
    apply scalar_weight pub _ _ _ run X.outputs _ (fun e he => (clean e he).2)
    simpa only [Inputs.outputs,Inputs.count,List.map_map,Function.comp_def] using reads
  obtain ⟨paths,passes,limits,val⟩ := continue_histories pub (library F codec) (terminals F codec) fuel TypedBatch.runCells FiniteScalarBatch.code s mem old
    (X.validatorCost pub mem) X.scalarCost (TeamScales.width n (1/2)) (n^25) X.outputs.prod admit budget same suffix
  refine ⟨paths,?_,limits,?_⟩
  · intro bits es
    exact (Code.execute_iff_runs (by decide : code.withoutAccept=true)).trans (and_congr_left fun _ => (passes es).symm)
  · unfold code
    rw [val]
    apply congrArg (· * X.outputs.prod)
    calc
      _ = ∑ es ∈ old, ((pathWeight es : ℤ) : F) := by
        apply Finset.sum_congr rfl
        intro es he
        obtain ⟨_,_,r⟩ := (admit es).mp he
        exact old_weight pub (CompactMachine.siteLibrary codec.driver) fuel r (by decide)
      _ = ((∑ es ∈ old, pathWeight es : ℤ) : F) := by simp only [Int.cast_sum]
      _ = _ := congrArg (fun z : ℤ => (z:F)) ival

/-- The contiguous-format specialization of the complete chronological field stage. -/
theorem prepared_value (pub : Arg → Word w) (s : Bank w) (mem : Memory w) (n : ℕ) (h : Prepared X pub mem n) :
    let fuel := CompactMachine.nativeClock n
    let mac := TeamSiteEvents.macros (library F) fuel
    let f := CellDispatch.Frame.ofMemory pub mem
    ∃ paths : Finset (List (TeamRAM.Event w)),
      (∀ bits es, execute (code.program.fetch pub mac) ⟨0,s⟩ mem bits = some es ↔ es∈paths ∧ es.map TeamRAM.Event.choices=bits) ∧
      (∀ es ∈ paths, Within (X.validatorCost pub mem+X.scalarCost) (TeamScales.width n (1/2)) (n^25) es) ∧
      (∑ es ∈ paths, weight pub (library F) (terminals F) fuel code s es) =
        ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod :=
  prepared_value_for X .dense pub s mem n h

end FiniteEvaluator.Cells

end BorderVNP
end Computability
end OAI
