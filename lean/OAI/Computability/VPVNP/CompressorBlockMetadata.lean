import OAI.Computability.VPVNP.CompressorBlockHeaderRun
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.CompressorShrinkSelectedPlan
import OAI.Computability.VPVNP.CompressorFormulaFootprint
import OAI.Computability.VPVNP.PairTraversalRoles
import OAI.Computability.VPVNP.CompressorRefreshStageFrame

/-!
# Publishing the DFS descriptor and prefix of a compressor substep

The planner emits three one-call rows. The first worker copies twelve
computed operands into the input graph header. The other two workers set
the next graph's DFS layer base and producing role. The native writer
reads its public operand bank before its first external store.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockMetadata

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe RowRecipe DescriptorSpace BlockPlanner LevelFields
open scoped Fin.CommRing

/-- Substep-specific child placement columns and the exclusive child capacity. -/
structure Fields where
  /-- Expression for the number of sites produced by the selected pass. -/
  newSites : Expr
  /-- Expression for the base of the column mapping old site identifiers to their owners. -/
  owner : Expr
  /-- Expression for the base of the child-count column, indexed by new site identifier. -/
  count : Expr
  /-- Expression for the base of the rows listing each new site's old children. -/
  row : Expr
  /-- Expression for the number of child identifiers reserved per placement row. -/
  cap : Expr

/-- The selected shrink's collector and the DFS reader use the same count
and row intervals and the same maximum preimage cardinality. -/
def Fields.shrink (a : ℕ) (I : SelectedPlan.Inputs) : Fields :=
  ⟨I.newSites, SelectedPlan.placementColumn I 0, SelectedPlan.roleEnd I, SelectedPlan.childRows I,
    .lit (ShrinkPreimages.capacity a)⟩

/-- Refresh placement is a bijection. Its owner, count, and unique-child
columns are three consecutive site-sized intervals. -/
def Fields.refresh (step : ℕ) (table4 : Expr) : Fields :=
  let count := table4.add (sites step)
  ⟨sites step,table4,count,count.add (sites step),.lit 1⟩

/-- The kind of compressor pass that produced a traversal layer. -/
inductive Role | shrink | refresh deriving DecidableEq

/-- Numerical role tag stored in the successor header, one for shrinking and two for refresh. -/
def Role.code : Role → ℕ | .shrink => 1 | .refresh => 2

/-- Expression reading the input length from word 29 of the first level header. -/
def lengthWord : Expr := .load (BlockHeaderPlan.firstHeader.add (.lit 29))

/-- Header offsets 15 through 26 in the order consumed by the DFS handler. -/
def fieldExprs (F : Shape) (step recordLimit slotDegree : ℕ) (v : Fields) : Fin 12 → Expr :=
  ![.lit (recordLimit+2),degree step,lengthWord,
    ((Expr.lit (2*slotDegree)).mul lengthWord).add (.lit 1),
    incidence F step 4,incidence F step 5,sites step,
    v.newSites,v.owner,v.count,v.row,v.cap]

/-- Advance the DFS row base by the current site count times the reserved row stride. -/
def nextBase (step recordLimit : ℕ) : Expr :=
  (scalar step 14).add ((Expr.lit (recordLimit+2)).mul (sites step))

/-- Destination followed by the twelve evaluated operands. -/
def writer : Recipe 13 13 9 where
  lines := (List.finRange 13).map fun j ↦ ⟨j,.publicWord j⟩
  dest := 0
  tag := 1
  start := 2
  stop := 3
  params := fun j ↦ j.succ.succ.succ.succ

/-- The visit that writes the twelve traversal metadata operands starting at offset 15 of the
input header. -/
def current (F : Shape) (step recordLimit slotDegree : ℕ) (v : Fields) : Visit :=
  ⟨⟨_,_,_,writer.table⟩,.lit 0,.lit 1,Fin.cons (address step 15) (fieldExprs F step recordLimit slotDegree v)⟩

/-- The visit that stores the computed DFS row base at offset 14 of the successor header. -/
def outputBase (step recordLimit : ℕ) : Visit :=
  BlockPlanner.publish (address (step+1) 14) (nextBase step recordLimit)

/-- The visit that stores the producing pass's role tag at offset 27 of the successor header. -/
def outputRole (step : ℕ) (role : Role) : Visit :=
  BlockPlanner.publish (address (step+1) 27) (.lit role.code)

/-- Publish the input level's traversal metadata, then the successor's row base and role tag. -/
def visits (F : Shape) (step recordLimit slotDegree : ℕ) (role : Role) (v : Fields) : List Visit :=
  [current F step recordLimit slotDegree v, outputBase step recordLimit, outputRole step role]

@[simp] theorem visits_length (F : Shape) (step recordLimit slotDegree : ℕ) (role : Role) (v : Fields) :
    (visits F step recordLimit slotDegree role v).length = 3 := rfl

variable {w : ℕ}

private theorem load_bank (pub : Fin 13 → Word w) (s : Word w) (m : Memory w)
    (js : List (Fin 13)) (regs : PrimedStackRAM.Regs w 13) (j : Fin 13) :
    (evaluate pub s m (js.map fun i ↦ (⟨i,.publicWord i⟩ : Assign 13 13)) regs).2 j =
      if j ∈ js then pub j else regs j := by
  induction js generalizing regs with
  | nil => simp [evaluate]
  | cons i js ih =>
    simp only [List.map_cons, evaluate, RHS.value, ih, List.mem_cons]
    by_cases e : j=i <;> by_cases h : j ∈ js <;> simp [e,h]

theorem writer_values (pub : Fin 13 → Word w) (s : Word w) (m : Memory w) :
    writer.values pub s m = pub := by
  funext i
  change (evaluate pub s m ((List.finRange 13).map _) _).2 i = _
  rw [load_bank,ite_eq_left (List.mem_finRange i)]

theorem writer_address (pub : Fin 13 → Word w) (s : Word w) (m : Memory w) :
    writer.address pub s m = pub 0 := by rw [Recipe.address, writer_values]; rfl

theorem writer_words (pub : Fin 13 → Word w) (s : Word w) (m : Memory w) :
    writer.words pub s m = List.ofFn (fun j : Fin 12 ↦ pub j.succ) := by
  rw [Recipe.words, writer_values]
  rfl

open private stores_at from OAI.Computability.VPVNP.CompressorRecordsCursorInit

/-- The worker uses 12 external probes, all writes. The returned cursor
advances once even when the first input field has numerical value zero. -/
theorem write_native (pub : Fin 13 → Word w) (s : Word w) (m : Memory w)
    (fit : (pub 0).val+12 ≤ 2^w) :
    let M := writer.table.instantiate w pub
    let rep := writer.report pub s m
    execute M.program 42 (M.program.start s) m [] = some rep ∧ rep.result = some (s+1) ∧
      (∀ j : Fin 12, after m rep.events ((pub 0).val+j.val) = pub j.succ) ∧
      (∀ addr, addr < (pub 0).val ∨ (pub 0).val+12 ≤ addr → after m rep.events addr = m addr) ∧
      rep.events.length = 41 ∧ rep.probes = 12 ∧ choiceBits rep.events = [] := by
  intro M rep
  have room : (writer.address pub s m).val + (9+3) ≤ 2^w := by rwa [writer_address]
  have stored := row_stores writer pub s m room
  rw [writer_address,writer_words] at stored
  obtain ⟨ht,hp,hc⟩ := report_cost writer pub s m
  refine ⟨execute_row writer pub s m [] 42 (by decide),rfl,?_,?_,ht,hp,hc⟩
  · intro j
    have hj : j.val < (List.ofFn (fun i : Fin 12 ↦ pub i.succ)).length :=
      by simpa only [List.length_ofFn] using j.isLt
    exact (stores_at _ _ stored (by simpa using fit) hj).trans (List.getElem_ofFn hj)
  · intro addr h
    exact row_outside writer pub s m room addr (by rwa [writer_address])

open SourceTransport
open private storeLog eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private store_writes store_no_reads from OAI.Computability.VPVNP.CompressorFormulaFootprint

/-- Native worker footprints. Planner evaluation of the operand expressions
takes place in a separate burst. -/
theorem writer_footprint (pub : Fin 13 → Word w) (s : Word w) (m : Memory w)
    (fit : (pub 0).val+12 ≤ 2^w) (data : ℕ → Prop) (cells : ∀ i : Fin 12, data ((pub 0).val+i.val)) :
    let es := (writer.report pub s m).events
    Reads (fun _ ↦ False) es ∧ Writes data es := by
  intro es
  have count : countProbes (evaluate pub s m writer.lines (fun _ ↦ 0)).1 = 0 :=
    (eval_cost pub s m writer.lines _).2
  have init := FlowFootprint.bounds_of_noProbes (fun _ ↦ False) data count
  have stores : Writes data (storeLog (writer.address pub s m) (writer.words pub s m)) := by
    rw [writer_address,writer_words]
    apply store_writes
    intro i
    have hi : i.val < 12 := by simpa only [List.length_ofFn] using i.isLt
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : i.val < 2^w),
      Nat.mod_eq_of_lt (by omega : (pub 0).val+i.val < 2^w)]
    exact cells ⟨i.val,hi⟩
  constructor <;> intro a v h
  all_goals simp only [es,Recipe.report,List.mem_append,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_false] at h
  · exact h.elim (init.1 a v) (store_no_reads (fun _ ↦ False) _ _ a v)
  · exact h.elim (init.2 a v) (stores a v)

/-- Evaluate a phase's public parameters before executing its worker. -/
def bank (visit : Visit) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Fin visit.worker.params → Word w :=
  fun j ↦ (visit.params j).eval pub s m

/-- The address and all data supplied by the actual online planner. -/
theorem current_bank (F : Shape) (step recordLimit slotDegree : ℕ) (v : Fields)
    (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    let data : Fin 13 → Word w := bank (current F step recordLimit slotDegree v) pub s m
    data 0 = (address step 15).eval pub s m ∧ ∀ j : Fin 12,
      data j.succ = (fieldExprs F step recordLimit slotDegree v j).eval pub s m := ⟨rfl,fun _ ↦ rfl⟩

/-- Data values supplied by the physical child-directory implementation at this substep. -/
structure Placement where
  /-- Number of output sites indexing the completed placement directory. -/
  newSites : ℕ
  /-- Natural base address of the column recording the owner of each old site. -/
  owner : ℕ
  /-- Natural base address of the column recording the number of children of each output site. -/
  count : ℕ
  /-- Natural base address of the fixed-stride child-identifier rows. -/
  row : ℕ
  /-- Number of child identifiers reserved in each output site's row. -/
  cap : ℕ

/-- The planner's five placement expressions evaluate to the recorded site count, column bases
and row capacity. -/
def Placement.reads (data : Placement) (v : Fields) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Prop :=
  v.newSites.eval pub s m = (data.newSites : Word w) ∧ v.owner.eval pub s m = (data.owner : Word w) ∧
    v.count.eval pub s m = (data.count : Word w) ∧ v.row.eval pub s m = (data.row : Word w) ∧
      v.cap.eval pub s m = (data.cap : Word w)

/-- The twelve metadata words at offsets 15 through 26, including the DFS stride, argument
frame, incidence pointers and child directory. -/
def payload (recordLimit slotDegree degree n actualIn width oldSites : ℕ) (x : Placement) : Fin 12 → ℕ :=
  ![recordLimit+2,degree,n,PairSimulation.NodeArguments.frameStride slotDegree n,actualIn,width,
    oldSites,x.newSites,x.owner,x.count,x.row,x.cap]

/-- Agreement with the DFS row stride, private arena, actual incidence pointers,
and the five placement operands. This statement allows arbitrarily different
old and new site counts. -/
theorem field_values {L : Layout} {step : ℕ} {pub : Fin 5 → Word w} {s : Word w} {m : Memory w}
    (recordLimit slotDegree : ℕ) (v : Fields) (x : Placement)
    {n dg oldSites actualIn width : ℕ} (firstHead : BlockHeaderPlan.firstHeader.eval pub s m = (levelStart L 0 : Word w))
    (firstRoom : levelStart L 0+29 < 2^w) (nCell : m (levelStart L 0+29) = (n : Word w))
    (deg : (degree step).eval pub s m = (dg : Word w)) (sitesEq : (sites step).eval pub s m = (oldSites : Word w))
    (inPtr : (incidence L.shape step 4).eval pub s m = (actualIn : Word w))
    (widthPtr : (incidence L.shape step 5).eval pub s m = (width : Word w))
    (placement : x.reads v pub s m) (j : Fin 12) :
    (fieldExprs L.shape step recordLimit slotDegree v j).eval pub s m =
      (payload recordLimit slotDegree dg n actualIn width oldSites x j : Word w) := by
  have len : lengthWord.eval pub s m = (n : Word w) := by
    change m (BlockHeaderPlan.firstHeader.eval pub s m + (29 : Word w)).val = _
    rw [firstHead, ← show ((levelStart L 0+29 : ℕ) : Word w) = (levelStart L 0 : Word w)+29 by simp,
      Fin.val_natCast, Nat.mod_eq_of_lt firstRoom, nCell]
  obtain ⟨newSites,owner,count,row,cap⟩ := placement
  fin_cases j
  · rfl
  · exact deg
  · exact len
  · change ((2*slotDegree : ℕ) : Word w)*lengthWord.eval pub s m+1 = ((2*slotDegree*n+1 : ℕ) : Word w)
    simp only [len,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  · exact inPtr
  · exact widthPtr
  · exact sitesEq
  · exact newSites
  · exact owner
  · exact count
  · exact row
  · exact cap

/-- The one-store worker's report, writing the given value at its destination and returning
cursor one. -/
def storeReport (dest val : Word w) : Report w :=
  ⟨[.tick,.tick,.tick,.write dest val,.tick,.tick],some (0+1)⟩

private theorem raw_store (dest val : Expr) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    BlockHeaderRun.rawCall (BlockPlanner.publish dest val) pub s m 7 =
      some (storeReport (dest.eval pub s m) (val.eval pub s m)) := by
  let data : Fin 2 → Word w := bank (BlockPlanner.publish dest val) pub s m
  exact (BlockPlanner.publish_native dest val data 0 m).1

private theorem store_after (m : Memory w) (dest val : Word w) :
    after m (storeReport dest val).events = writeMemory m dest val := rfl

/-- The source relation retains the actual public bank, input cursor and
individual native budget of each visit. -/
def Source (pub : Fin 5 → Word w) (s : Word w) (visit : Visit) (m : Memory w) (rs : List (Report w)) :=
  ∃ (fuel : ℕ) (rep : Report w), rs = [rep] ∧ 0 < fuel ∧ fuel ≤ 42 ∧ rep.result = some 1 ∧
    BlockHeaderRun.rawCall visit pub s m fuel = some rep

/-- Each metadata row contributes one completed source scan and one real
worker run at its planner-supplied operands. -/
theorem Source.packet {pub : Fin 5 → Word w} {s : Word w} {visit : Visit} {m : Memory w}
    {rs : List (Report w)} (h : Source pub s visit m rs) :
    StageFrame.Scanned 0 1 rs ∧ ∃ fuel, 0 < fuel ∧ fuel ≤ 42 ∧
      let M := (visit.worker.table.instantiate w (bank visit pub s m)).program
      runSegment M fuel (some (visit.initial.eval pub s m)) m [[]] = some rs := by
  obtain ⟨fuel,r,rfl,positive,bounded,ret,call⟩ := h
  refine ⟨.next (by decide) (by simpa using ret) (.done 1),fuel,positive,bounded,?_⟩
  dsimp only
  rw [runSegment]
  change execute (visit.worker.table.instantiate w (bank visit pub s m)).program fuel
    ((visit.worker.table.instantiate w (bank visit pub s m)).program.start (visit.initial.eval pub s m)) m [] = some r at call
  rw [call]
  rfl

/-- The three visits run on consecutive memory images. All other addresses,
including the original layer base, cursor frame, and both pointer banks,
retain their original values. -/
theorem publish_metadata {L : Layout} {first step : ℕ} {pub : Fin 5 → Word w}
    {s : Word w} (m : Memory w) (entry : Entry L first pub s m)
    (recordLimit slotDegree : ℕ) (role : Role) (v : Fields) (oldSites : ℕ)
    (sitesEq : (sites step).eval pub s m = (oldSites : Word w))
    (wide : 30 ≤ L.shape.scalarFields) (nextLevel : first+(step+1) < L.levels)
    (room : endAddress L < 2^w) (pitchBefore : (pub 1-1).val < levelStart L (first+step)) :
    let head := levelStart L (first+step)
    let next := levelStart L (first+(step+1))
    ∃ rs, SourceWalk (Source pub s) (visits L.shape step recordLimit slotDegree role v) m rs ∧
      let out := after m (eventLog rs)
      (∀ j : Fin 12, out (head+15+j.val) = (fieldExprs L.shape step recordLimit slotDegree v j).eval pub s m) ∧
      out (next+14) = m (head+14) + ((recordLimit+2 : ℕ) : Word w) * (oldSites : Word w) ∧
      out (next+27) = (role.code : Word w) ∧
      (∀ x, (x < head+15 ∨ head+27 ≤ x) → x ≠ next+14 → x ≠ next+27 → out x = m x) ∧
      Reads (fun _ ↦ False) (eventLog rs) ∧
      Writes (fun x ↦ (head+15 ≤ x ∧ x<head+27) ∨ x=next+14 ∨ x=next+27) (eventLog rs) ∧
      rs.length = 3 ∧ RAMBuckets.cost Report.probes rs = 17 := by
  intro head next
  have advanceHead (i : ℕ) : levelStart L (i+1) = levelStart L i + levelWords L := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  have hw : 30 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
  have hn : head+30 ≤ next := by
    change levelStart L (first+step)+30 ≤ levelStart L (first+(step+1))
    rw [← Nat.add_assoc,advanceHead]
    omega
  have hi := level_room L room (⟨first+(step+1),nextLevel⟩ : Fin L.levels)
  have hnext : next+30 < 2^w := by
    change levelStart L ((first+(step+1))+1) < 2^w at hi
    rw [advanceHead] at hi
    change levelStart L (first+(step+1))+30 < _
    omega
  let data : Fin 13 → Word w := bank (current L.shape step recordLimit slotDegree v) pub s m
  have dest : (data 0).val = head+15 := by
    change ((address step 15).eval pub s m).val = _
    rw [eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt (by change head+15 < _; omega)]
  let r := writer.report data 0 m
  let m₁ := after m r.events
  obtain ⟨raw₁,_,fields,unchanged,_,probes,_⟩ := write_native data 0 m (by rw [dest]; omega)
  rw [dest] at fields unchanged
  have keep₁ (addr : ℕ) (h : addr < head+15 ∨ head+27 ≤ addr) : m₁ addr = m addr := by
    apply unchanged; omega
  have e₁ : Entry L first pub s m₁ := ⟨entry.pointer,(keep₁ _ (.inl (by omega))).trans entry.pitch⟩
  have prefixEq : (nextBase step recordLimit).eval pub s m₁ =
      m (head+14)+((recordLimit+2 : ℕ) : Word w)*(oldSites : Word w) := by
    have read (i : ℕ) (hi : i < 15) :
        (scalar step i).eval pub s m₁ = (scalar step i).eval pub s m := by
      rw [eval_scalar e₁,eval_scalar entry]
      · exact keep₁ _ (.inl (by change head+i < _; omega))
      all_goals change head+i < 2^w; omega
    have pos : (sites step).eval pub s m₁ = (sites step).eval pub s m := by
      change (scalar step 0).eval pub s m₁ * (scalar step 2).eval pub s m₁ =
        (scalar step 0).eval pub s m * (scalar step 2).eval pub s m
      rw [read 0 (by decide),read 2 (by decide)]
    change (scalar step 14).eval pub s m₁ + ((recordLimit+2 : ℕ) : Word w)*(sites step).eval pub s m₁ = _
    rw [read 14 (by decide),eval_scalar entry, pos,sitesEq]
    change head+14 < 2^w
    omega
  let prefixWord := m (head+14)+((recordLimit+2 : ℕ) : Word w)*(oldSites : Word w)
  let r₂ := storeReport ((next+14 : ℕ) : Word w) prefixWord
  let m₂ := after m₁ r₂.events
  have raw₂ : BlockHeaderRun.rawCall (outputBase step recordLimit) pub s m₁ 7 = some r₂ := by
    rw [outputBase, raw_store, eval_address e₁,prefixEq]
  have m₂eq : m₂ = writeMemory m₁ ((next+14 : ℕ) : Word w) prefixWord := store_after ..
  have keep₂ (addr : ℕ) (h : addr ≠ next+14) : m₂ addr = m₁ addr := by
    rw [m₂eq,writeMemory,Fin.val_natCast,Nat.mod_eq_of_lt (by omega),ite_eq_right h]
  have e₂ : Entry L first pub s m₂ := ⟨entry.pointer,(keep₂ _ (by omega)).trans e₁.pitch⟩
  let r₃ := storeReport ((next+27 : ℕ) : Word w) (role.code : Word w)
  let m₃ := after m₂ r₃.events
  have raw₃ : BlockHeaderRun.rawCall (outputRole step role) pub s m₂ 7 = some r₃ := by
    rw [outputRole,raw_store,eval_address e₂]; rfl
  have m₃eq : m₃ = writeMemory m₂ ((next+27 : ℕ) : Word w) (role.code : Word w) := store_after ..
  have keep₃ (addr : ℕ) (h : addr ≠ next+27) : m₃ addr = m₂ addr := by
    rw [m₃eq,writeMemory,Fin.val_natCast,Nat.mod_eq_of_lt (by omega),ite_eq_right h]
  let rs := [r,r₂,r₃]
  have singleton (mem : Memory w) (r : Report w) : after mem (eventLog [r]) = after mem r.events := by
    simp [eventLog]
  have seq₂ : SourceWalk (Source pub s) [outputBase step recordLimit,outputRole step role] m₁ [r₂,r₃] := by
    apply SourceWalk.next (rs := [r₂]) (ts := [r₃]) ⟨7,r₂,rfl,by decide,by decide,by simp [r₂,storeReport],raw₂⟩
    rw [singleton]
    exact SourceWalk.singleton ⟨7,r₃,rfl,by decide,by decide,by simp [r₃,storeReport],raw₃⟩
  have seq : SourceWalk (Source pub s) (visits L.shape step recordLimit slotDegree role v) m rs := by
    apply SourceWalk.next (rs := [r]) (ts := [r₂,r₃]) ⟨42,r,rfl,by decide,le_rfl,by simp [r,Recipe.report],raw₁⟩
    rwa [singleton]
  have final : after m (eventLog rs) = m₃ := by
    simp only [rs,eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,after,List.foldl_append]
    rfl
  refine ⟨rs,seq,?_⟩
  rw [final]
  refine ⟨?_,?_,?_,?_,?_,?_,rfl,?_⟩
  · intro j
    have hj := j.isLt
    rw [keep₃ _ (by omega),keep₂ _ (by omega)]
    exact fields j
  · rw [keep₃ _ (by omega),m₂eq,writeMemory,Fin.val_natCast,Nat.mod_eq_of_lt (by omega),ite_eq_left rfl]
  · rw [m₃eq,writeMemory,Fin.val_natCast,Nat.mod_eq_of_lt (by omega),ite_eq_left rfl]
  · intro x hx h₂ h₃
    exact (keep₃ _ h₃).trans ((keep₂ _ h₂).trans (keep₁ _ hx))
  · intro addr val read
    have hr := (writer_footprint data 0 m (by rw [dest]; omega) (fun _ ↦ True) (fun _ ↦ trivial)).1
    change Event.read addr val ∈ r.events ++ (r₂.events ++ (r₃.events ++ [])) at read
    exact hr addr val (by simpa [r₂,r₃,storeReport] using read)
  · intro addr val wr
    let region := fun x ↦ (head+15 ≤ x ∧ x<head+27) ∨ x=next+14 ∨ x=next+27
    have hw := (writer_footprint data 0 m (by rw [dest]; omega) region
      (fun i ↦ Or.inl (by rw [dest]; have := i.isLt; omega))).2
    change Event.write addr val ∈ r.events ++ (r₂.events ++ (r₃.events ++ [])) at wr
    rcases List.mem_append.mp wr with h | h
    · exact hw addr val h
    · simp only [r₂,r₃,storeReport,List.mem_append,List.mem_cons,List.not_mem_nil,reduceCtorEq,
        Event.write.injEq,false_or,or_false] at h
      rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact Or.inr (Or.inl (Nat.mod_eq_of_lt (by omega)))
      · exact Or.inr (Or.inr (Nat.mod_eq_of_lt (by omega)))
  · change (1+r.probes)+(1+1+(1+1+0)) = 17
    change r.probes = 12 at probes
    omega

open PairSimulation.TraversalRoles PairSimulation.TraversalRows

/-- The prefix word advanced by the metadata worker is precisely the
ordinary DFS address of the next layer in the selected traversal. -/
theorem next_layerBase (cap start : ℕ) (layers : List TaggedLayer) (i : Fin layers.length) :
    ((layerBase cap start layers i.val : ℕ) : Word w) +
        ((cap+2 : ℕ) : Word w)*(layers[i].layer.count : Word w) =
      ((layerBase cap start layers (i.val+1) : ℕ) : Word w) := by
  have h : layerBase cap start layers (i.val+1) = layerBase cap start layers i.val +
      (cap+2)*layers[i].layer.count := by
    simp only [layerBase,words,List.take_succ_eq_append_getElem i.isLt,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.add_assoc]
    rfl
  simp only [h,Nat.cast_add,Nat.cast_mul]

/-- A real selected substep determines the same producing-role word as the
traversal's layer list. -/
def producingRole {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    {a b l g : ℕ} {X : Compression.State a l} {p : Compression.StatePass R X b g} :
    PassOrigin B f hf p → BlockMetadata.Role
  | .shrink _ _ _ => .shrink
  | .refresh _ => .refresh

theorem producingRole_code {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    (v : SelectedLevel B f hf) : (producingRole v.origin).code = (tagLevel B f hf v).code := by
  obtain ⟨a,l,b,g,X,p,o,z,bits⟩ := v
  cases o <;> rfl

end CompressorRecords.BlockMetadata

end VPVNP
end Computability
end OAI
