import OAI.Computability.VPVNP.PairTraversalArena

/-!
# Reading traversal workers from the resident terminal header

The cursor layer precedes the outputs of the chosen compression passes. Each
output layer uses its producing pass's preimage directory and the DFS bases
of that pass's input and output states. Tags refer to the output state's
producing role, including the final state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalControllerInputs

open BurstRAM BurstRAM.PrivateRAM CompressorRecords LocalHistory NetworkKernel Compression
open TraversalRows DirectoryRun TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ}

/-- The last 32 words of the pair's square workspace are the terminal header. -/
def terminalHead (pub : Fin 11 → Word w) : Word w :=
  let radix := BinaryOp.shiftLeft.eval 1 (pub 7)
  pub 2 + radix * radix - 32

/-- The word address equals the natural square-workspace formula whenever
the public address width fits the shift and the 32-word header fits the square. -/
theorem terminalHead_eq_nat (pub : Fin 11 → Word w) (hw : (pub 7).val < w)
    (h32 : 32 ≤ (pub 2).val + 2 ^ (pub 7).val * 2 ^ (pub 7).val) :
    terminalHead pub = (((pub 2).val + 2 ^ (pub 7).val * 2 ^ (pub 7).val - 32 : ℕ) : Word w) := by
  have hone : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have radix : BinaryOp.shiftLeft.eval 1 (pub 7) = ((2 ^ (pub 7).val : ℕ) : Word w) := by
    simp only [BinaryOp.eval,hw,ite_true,hone,Nat.shiftLeft_eq,Nat.one_mul,Fin.ofNat_eq_cast]
  simp only [terminalHead,radix,Nat.cast_sub h32,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hb : ((pub 2).val : Word w) = pub 2 := Fin.ext (Nat.mod_eq_of_lt (pub 2).isLt)
  rw [hb]

/-- Read a terminal-header field at its machine-word offset in the supplied external memory. -/
def terminalField (pub : Fin 11 → Word w) (m : Memory w) (field : ℕ) : Word w :=
  m (terminalHead pub + (field : Word w)).val

/-- Compute the physical head of level j from the first-level word and the level pitch saved in
the terminal header. -/
def levelHead (pub : Fin 11 → Word w) (m : Memory w) (j : ℕ) : Word w :=
  terminalField pub m 16 + (j : Word w) * terminalField pub m 17

/-- Read a selected level-header field using the terminal header's runtime level geometry. -/
def levelField (pub : Fin 11 → Word w) (m : Memory w) (j field : ℕ) : Word w :=
  m (levelHead pub m j + (field : Word w)).val

/-- The input site's count comes from its first pass, or from the terminal
site count when there are no passes. Later counts come from their producer. -/
def siteCount (pub : Fin 11 → Word w) (m : Memory w) : ℕ → Word w
  | 0 => if (terminalField pub m 1).val = 1 then terminalField pub m 7 else levelField pub m 0 21
  | j+1 => levelField pub m j 22

/-- Assemble the four role-tag parameters from the terminal displacement, current row base, row
pitch, and stored producing role. -/
def tagParams (pub : Fin 11 → Word w) (m : Memory w) (j : ℕ) : Fin 4 → Word w :=
  ![terminalField pub m 14, levelField pub m j 14, terminalField pub m 15, levelField pub m j 27]

/-- Read the initial row base and row pitch for writing cursor leaf rows. -/
def leafParams (pub : Fin 11 → Word w) (m : Memory w) : Fin 2 → Word w :=
  ![levelField pub m 0 14, terminalField pub m 15]

/-- Fiber worker for pass `i` writes the rows of state `i+1`. -/
def fiberParams (pub : Fin 11 → Word w) (m : Memory w) (i : ℕ) : Fin 6 → Word w :=
  ![levelField pub m i 24, levelField pub m i 25, levelField pub m i 26,
    levelField pub m i 14, levelField pub m (i+1) 14, terminalField pub m 15]

/-- A fiber is the tagged output together with the corresponding raw
placement directory's six public words. -/
abbrev Fiber (w : ℕ) := TaggedLayer × (Fin 6 → Word w)

/-- Chronological translation of tagged output levels into native row workers. -/
def fiberWorkers (cap : ℕ) (previous base : ℕ) : List (Fiber w) → List (Worker w)
  | [] => []
  | (l, p) :: ls => .fiber p cap previous base l.layer.count ::
      fiberWorkers cap base (endPos cap base l.layer) ls

theorem fiberWorkers_length (cap previous base : ℕ) (ls : List (Fiber w)) :
    (fiberWorkers cap previous base ls).length = ls.length := by
  induction ls generalizing previous base with
  | nil => rfl
  | cons h ls ih => simp [fiberWorkers, ih]

/-- The `i`-th fiber connects states `i` and `i+1`. The last fiber uses
its output state header by precisely the same formula. -/
theorem fiberWorkers_at (cap base : ℕ) (old : TaggedLayer) (ls : List (Fiber w))
    (i : Fin ls.length) :
    (fiberWorkers cap base (endPos cap base old.layer) ls)[i.val]? = some (.fiber ls[i].2 cap
      (layerBase cap base (old :: ls.map Prod.fst) i.val)
      (layerBase cap base (old :: ls.map Prod.fst) (i.val+1)) ls[i].1.layer.count) := by
  induction ls generalizing old base with
  | nil => exact Fin.elim0 i
  | cons l ls ih =>
    cases i using Fin.cases with
    | zero => simp [fiberWorkers, layerBase_zero, layerBase_cons]
    | succ i =>
      simpa only [Fin.getElem_fin, Fin.val_succ, fiberWorkers, List.getElem?_cons_succ,
        List.getElem_cons_succ, List.map_cons, layerBase_cons] using ih (endPos cap base old.layer) l.1 i

/-- The full schedule has one leaf worker before the fiber workers. -/
def rowWorkers (cap base : ℕ) (old : TaggedLayer) (ls : List (Fiber w)) : List (Worker w) :=
  Worker.leaf cap base old.layer.count :: fiberWorkers cap base (endPos cap base old.layer) ls

/-- Physical header cells for one finished compressor branch. Addresses here
are ordinary natural addresses, independent of the controller's word arithmetic. -/
structure Resident (pub : Fin 11 → Word w) (m : Memory w) (H first pitch offset cap base : ℕ)
    (old : TaggedLayer) (ls : List (Fiber w)) : Prop where
  header : terminalHead pub = (H : Word w)
  headerFits : H + 32 ≤ 2 ^ w
  levelFits : ∀ j ≤ ls.length, first + j * pitch + 28 ≤ 2 ^ w
  firstHead : m (H+16) = (first : Word w)
  levelPitch : m (H+17) = (pitch : Word w)
  levels : (m (H+1)).val = ls.length + 1
  roleOffset : m (H+14) = (offset : Word w)
  rowStride : m (H+15) = ((cap + 2 : ℕ) : Word w)
  currentBase : ∀ j ≤ ls.length, m (first + j*pitch + 14) =
    (layerBase cap base (old :: ls.map Prod.fst) j : Word w)
  role : ∀ j : Fin (old :: ls.map Prod.fst).length,
    m (first + j.val*pitch + 27) = ((old :: ls.map Prod.fst)[j].role.code : Word w)
  initial : ls ≠ [] → (m (first+21)).val = old.layer.count
  terminalSites : ls = [] → (m (H+7)).val = old.layer.count
  produced : ∀ i : Fin ls.length, (m (first + i.val*pitch + 22)).val = ls[i].1.layer.count
  childCounts : ∀ i : Fin ls.length, m (first + i.val*pitch + 24) = ls[i].2 3
  childLists : ∀ i : Fin ls.length, m (first + i.val*pitch + 25) = ls[i].2 5
  childCapacity : ∀ i : Fin ls.length, m (first + i.val*pitch + 26) = ls[i].2 4

variable {pub : Fin 11 → Word w} {m : Memory w} {H first pitch offset cap base : ℕ}
variable {old : TaggedLayer} {ls : List (Fiber w)}
variable (d : Resident pub m H first pitch offset cap base old ls)

include d in
theorem terminal_read (field : ℕ) (h : field < 32) :
    terminalField pub m field = m (H+field) := by
  simp only [terminalField,d.header,← Nat.cast_add,Fin.val_natCast]
  rw [Nat.mod_eq_of_lt ((Nat.add_lt_add_left h H).trans_le d.headerFits)]

include d in
theorem level_read (j field : ℕ) (hj : j ≤ ls.length) (h : field < 28) :
    levelField pub m j field = m (first+j*pitch+field) := by
  simp only [levelField,levelHead,terminal_read d 16 (by decide),terminal_read d 17 (by decide),
    d.firstHead,d.levelPitch,← Nat.cast_mul,← Nat.cast_add,Fin.val_natCast]
  rw [Nat.mod_eq_of_lt ((Nat.add_lt_add_left h _).trans_le (d.levelFits j hj))]

include d in
theorem count_zero : (siteCount pub m 0).val = old.layer.count := by
  simp only [siteCount,terminal_read d 1 (by decide),d.levels,terminal_read d 7 (by decide),
    level_read d 0 21 (Nat.zero_le _) (by decide),Nat.zero_mul,Nat.add_zero]
  by_cases h : ls = []
  · simp [h,d.terminalSites h]
  · have hl : ls.length ≠ 0 := fun e => h (List.length_eq_zero_iff.mp e)
    simp [hl,d.initial h]

include d in
theorem count_succ (i : Fin ls.length) : (siteCount pub m (i.val+1)).val = ls[i].1.layer.count :=
  (congrArg Fin.val (level_read d i.val 22 i.isLt.le (by decide))).trans (d.produced i)

include d in
theorem fiber_params (i : Fin ls.length) :
    fiberParams pub m i.val = workerData ls[i].2 cap
      (layerBase cap base (old :: ls.map Prod.fst) i.val)
      (layerBase cap base (old :: ls.map Prod.fst) (i.val+1)) := by
  simp only [fiberParams,workerData,level_read d i.val 24 i.isLt.le (by decide), d.childCounts i,
    level_read d i.val 25 i.isLt.le (by decide),d.childLists i,
    level_read d i.val 26 i.isLt.le (by decide),d.childCapacity i,
    level_read d i.val 14 i.isLt.le (by decide),d.currentBase _ i.isLt.le,
    level_read d (i.val+1) 14 i.isLt (by decide),d.currentBase _ i.isLt,
    terminal_read d 15 (by decide),d.rowStride]

include d in
theorem leaf_params : leafParams pub m = LeafWorker.directory w cap base := by
  simp only [leafParams,LeafWorker.directory,level_read d 0 14 (Nat.zero_le _) (by decide),
    d.currentBase 0 (Nat.zero_le _),layerBase_zero,terminal_read d 15 (by decide),d.rowStride]

include d in
theorem tag_params (j : Fin (old :: ls.map Prod.fst).length) :
    tagParams pub m j.val = Native.params offset cap (layerBase cap base (old :: ls.map Prod.fst) j.val)
      ((old :: ls.map Prod.fst)[j].role.code : Word w) := by
  have hj : j.val ≤ ls.length := by simpa only [List.length_cons,List.length_map,Nat.lt_succ_iff] using j.isLt
  simp only [tagParams,Native.params,terminal_read d 14 (by decide),d.roleOffset,
    level_read d j.val 14 hj (by decide),d.currentBase _ hj,terminal_read d 15 (by decide),
    d.rowStride,level_read d j.val 27 hj (by decide),d.role j]

/-- Lookup of a row worker supplies its exact count and public operand bank. -/
def RowAt (pub : Fin 11 → Word w) (m : Memory w) (j : ℕ) : Worker w → Prop
  | .leaf cap base count => j = 0 ∧ (siteCount pub m j).val = count ∧
      leafParams pub m = LeafWorker.directory w cap base
  | .fiber p cap previous base count => ∃ i, j = i+1 ∧ (siteCount pub m j).val = count ∧
      fiberParams pub m i = workerData p cap previous base

/-- The controller has one pair of row/tag stages per state level. Every
admitted ordinal selects the exact chronological worker and role. -/
structure Schedule (pub : Fin 11 → Word w) (m : Memory w) (offset cap base : ℕ)
    (tags : List TaggedLayer) (jobs : List (Worker w)) : Prop where
  total : (terminalField pub m 1).val = tags.length
  jobs_length : jobs.length = tags.length
  lookup : ∀ j : Fin tags.length,
    (siteCount pub m j.val).val = tags[j].layer.count ∧
    tagParams pub m j.val = Native.params offset cap (layerBase cap base tags j.val)
      (tags[j].role.code : Word w) ∧ RowAt pub m j.val (jobs[j.val]'(jobs_length.symm ▸ j.isLt))

include d in
theorem resident_schedule : Schedule pub m offset cap base (old :: ls.map Prod.fst) (rowWorkers cap base old ls) := by
  have len : (rowWorkers cap base old ls).length = (old :: ls.map Prod.fst).length := by
    simp [rowWorkers,fiberWorkers_length]
  refine ⟨by simpa only [terminal_read d 1 (by decide), List.length_cons,List.length_map] using d.levels,
    len,fun j => ⟨?_,tag_params d j,?_⟩⟩
  · cases j using Fin.cases with
    | zero => exact count_zero d
    | succ i =>
      let i' : Fin ls.length := ⟨i.val,by simpa using i.isLt⟩
      simpa only [Fin.getElem_fin,Fin.val_succ,List.getElem_cons_succ,List.getElem_map] using count_succ d i'
  · cases j using Fin.cases with
    | zero => exact ⟨rfl,count_zero d,leaf_params d⟩
    | succ i =>
      let i' : Fin ls.length := ⟨i.val,by simpa using i.isLt⟩
      have e := fiberWorkers_at cap base old ls i'
      rw [List.getElem?_eq_getElem (by rw [fiberWorkers_length]; exact i'.isLt),Option.some.injEq] at e
      have hi : i.val < (fiberWorkers cap base (endPos cap base old.layer) ls).length := by
        rw [fiberWorkers_length]
        exact i'.isLt
      change RowAt pub m (i.val+1) ((fiberWorkers cap base (endPos cap base old.layer) ls)[i.val]'hi)
      rw [e]
      exact ⟨i.val,rfl,count_succ d i',fiber_params d i'⟩

variable {A k : Type*} [CommRing A] [Field k] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f}

open private castOrders from OAI.Computability.VPVNP.PairTraversalSelectedOrder
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open private castDirectories collectDirectories from OAI.Computability.VPVNP.PairTraversalLevelDirectories

omit [CommRing A] in
private theorem workers_cast {N M Y : Network} (e : N = M) (c : TermChain A M Y)
    (ords : ChainOrders c) (old : Order M.Site) {m : Memory w} {limit : ℕ}
    (dirs : Directories m limit c ords old) (cap previous base : ℕ) :
    workers (e.symm ▸ c : TermChain A N Y) (castOrders e c ords) (e.symm ▸ old)
      (castDirectories e c ords old m limit dirs) cap previous base =
      workers c ords old dirs cap previous base := by cases e; rfl

private noncomputable def taggedLevel (v : SelectedLevel B f hf) : TaggedLayer :=
  ⟨levelLayer B f hf v, tagLevel B f hf v⟩

/-- The typed directory list keeps the address of every occurrence of a
selected level, even when two levels have equal mathematical data. -/
noncomputable def levelFibers (vs : List (SelectedLevel B f hf)) {m : Memory w} {limit : ℕ}
    (ds : (i : Fin vs.length) → LevelDirectory vs[i] m limit) : List (Fiber w) :=
  List.ofFn fun i => (taggedLevel vs[i], (ds i).pub)

private theorem levelFibers_cons (v : SelectedLevel B f hf) (vs : List (SelectedLevel B f hf))
    {m : Memory w} {limit : ℕ} (ds : (i : Fin (v :: vs).length) → LevelDirectory (v :: vs)[i] m limit) :
    levelFibers (v :: vs) ds = (taggedLevel v, (ds 0).pub) ::
      levelFibers vs (fun i => ds i.succ) :=
  List.ofFn_succ

set_option maxHeartbeats 800000 in
private theorem collect_workers {a g b n : ℕ} {X : State a g}
    (E : StateExecution A b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (o : PassOrigins B f hf E) (data : E.Records) (z : E.Choices) {m : Memory w} {limit : ℕ}
    (ds : let vs := collectLevels B f hf E W r o z
      (i : Fin vs.length) → LevelDirectory vs[i] m limit) (cap previous base : ℕ) :
    workers (E.termChain data z) (branchOrders E data z) (siteOrder X)
      (collectDirectories E W r o data z m limit ds) cap previous base =
      fiberWorkers cap previous base (levelFibers (collectLevels B f hf E W r o z) ds) := by
  induction E generalizing previous base with
  | done => rfl
  | @more a₀ g₀ a₁ g₁ X₀ p tail ih =>
    let v : SelectedLevel B f hf := ⟨a₀,g₀,a₁,g₁,X₀,p,o.1,z.1,r.1.select.encode z.1⟩
    let E' := tail z.1
    let vs := collectLevels B f hf E' (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2
    let rest (i : Fin vs.length) : LevelDirectory vs[i] m limit := ds i.succ
    let data' := data.2 z.1
    let c := E'.termChain data' z.2
    let ords := branchOrders E' data' z.2
    let old := siteOrder (p.next z.1)
    let d := collectDirectories E' (W.2 z.1) (r.2 z.1) (o.2 z.1) data' z.2 m limit rest
    change _ = fiberWorkers cap previous base (levelFibers (v :: vs) ds)
    rw [levelFibers_cons v vs ds]
    apply congrArg (List.cons (Worker.fiber (ds ⟨0,Nat.zero_lt_succ _⟩).pub cap previous base
      (taggedLevel v).layer.count))
    exact (workers_cast (p.output_eq z.1) c ords old d _ _ _).trans
      (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) data' z.2 rest _ _)

theorem levelFibers_tags (vs : List (SelectedLevel B f hf)) {raw : Memory w} {limit : ℕ}
    (ds : (i : Fin vs.length) → LevelDirectory vs[i] raw limit) :
    (levelFibers vs ds).map Prod.fst = vs.map (fun v => ⟨levelLayer B f hf v,tagLevel B f hf v⟩) := by
  simp only [levelFibers,List.map_ofFn,Function.comp_def,taggedLevel]
  simpa only [Fin.getElem_fin] using List.ofFn_getElem_eq_map vs
    (fun v => (⟨levelLayer B f hf v,tagLevel B f hf v⟩ : TaggedLayer))

private theorem collect_first_sites {a g b n : ℕ} {X : State a g}
    (E : StateExecution A b n X) (W : E.MapWitnesses f) (r : ExecutionReaders E W)
    (o : PassOrigins B f hf E) (z : E.Choices) :
    let vs := collectLevels B f hf E W r o z
    ∀ i : Fin vs.length, i.val = 0 → (siteOrder vs[i].input).length = (siteOrder X).length := by
  cases E with
  | done => exact fun i => Fin.elim0 i
  | more p tail =>
    intro vs i hi
    obtain ⟨j,hj⟩ := i
    change j = 0 at hi
    subst j
    rfl

variable (B f hf) {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (base : ℕ) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

/-- Exactly the worker list executed by the selected traversal-arena build. -/
noncomputable def selectedJobs : List (Worker w) :=
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let ords := branchOrders E data z
  let old := siteOrder X
  let dirs := selectedDirectories B f hf T hT X z raw base ds
  .leaf B.recordLimit base old.length ::
    workers c ords old dirs B.recordLimit base (address B.recordLimit base old.length)

theorem selectedJobs_eq : selectedJobs B f hf T hT X z base raw ds =
    rowWorkers B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩
      (levelFibers (executeLevels B f hf T hT X z) ds) := by
  apply congrArg (List.cons _)
  apply collect_workers

/-- Physical fields for the initial state and each selected pass provide all
the operands of the native workers, with the precise chronological schedule. -/
theorem selected_schedule {H first pitch offset : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
    (fields : Resident pub m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds)) :
    Schedule pub m offset B.recordLimit base (TraversalRoles.selected B f hf T hT X z)
      (selectedJobs B f hf T hT X z base raw ds) := by
  have hs := resident_schedule fields
  rw [levelFibers_tags] at hs
  rw [selectedJobs_eq]
  exact hs

/-- Read the public placement words from the real directory for each
occurrence of a selected pass. The count cells are identified with the
mathematical site counts by that directory's old/new count witnesses. -/
theorem selected_resident_of_directory_fields {H first pitch offset : ℕ} {pub : Fin 11 → Word w}
    {m : Memory w}
    (head : terminalHead pub = (H : Word w)) (hfHead : H + 32 ≤ 2^w)
    (firstCell : m (H+16) = (first : Word w)) (pitchCell : m (H+17) = (pitch : Word w))
    (offsetCell : m (H+14) = (offset : Word w)) (strideCell : m (H+15) = ((B.recordLimit+2 : ℕ) : Word w)) :
    let vs := executeLevels B f hf T hT X z
    let tags := TraversalRoles.selected B f hf T hT X z
    (m (H+1)).val = vs.length+1 →
    (∀ j ≤ vs.length, first+j*pitch+28 ≤ 2^w) →
    (∀ j ≤ vs.length, m (first+j*pitch+14) = (layerBase B.recordLimit base tags j : Word w)) →
    (∀ j : Fin tags.length, m (first+j.val*pitch+27) = (tags[j].role.code : Word w)) →
    (∀ i : Fin vs.length, i.val = 0 → m (first+21) = (ds i).pub 0) →
    (vs = [] → (m (H+7)).val = X.positions) →
    (∀ i : Fin vs.length, m (first+i.val*pitch+22) = (ds i).pub 2 ∧
      m (first+i.val*pitch+24) = (ds i).pub 3 ∧
      m (first+i.val*pitch+25) = (ds i).pub 5 ∧ m (first+i.val*pitch+26) = (ds i).pub 4) →
    Resident pub m H first pitch offset B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩
      (levelFibers vs ds) := by
  intro vs tags levels fits cur role oldCount terminalSites directory
  let fibers := levelFibers vs ds
  let leaf : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
  have len : fibers.length = vs.length := List.length_ofFn
  have tagEq : leaf :: fibers.map Prod.fst = tags := by
    rw [show fibers = levelFibers vs ds from rfl,levelFibers_tags]
    rfl
  have countX : (siteOrder X).length = X.positions := by
    change (siteOrder X).length = Fintype.card X.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X).entries
  have cell (i : Fin fibers.length) :
      fibers[i] = (taggedLevel vs[i.cast len],(ds (i.cast len)).pub) := by
    exact List.get_ofFn (fun j : Fin vs.length => (taggedLevel vs[j], (ds j).pub)) i
  change Resident pub m H first pitch offset B.recordLimit base leaf fibers
  refine ⟨head,hfHead,fun j hj => fits j (len ▸ hj),firstCell,pitchCell,levels.trans (congrArg (·+1) len.symm),
    offsetCell,strideCell,fun j hj => tagEq ▸ cur j (len ▸ hj),?_,?_,?_,?_,?_,?_,?_⟩
  · let P (xs : List TaggedLayer) := ∀ j : Fin xs.length,
        m (first+j.val*pitch+27) = (xs[j].role.code : Word w)
    exact (congrArg P tagEq).mpr role
  · intro nonempty
    have pos : 0 < fibers.length := List.length_pos_iff.mpr nonempty
    let i : Fin vs.length := ⟨0,len ▸ pos⟩
    have hi : (siteOrder vs[i].input).length = (siteOrder X).length :=
      collect_first_sites (B := B) (f := f) (hf := hf) (B.execute f hf T hT X)
        _ _ _ z i rfl
    exact (congrArg Fin.val (oldCount i rfl)).trans ((ds i).oldCount.trans hi)
  · intro h
    have vsnil : vs = [] := List.length_eq_zero_iff.mp (len.symm.trans (by rw [h]; rfl))
    exact (terminalSites vsnil).trans countX.symm
  · intro i
    rw [cell i]
    exact (congrArg Fin.val (directory (i.cast len)).1).trans (ds (i.cast len)).newCount
  · intro i
    rw [cell i]
    exact (directory (i.cast len)).2.1
  · intro i
    rw [cell i]
    exact (directory (i.cast len)).2.2.1
  · intro i
    rw [cell i]
    exact (directory (i.cast len)).2.2.2

/-- The physical directory fields select exactly the workers of the reference
arena construction, including the final output layer. -/
theorem selected_schedule_of_directory_fields {H first pitch offset : ℕ} {pub : Fin 11 → Word w}
    {m : Memory w}
    (head : terminalHead pub = (H : Word w)) (hfHead : H + 32 ≤ 2^w)
    (firstCell : m (H+16) = (first : Word w)) (pitchCell : m (H+17) = (pitch : Word w))
    (offsetCell : m (H+14) = (offset : Word w)) (strideCell : m (H+15) = ((B.recordLimit+2 : ℕ) : Word w)) :
    let vs := executeLevels B f hf T hT X z
    let tags := TraversalRoles.selected B f hf T hT X z
    (m (H+1)).val = vs.length+1 →
    (∀ j ≤ vs.length, first+j*pitch+28 ≤ 2^w) →
    (∀ j ≤ vs.length, m (first+j*pitch+14) = (layerBase B.recordLimit base tags j : Word w)) →
    (∀ j : Fin tags.length, m (first+j.val*pitch+27) = (tags[j].role.code : Word w)) →
    (∀ i : Fin vs.length, i.val = 0 → m (first+21) = (ds i).pub 0) →
    (vs = [] → (m (H+7)).val = X.positions) →
    (∀ i : Fin vs.length, m (first+i.val*pitch+22) = (ds i).pub 2 ∧
      m (first+i.val*pitch+24) = (ds i).pub 3 ∧
      m (first+i.val*pitch+25) = (ds i).pub 5 ∧ m (first+i.val*pitch+26) = (ds i).pub 4) →
    Schedule pub m offset B.recordLimit base tags (selectedJobs B f hf T hT X z base raw ds) := by
  intro vs tags levels fits cur role oldCount terminalSites directory
  exact selected_schedule B f hf T hT X z base raw ds
    (selected_resident_of_directory_fields B f hf T hT X z base raw ds head hfHead firstCell pitchCell
      offsetCell strideCell levels fits cur role oldCount terminalSites directory)

end PairSimulation.TraversalControllerInputs

end VPVNP
end Computability
end OAI
