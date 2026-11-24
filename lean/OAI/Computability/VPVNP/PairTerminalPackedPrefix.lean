import OAI.Computability.VPVNP.PairTerminalCalendarBoundary
import OAI.Computability.VPVNP.PairTraversalResidentHandoff
import OAI.Computability.VPVNP.PairTerminalSelectedPrefix
import OAI.Computability.VPVNP.PairTerminalVertexMemory
import OAI.Computability.VPVNP.PairSimulationSharedBitPhase
import OAI.Computability.VPVNP.CompressorDetailedResident

/-!
# Selected calendar data at the physical vertex entry

The packed calendar supplies the terminal bootstrap, width-prefix scan and
traversal construction. Each shared-wire assignment then determines one
physical bit block. At its exit, the earlier parser tables and the final
incidence bank still read their producing values. The final prefix table
reads the computed arc offsets, and the vertex worker sees the actual DFS
rows, role tags and wire bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs TerminalPrefix TerminalPrefix.Linked TerminalLink
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "rowsSize" => words B.recordLimit (ls)
local notation "last" => List.length (List.dropLast (ls))

private theorem move_directories {base H first pitch offset floor : ℕ} {pub : Fin 11 → Word w}
    {src vertex : Memory w} (ds : (i : Fin (vs).length) → LevelDirectory vs[i] src base)
    (d : Resident pub src H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds))
    (lower : ∀ i, floor ≤ ((ds i).pub 1).val)
    (heads : ∀ j ≤ (vs).length, first+j*pitch+28 ≤ base)
    (frame : ∀ x < base, vertex x = src x)
    (same : ∀ j ∈ terminalScalars, vertex (H+j) = src (H+j)) :
    ∃ ds' : (i : Fin (vs).length) → LevelDirectory vs[i] vertex base,
      (∀ i, floor ≤ ((ds' i).pub 1).val) ∧ Resident pub vertex H first pitch offset B.recordLimit base
        ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds') := by
  let nextDirs (i : Fin (vs).length) : LevelDirectory vs[i] vertex base :=
    (ds i).transport fun x hx => (frame x ((ds i).cells_interval hx).2).symm
  have banks : levelFibers (vs) nextDirs = levelFibers (vs) ds := rfl
  refine ⟨nextDirs,lower,?_⟩
  rw [banks]
  exact d.transfer (by simpa only [levelFibers,List.length_ofFn] using heads) frame same

/-- Readback of the selected parser history and the native DFS data after
the four linked stages, for one assignment of the shared bits. -/
structure VertexEntry (L : Layout) (tab : Fin L.shape.tables) (baseBits laneBits : ℕ)
    (pub : Fin 11 → Word w) (calendar vertex : Memory w) (bits : Fin (Y).totalWidth → Bool) : Prop where
  boundedDirectories : ∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] vertex (endAddress L),
    (∀ i, levelsBase L ≤ ((ds i).pub 1).val) ∧ Resident pub vertex (header pub).val (levelStart L 0) (levelWords L) (rowsSize+(Y).totalWidth)
      B.recordLimit (endAddress L) ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds)
  valid : (Entry.resume Stage.vertices (0 : Word w)).Valid (header pub) vertex
  rows : AllRows w vertex B.recordLimit (endAddress L) (endAddress L) (ls)
  roles : Reads w vertex (rowsSize + (Y).totalWidth) B.recordLimit (endAddress L) (tags)
  wires : ∀ i, vertex (endAddress L+rowsSize+i.val) = PrimedInputRAM.encodeBit w (bits i)
  offsets : ∀ i : Fin (arcCount (Y)), (vertex (tableBase L last tab + i.val)).val =
    EndpointBits.offset (width (Y)) i
  raw : ∀ x < endAddress L, x < tableBase L last tab ∨ tableBase L last tab + arcCount (Y) ≤ x →
    vertex x = calendar x
  headers : ∀ j : Fin 21, 0 < j.val → j.val ≠ 12 → j.val ≠ 14 →
    vertex ((header pub).val+j.val) = TerminalBootstrap.values L last
      (TerminalBootstrap.fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab)
      B.recordLimit pub calendar j
  total : (vertex ((header pub).val+12)).val = (Y).totalWidth
  offset : vertex ((header pub).val+14) = ((rowsSize + (Y).totalWidth : ℕ) : Word w)

variable {B f hf T hT X z} in
/-- Every selected placement directory is present in the entry memory. -/
theorem VertexEntry.directories {L : Layout} {tab : Fin L.shape.tables}
    {baseBits laneBits : ℕ} {pub : Fin 11 → Word w} {calendar vertex : Memory w}
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits) :
    ∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] vertex (endAddress L),
      Resident pub vertex (header pub).val (levelStart L 0) (levelWords L) (rowsSize+(Y).totalWidth)
        B.recordLimit (endAddress L) ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds) := by
  obtain ⟨ds,_,d⟩ := entry.boundedDirectories
  exact ⟨ds,d⟩

/-- The native level locator uses the packed origin and pitch still present
in the terminal header at vertex entry. -/
theorem VertexEntry.level_head {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ}
    {pub : Fin 11 → Word w} {calendar vertex : Memory w} {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits) (j : ℕ) :
    levelHead pub vertex j = (levelStart L j : Word w) := by
  obtain ⟨ds,d⟩ := entry.directories
  rw [levelHead, terminal_read d 16 (by decide), terminal_read d 17 (by decide), d.firstHead,
    d.levelPitch, ← Nat.cast_mul, ← Nat.cast_add]
  simp only [levelStart,Nat.zero_mul,Nat.add_zero]

theorem VertexEntry.level_head_val {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ}
    {pub : Fin 11 → Word w} {calendar vertex : Memory w} {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits)
    (j : ℕ) (hj : j ≤ (vs).length) : (levelHead pub vertex j).val = levelStart L j := by
  obtain ⟨ds,d⟩ := entry.directories
  have fit := d.levelFits j (by simpa only [levelFibers,List.length_ofFn] using hj)
  rw [entry.level_head B f hf T hT X z j, Fin.val_natCast, Nat.mod_eq_of_lt]
  simp only [levelStart,Nat.zero_mul,Nat.add_zero] at fit ⊢
  omega

/-- Recover every producing snapshot, including the final pass's successor
incidence. Only addresses before the last scratch bank are used. -/
theorem VertexEntry.payload {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ}
    {pub : Fin 11 → Word w} {calendar vertex : Memory w} {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits)
    (hl : last < L.levels) {data : SelectedPayloadHistory.Data (w := w) B f hf}
    (past : SelectedPayloadHistory.Past B f hf L data (vs) calendar) :
    SelectedPayloadHistory.Past B f hf L data (vs) vertex := by
  have idx := TerminalBootstrap.selected_last_index B f hf T hT X z
  have upper : tableBase L last tab + tableWords L ≤ endAddress L :=
    (tableEnd_le_nextLevel L last tab).trans (levelStart_mono L hl)
  apply past.transfer
  intro x _ hx
  rw [← idx] at hx
  have before : x < tableBase L last tab := hx.trans_le (Nat.le_add_right ..)
  exact entry.raw x (by omega) (.inl before)

variable (positions baseBits laneBits initialWidth inputN : ℕ) (pub : Fin 11 → Word w)
set_option quotPrecheck false in
local notation "L" => BlockProgram.layout B (pub 2).val positions T
set_option quotPrecheck false in
local notation "tab" => (⟨0,by change 0 < 6; decide⟩ : Fin (L).shape.tables)
local notation "saved" => CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L))
  (CursorRAM.encode w 1) baseBits laneBits (S.degreeExponent 0) initialWidth (incidenceStart L 0)
set_option quotPrecheck false in
local notation "resident" => CurrentResident.resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩
  L (endAddress L) inputN saved

set_option maxHeartbeats 800000 in
/-- From the completed selected calendar, construct the three deterministic
blocks and the equivalence between wire assignments and all legal fourth
blocks. Each block leads to the selected vertex readback. -/
theorem packed_prefix (segments : VertexImage.Part → VertexImage.Segment) (r cap : ℕ)
    (m phy : Memory w)
    (boundary : ScheduledTrace.Boundary resident pub (levelWords L : Word w) (directoryRows L)
      (directoryRows L) (vs) (Y) m)
    (handoff : SourceTransport.Agree ((pub 2).val+6 ≤ ·) m phy)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ (L).base+2^r*2^r)
    (room : (L).base+2^r*2^r ≤ 2^w)
    (below : endAddress L + 2*rowsSize + (Y).totalWidth ≤ TerminalBootstrap.address (L).base r)
    (ordinal : 2*(tags).length*(X.positions+1) < 2^w)
    (slots : arcCount (Y) ≤ slotCapacity L) (cells : arcCount (Y) ≤ tableWords L)
    (totalFit : (Y).totalWidth < 2^w)
    (clock₀ : TerminalBootstrap.cost (L).shape B.recordLimit+1+30 ≤ cap) (clock₁ : 60 ≤ cap)
    (clock₂ : TraversalController.callFuel B.recordLimit+30 ≤ cap) :
    let bank := workers (L).shape B.recordLimit segments
    ∃ q : QuietPrefix bank pub cap phy, ∃ bitPaths : (Fin (Y).totalWidth → Bool) ≃ q.BitPaths,
      q.boot.val.choices = [[]] ∧
      q.prefixRows.val.choices = List.replicate (arcCount (Y)+1) [] ∧
      q.traversalRows.val.choices =
        List.replicate (2*((ls).map Layer.count).sum+2*(tags).length+1) [] ∧
      FinalBits.Worker.Layout pub q.traversalRows.val.memory (endAddress L+rowsSize) (Y).totalWidth ∧
      ∀ bits, (bitPaths bits).val.choices = FinalBits.calls bits ++ [[]] ∧
        VertexEntry B f hf T hT X z L tab baseBits laneBits pub phy (bitPaths bits).val.memory bits := by
  intro bank
  let H := TerminalBootstrap.address (L).base r
  let rowBase := endAddress L
  let Aₜ := TerminalBootstrap.fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) tab
  let boot := TerminalBootstrap.report (L).shape B.recordLimit pub 0 phy
  have above : rowBase ≤ H := by dsimp only [rowBase,H]; omega
  obtain ⟨⟨history⟩,ready,rs,start,_⟩ := run_boundary B f hf T hT X z positions baseBits laneBits
    initialWidth inputN pub segments r cap m phy boundary handoff exp hr reserve room above slots
    cells totalFit clock₀ clock₁
  let src := prefixMemory pub phy boot rs
  have wide : 28 ≤ (L).shape.scalarFields := by change 28 ≤ 54; decide
  have hl : last < (L).levels := by
    rw [TerminalBootstrap.selected_prior_length,BlockProgram.actual_level_count, Nat.mul_comm T]; omega
  have fields := TraversalResidentHandoff.fields_of_start L last hl tab Aₜ B.recordLimit r (Y)
    pub phy src ready exp hr reserve room above wide cells rs start start.handoff_rows.1
  have residentData := TraversalResidentHandoff.selected_resident B f hf T hT X z
    L baseBits laneBits tab history fields hl wide
  let ds := residentData.choose
  have residentFields := residentData.choose_spec.2.1
  have heads := residentData.choose_spec.2.2
  obtain ⟨q,hboot,hpref,hrows,_,valid,rows,roles,low,high⟩ :=
    selectedQuietPrefix B f hf T hT X z bank pub cap _ rowBase H (levelStart L 0) (levelWords L)
      _ _ phy boot rs rfl clock₀ clock₁ clock₂ start ds residentFields heads below ordinal
  let mid := q.traversalRows.val.memory
  have hv : (header pub).val = H := header_val L pub r ready.workspace exp hr reserve room
  have fits := fields.fits
  have pos (j : ℕ) (hj : j < 32) : (header pub+(j : Word w)).val = H+j := by
    rw [Fin.val_add,hv,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]
  have headFit : (header pub).val+32 ≤ 2^w := hv ▸ fits
  have liveRows := TerminalBootstrap.selected_rowWords B f hf T hT X z L baseBits laneBits tab
  have middle (j : ℕ) (hj : 0 < j) (hj' : j < 31) : mid (H+j) = src (H+j) := high j hj hj'
  have baseValue : FinalBits.Worker.base pub mid = ((rowBase+rowsSize : ℕ) : Word w) := by
    change mid (header pub+13).val = _
    rw [show (header pub+13).val = H+13 from pos 13 (by decide),middle 13 (by decide) (by decide)]
    have x := fields.headerFields 13 (by decide) (by decide) (by decide)
    change src (H+13) = ((rowBase+Aₜ.rowWords B.recordLimit : ℕ) : Word w) at x
    exact x.trans (congrArg (fun d : ℕ => ((rowBase+d : ℕ) : Word w)) liveRows)
  have totalValue : FinalBits.Worker.total pub mid = ((Y).totalWidth : Word w) := by
    change mid (header pub+12).val = _
    rw [show (header pub+12).val = H+12 from pos 12 (by decide),middle 12 (by decide) (by decide)]
    exact Fin.ext (fields.total.trans (Nat.mod_eq_of_lt totalFit).symm)
  have bitEnd : rowBase+rowsSize+(Y).totalWidth ≤ (header pub).val := by
    rw [hv]; change endAddress L+rowsSize+(Y).totalWidth ≤ TerminalBootstrap.address (L).base r; omega
  have layout := FinalBits.Worker.Layout.ofBelow baseValue totalValue bitEnd headFit
  have self : SourceTransport.Agree (workerCell (header pub)) mid mid := fun _ _ => rfl
  let bitPaths := SharedBitPhase.equiv (L).shape B.recordLimit segments pub cap mid mid layout
    (by omega) headFit bitEnd self
  refine ⟨q,bitPaths,hboot,hpref,hrows,layout,fun bits => ⟨rfl,?_⟩⟩
  let vertex := (bitPaths bits).val.memory
  have layers := selected_layers B f hf T hT X z
  have rows' : AllRows w mid B.recordLimit rowBase rowBase ((tags).map TaggedLayer.layer) := layers ▸ rows
  obtain ⟨run,vr,vt,wire,lv,hvtx⟩ := TerminalLayout.linked_vertexMemory bank rfl pub mid mid cap
    B.recordLimit rowBase (Y).totalWidth (tags) bits (layers ▸ selected_capacity B f hf T hT X z)
    (layers ▸ layout) headFit (by rw [hv,layers]; exact below) (by omega) valid self rows' (layers ▸ roles)
  have tableEnd : tableBase L last tab + tableWords L ≤ endAddress L :=
    (tableEnd_le_nextLevel L last tab).trans (levelStart_mono L hl)
  have tableFit : tableBase L last tab < 2^w := by
    change endAddress L ≤ H at above
    omega
  have pointer : (tableBase L last tab : Word w).val = tableBase L last tab := Nat.mod_eq_of_lt tableFit
  have beforeHeader : (tableBase L last tab : Word w).val + arcCount (Y) ≤ (header pub).val := by
    rw [pointer,hv]; change endAddress L ≤ H at above; omega
  have offsetCells := (start.physical_readback headFit beforeHeader).2.2
  have frame (x : ℕ) (hx : x < rowBase) : vertex x = src x := (lv x hx).trans (low x hx)
  have head (j : ℕ) (hj : 0 < j) (hj' : j < 31) : vertex (H+j) = src (H+j) := by
    exact (pos j (by omega) ▸ hvtx j hj hj').trans (high j hj hj')
  have sameHeads (j : ℕ) (hj : j ∈ terminalScalars) : vertex (H+j) = src (H+j) := by
    simp only [terminalScalars,Finset.mem_insert,Finset.mem_singleton] at hj
    exact head j (by omega) (by omega)
  have lower (i : Fin (vs).length) : levelsBase L ≤ ((ds i).pub 1).val := by
    change levelsBase L ≤ ((residentData.choose i).pub 1).val
    rw [residentData.choose_spec.1 i]
    exact history.lower i
  have vertexDirs := move_directories B f hf T hT X z ds residentFields lower heads frame sameHeads
  refine ⟨?_,run.valid _ rfl,layers ▸ vr,layers ▸ vt,layers ▸ wire,
    ?_,?_,?_,?_,?_⟩
  · rw [hv]
    exact vertexDirs
  · intro i
    have hi := i.isLt
    have bound : tableBase L last tab+i.val < rowBase := by change _ < endAddress L; omega
    exact (congrArg Fin.val (frame _ bound)).trans (pointer ▸ offsetCells i)
  · intro x hx hs
    exact (frame x hx).trans (fields.tableFrame x (hx.trans_le above) hs)
  · intro j hj hn hm
    rw [hv]
    exact (head j.val hj (by have := j.isLt; omega)).trans (fields.headerFields j hj hn hm)
  · rw [hv]
    exact (congrArg Fin.val (head 12 (by decide) (by decide))).trans fields.total
  · rw [hv]
    exact (head 14 (by decide) (by decide)).trans (fields.offset.trans
      (congrArg (fun d : ℕ => ((d+(Y).totalWidth : ℕ) : Word w)) liveRows))

/-- The same selected parser snapshots that were recorded by the detailed
calendar are available in every physical vertex-entry memory. -/
theorem packed_detailed_prefix (data : SelectedPayloadHistory.Data (w := w) B f hf)
    (segments : VertexImage.Part → VertexImage.Segment) (r cap : ℕ) (m phy : Memory w)
    (boundary : ScheduledTrace.Boundary
      (DetailedResident.resident B f hf ⟨leafLayer (siteOrder X), .cursor⟩ L (endAddress L) inputN saved data)
      pub (levelWords L : Word w) (directoryRows L) (directoryRows L) (vs) (Y) m)
    (handoff : SourceTransport.Agree ((pub 2).val+6 ≤ ·) m phy)
    (exp : (pub 7).val = r) (hr : r < w) (reserve : 32 ≤ (L).base+2^r*2^r)
    (room : (L).base+2^r*2^r ≤ 2^w)
    (below : endAddress L + 2*rowsSize + (Y).totalWidth ≤ TerminalBootstrap.address (L).base r)
    (ordinal : 2*(tags).length*(X.positions+1) < 2^w)
    (slots : arcCount (Y) ≤ slotCapacity L) (cells : arcCount (Y) ≤ tableWords L)
    (totalFit : (Y).totalWidth < 2^w)
    (clock₀ : TerminalBootstrap.cost (L).shape B.recordLimit+1+30 ≤ cap) (clock₁ : 60 ≤ cap)
    (clock₂ : TraversalController.callFuel B.recordLimit+30 ≤ cap) :
    let bank := workers (L).shape B.recordLimit segments
    ∃ q : QuietPrefix bank pub cap phy, ∃ bitPaths : (Fin (Y).totalWidth → Bool) ≃ q.BitPaths,
      q.boot.val.choices = [[]] ∧
      q.prefixRows.val.choices = List.replicate (arcCount (Y)+1) [] ∧
      q.traversalRows.val.choices =
        List.replicate (2*((ls).map Layer.count).sum+2*(tags).length+1) [] ∧
      FinalBits.Worker.Layout pub q.traversalRows.val.memory (endAddress L+rowsSize) (Y).totalWidth ∧
      ∀ bits, (bitPaths bits).val.choices = FinalBits.calls bits ++ [[]] ∧
        VertexEntry B f hf T hT X z L tab baseBits laneBits pub phy (bitPaths bits).val.memory bits ∧
        SelectedPayloadHistory.Past B f hf L data (vs) (bitPaths bits).val.memory := by
  obtain ⟨q,paths,h₀,h₁,h₂,layout,each⟩ := packed_prefix B f hf T hT X z positions baseBits
    laneBits initialWidth inputN pub segments r cap m phy (DetailedResident.currentBoundary boundary)
    handoff exp hr reserve room below ordinal slots cells totalFit clock₀ clock₁ clock₂
  have hl : last < (L).levels := by
    rw [TerminalBootstrap.selected_prior_length,BlockProgram.actual_level_count,Nat.mul_comm T]; omega
  have past : SelectedPayloadHistory.Past B f hf L data (vs) phy := by
    apply (DetailedResident.payloads boundary.stored).transfer
    intro x lower _
    have low : (pub 2).val+6 ≤ levelsBase L := by
      unfold levelsBase directoryBase plannerTag frameBase
      change (pub 2).val+6 ≤ (pub 2).val+9+_+1+_
      omega
    exact (handoff x (low.trans lower)).symm
  exact ⟨q,paths,h₀,h₁,h₂,layout,fun bits =>
    ⟨(each bits).1,(each bits).2,(each bits).2.payload B f hf T hT X z hl past⟩⟩

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
