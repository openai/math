import OAI.Computability.VPVNP.PairTerminalPackedPrefix
import OAI.Computability.VPVNP.PairTerminalVertexFramePacked

/-!
# Placement and traversal operands on a physical vertex call

The counter updater can change the low workspace between two vertex calls.
The selected directories and the operand fields remain in the packed levels
or in the high header. Their two physical frames suffice for every site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs TerminalLink
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {n T : ℕ}
variable {hT : T*S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices}
local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

private theorem resident_data_frame {pub : Fin 11 → Word w} {H first pitch offset cap base : ℕ}
    {leaf : TaggedLayer} {fibers : List (Fiber w)} {vertex site : Memory w}
    (d : Resident pub vertex H first pitch offset cap base leaf fibers)
    (headerCells : ∀ j ∈ terminalScalars, site (H+j) = vertex (H+j))
    (levelCells : ∀ j ≤ fibers.length, ∀ o < 28, site (first+j*pitch+o) = vertex (first+j*pitch+o)) :
    Resident pub site H first pitch offset cap base leaf fibers := by
  refine ⟨d.header,d.headerFits,d.levelFits,(headerCells 16 (by decide)).trans d.firstHead,
    (headerCells 17 (by decide)).trans d.levelPitch,(congrArg Fin.val (headerCells 1 (by decide))).trans d.levels,
    (headerCells 14 (by decide)).trans d.roleOffset,(headerCells 15 (by decide)).trans d.rowStride,
    fun j h => (levelCells j h 14 (by decide)).trans (d.currentBase j h),
    fun j => (levelCells j.val (by simpa using j.isLt) 27 (by decide)).trans (d.role j),
    ?_,fun h => (congrArg Fin.val (headerCells 7 (by decide))).trans (d.terminalSites h),
    fun i => (congrArg Fin.val (levelCells i.val i.isLt.le 22 (by decide))).trans (d.produced i),
    fun i => (levelCells i.val i.isLt.le 24 (by decide)).trans (d.childCounts i),
    fun i => (levelCells i.val i.isLt.le 25 (by decide)).trans (d.childLists i),
    fun i => (levelCells i.val i.isLt.le 26 (by decide)).trans (d.childCapacity i)⟩
  intro h
  have same := levelCells 0 (Nat.zero_le _) 21 (by decide)
  simp only [Nat.zero_mul,Nat.add_zero] at same
  exact (congrArg Fin.val same).trans (d.initial h)

variable {L : Layout} {tab : Fin L.shape.tables} {baseBits laneBits : ℕ}
variable {pub : Fin 11 → Word w} {calendar vertex site : Memory w}

/-- The same indexed native directories, with the full traversal resident
header, on the physical input memory of an arbitrary later vertex call. -/
theorem VertexEntry.site_directories
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits)
    (live : (vs).length < L.levels) (wide : 28 ≤ L.shape.scalarFields)
    (dataFrame : ∀ x, levelsBase L ≤ x → x < endAddress L → site x = vertex x)
    (headerFrame : ∀ j ∈ terminalScalars, site ((header pub).val+j) = vertex ((header pub).val+j)) :
    ∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] site (endAddress L),
      Resident pub site (header pub).val (levelStart L 0) (levelWords L)
        (words B.recordLimit (ls)+(Y).totalWidth) B.recordLimit (endAddress L)
        ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds) := by
  obtain ⟨dirs,lower,d⟩ := entry.boundedDirectories
  let ds (i : Fin (vs).length) : LevelDirectory vs[i] site (endAddress L) :=
    (dirs i).transport fun x hx => (dataFrame x ((lower i).trans ((dirs i).cells_interval hx).1)
      ((dirs i).cells_interval hx).2).symm
  have banks : levelFibers (vs) ds = levelFibers (vs) dirs := rfl
  refine ⟨ds,?_⟩
  rw [banks]
  apply resident_data_frame d headerFrame
  intro j hj o ho
  have before := TraversalResidentHandoff.headers_before L live wide j
    (by simpa only [levelFibers,List.length_ofFn] using hj)
  apply dataFrame
  · simp only [levelStart,Nat.zero_mul,Nat.add_zero]
    omega
  · omega

/-- Natural and word addresses of every live level at a later site. -/
theorem VertexEntry.site_level_head
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits pub calendar vertex bits)
    (live : (vs).length < L.levels) (wide : 28 ≤ L.shape.scalarFields)
    (dataFrame : ∀ x, levelsBase L ≤ x → x < endAddress L → site x = vertex x)
    (headerFrame : ∀ j ∈ terminalScalars, site ((header pub).val+j) = vertex ((header pub).val+j))
    (j : ℕ) (hj : j ≤ (vs).length) :
    levelHead pub site j = (levelStart L j : Word w) ∧ (levelHead pub site j).val = levelStart L j := by
  obtain ⟨ds,d⟩ := entry.site_directories live wide dataFrame headerFrame
  have loc : levelHead pub site j = (levelStart L j : Word w) := by
    rw [levelHead,terminal_read d 16 (by decide),terminal_read d 17 (by decide),
      d.firstHead,d.levelPitch,← Nat.cast_mul,← Nat.cast_add]
    simp only [levelStart,Nat.zero_mul,Nat.add_zero]
  refine ⟨loc,?_⟩
  have fit := d.levelFits j (by simpa only [levelFibers,List.length_ofFn] using hj)
  rw [loc,Fin.val_natCast,Nat.mod_eq_of_lt]
  simp only [levelStart,Nat.zero_mul,Nat.add_zero] at fit ⊢
  omega

end PairSimulation.TerminalProgram

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM Compression CompressorRecords DescriptorSpace PairSimulation
open LocalHistory TraversalRows TraversalRoles TraversalControllerInputs TerminalProgram
open scoped Fin.CommRing

variable {G : Group} {L : Layout} {cap width ord : ℕ} {roles : List TaggedLayer}
variable {vertex site : Memory G.w}

private theorem levelFloor (L : Layout) : L.base ≤ levelsBase L := by
  unfold levelsBase directoryBase plannerTag frameBase
  omega

/-- The two operand frames at the actual site's physical entry. -/
theorem VertexPacked.traversal_frames (P : VertexPacked G L cap roles width)
    (frame : LinkedVertexMemory G vertex ord site) :
    (∀ x, levelsBase L ≤ x → x < endAddress L → site x = vertex x) ∧
    ∀ j ∈ terminalScalars, site ((vertexHeader G).val+j) = vertex ((vertexHeader G).val+j) := by
  refine ⟨fun _ lo hi => P.directory frame ((levelFloor L).trans lo) hi,?_⟩
  intro j hj
  simp only [terminalScalars,Finset.mem_insert,Finset.mem_singleton] at hj
  have h := P.header frame j (by omega) (by omega)
  have fit := P.room
  have addr : (vertexHeader G+(j : Word G.w)).val = (vertexHeader G).val+j := by
    change ((vertexHeader G).val+j % (2^G.w)) % (2^G.w) = (vertexHeader G).val+j
    rw [Nat.mod_eq_of_lt (by omega : j < 2^G.w),Nat.mod_eq_of_lt (by omega)]
  rwa [addr] at h

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {n T : ℕ}
variable {hT : T*S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices}
local notation "vs" => executeLevels B f hf T hT X z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
variable {tab : Fin L.shape.tables} {baseBits laneBits : ℕ} {calendar : Memory G.w}

/-- The directory and parser snapshot witnesses coexist in the memory used
by a real site, after any preceding motif counter flushes. -/
theorem VertexPacked.site_operands (P : VertexPacked G L cap roles width)
    (frame : LinkedVertexMemory G vertex ord site)
    {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z L tab baseBits laneBits (terminalOperands G) calendar vertex bits)
    (live : (vs).length < L.levels) (wide : 28 ≤ L.shape.scalarFields)
    {data : SelectedPayloadHistory.Data (w := G.w) B f hf}
    (past : SelectedPayloadHistory.Past B f hf L data (vs) vertex) :
    (∃ ds : (i : Fin (vs).length) → LevelDirectory vs[i] site (endAddress L),
      Resident (terminalOperands G) site (vertexHeader G).val (levelStart L 0) (levelWords L)
        (words B.recordLimit (ls)+(Y).totalWidth) B.recordLimit (endAddress L)
        ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (vs) ds)) ∧
      SelectedPayloadHistory.Past B f hf L data (vs) site := by
  obtain ⟨low,high⟩ := P.traversal_frames frame
  refine ⟨entry.site_directories live wide low high,past.transfer ?_⟩
  have upper : DescriptorSpace.tableBase L (vs).length tab + tableWords L ≤ endAddress L :=
    (tableEnd_le_nextLevel L (vs).length tab).trans (levelStart_mono L live)
  intro x lo hx
  have before : x < DescriptorSpace.tableBase L (vs).length tab := hx.trans_le (Nat.le_add_right ..)
  exact low x lo (by omega)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
