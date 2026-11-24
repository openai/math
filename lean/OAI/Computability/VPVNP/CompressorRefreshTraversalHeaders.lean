import OAI.Computability.VPVNP.CompressorRefreshArgumentPlan
import OAI.Computability.VPVNP.CompressorBlockMetadata
import OAI.Computability.VPVNP.PairTraversalArena

/-!
# Refresh operands at a completed DFS node

The persistent state names the input level header. Public operands zero, one and two
name the owner site, popped parent node, and current level header. The sole child is
read through the parent row pointer. The parent node uses the canonical inverse-slot
and width columns named by the current header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalHeaders

open BurstRAM PhaseRecipe Compression Compression.Refresh Compression.DegreeRefresh NewSlots
open OperandInputs RefreshMapOperands PairSimulation PairSimulation.NodeArguments DescriptorSpace
open scoped Fin.CommRing

/-- Read the six level-plan operands from the old header. The first table pointer
starts the packed refresh scratch region. -/
def level : LevelRecipe.Input :=
  ⟨.header 60, .header 0, .header 3, .header 54, .header 56, .header 59⟩

/-- Refresh traversal expressions for the saved arena start and stride, the sole child's
address read through the parent pointer, the parent and owner operands, and the old
incoming-slot head. -/
def traversal : OperandInputs.Traversal :=
  ⟨.header 17, .header 18, .load (.load (.publicWord 1)), .publicWord 1, .publicWord 0, .header 58⟩

/-- Load the field at the given offset in the successor level header whose base is public
operand two. -/
def current (offset : ℕ) : Expr := .load ((Expr.publicWord 2).add (.lit offset))

/-- Retain the old level's segment and term addresses, while sourcing the new incidence
columns from the successor's canonical header. -/
def input (s : LevelRecipe.Shape) : OperandInputs.Input :=
  let I := fromLevel s level traversal
  { I with parent := { I.parent with actualIn := current 58, width := current 59 } }

variable {w : ℕ}

/-- Typed values in the persisted level headers used by the actual refresh expression
bank. The two canonical incidence arrays may occupy separate physical regions. -/
structure Geometry (V g oldHead newHead start : ℕ) (A : Arena) (T U : IncidenceDirectory w)
    (m : Memory w) : Prop where
  oldRoom : oldHead + 60 < 2 ^ w
  newRoom : newHead + 59 < 2 ^ w
  vertices : m (oldHead + 0) = word V
  residual : m (oldHead + 3) = word (2 ^ g)
  arena : m (oldHead + 17) = word A.start
  stride : m (oldHead + 18) = word A.stride
  oldIncidence : ∀ c : Fin 6, m (oldHead + 54 + c.val) = T.column c
  newIncidence : ∀ c : Fin 6, m (newHead + 54 + c.val) = U.column c
  scratch : m (oldHead + 60) = word start

/-- Transfer retained header facts through later planner and traversal writes. -/
theorem Geometry.keep {V g oldHead newHead start : ℕ} {A : Arena} {T U : IncidenceDirectory w}
    {m m' : Memory w}
    (data : Geometry V g oldHead newHead start A T U m)
    (old : ∀ n ≤ 60, m' (oldHead + n) = m (oldHead + n))
    (new : ∀ n ≤ 59, m' (newHead + n) = m (newHead + n)) :
    Geometry V g oldHead newHead start A T U m' := by
  refine ⟨data.oldRoom, data.newRoom, (old 0 (by decide)).trans data.vertices,
    (old 3 (by decide)).trans data.residual, (old 17 (by decide)).trans data.arena,
    (old 18 (by decide)).trans data.stride, ?_, ?_, (old 60 le_rfl).trans data.scratch⟩
  · intro c
    rw [Nat.add_assoc, old _ (by have := c.isLt; omega), ← Nat.add_assoc]
    exact data.oldIncidence c
  · intro c
    rw [Nat.add_assoc, new _ (by have := c.isLt; omega), ← Nat.add_assoc]
    exact data.newIncidence c

private theorem addr_val {x : W w} {base offset : ℕ} (h : x.val = base)
    (room : base + offset < 2 ^ w) :
    (x + word offset).val = base + offset := by
  rw [Fin.val_add, h, Fin.val_ofNat, Nat.mod_eq_of_lt (show offset < 2 ^ w by omega),
    Nat.mod_eq_of_lt room]

/-- The two external loads at the popped parent read its first and unique child. -/
theorem child_read {pub : Fin 5 → W w} {state : W w} {m : Memory w} {parent child listHead : ℕ}
    (hp : (pub 1).val = parent) (row : DFS.Row m parent listHead [word child]) :
    traversal.child.eval pub state m = word child := by
  obtain ⟨_, room, head, _, kids⟩ := row
  have hl : (m parent).val = listHead := by
    rw [head]
    exact Nat.mod_eq_of_lt (by
      simpa using (Nat.lt_of_le_of_lt (Nat.le_add_right listHead _) room))
  change m (m (pub 1).val).val = _
  rw [hp, hl]
  exact kids ⟨0, by simp⟩

variable (s : LevelRecipe.Shape) {g : ℕ} (X : State s.a (s.a + g))
  (p : (X.Base × BitWord g) × Fin (2 ^ s.a)) (P : SlotGraph (Fin (2 ^ s.a)) s.dH)
  (hD : 1 < 2 ^ s.a) (hd : s.dH + 1 ≤ 2 ^ s.a₀)
  (internal : X.Base × BitWord g → Fin (2 ^ s.a) × Fin s.dH → ℕ)
  (A : Arena) (T U : IncidenceDirectory w) (C : LevelRecipe.Context w)

local notation "O" => sites (D := 2 ^ s.a) X.baseIndex (bitWordFinEquiv g)

/-- The fixed header expressions evaluate to all typed operands of the chosen map.
The old and current headers, saved site, and popped parent are the four live DFS words. -/
theorem describes {oldHead newHead start parent child listHead : ℕ}
    (geometry : Geometry (Fintype.card X.Base) g oldHead newHead start A T U C.memory)
    (state : C.state.val = oldHead) (newHeadWord : (C.pub 2).val = newHead)
    (site : (C.pub 0).val = (O p).val) (parentWord : (C.pub 1).val = parent)
    (row : DFS.Row C.memory parent listHead [word child]) (lanesFit : 2 ^ g < 2 ^ w) :
    Describes (input s) C.pub C.state C.memory X p P hD hd internal A child parent T U
      ((Allocation.plan X s.a₀ s.dH s.ties s.stride start).scratch w)
      (word (Allocation.plan X s.a₀ s.dH s.ties s.stride start).demand)
      (word (Allocation.plan X s.a₀ s.dH s.ties s.stride start).term) := by
  have oldRead (i : ℕ) (hi : i ≤ 60) : C.eval (.header i) = C.memory (oldHead + i) :=
    congrArg C.memory (addr_val state ((Nat.add_le_add_left hi _).trans_lt geometry.oldRoom))
  have newRead (i : ℕ) (hi : i ≤ 59) : C.eval (current i) = C.memory (newHead + i) :=
    congrArg C.memory (addr_val newHeadWord ((Nat.add_le_add_left hi _).trans_lt geometry.newRoom))
  have levelData : LevelRecipe.Describes (s := s) level C X start T :=
    ⟨(oldRead 60 le_rfl).trans geometry.scratch, (oldRead 0 (by decide)).trans geometry.vertices,
     (oldRead 3 (by decide)).trans geometry.residual,
     (oldRead 54 (by decide)).trans (geometry.oldIncidence 0),
     (oldRead 56 (by decide)).trans (geometry.oldIncidence 2),
     (oldRead 59 (by decide)).trans (geometry.oldIncidence 5)⟩
  have prev := describes_fromLevel s level traversal C X p P hD hd internal A child parent start T
    levelData
    ((oldRead 17 (by decide)).trans geometry.arena) ((oldRead 18 (by decide)).trans geometry.stride)
    (child_read (state := C.state) parentWord row)
    (Fin.ext (parentWord.trans (Nat.mod_eq_of_lt (parentWord ▸ (C.pub 1).isLt)).symm)) site
    ((oldRead 58 (by decide)).trans (geometry.oldIncidence 4)) lanesFit
  refine ⟨prev.childRep, ?_, prev.site, prev.lanes, prev.offOut, prev.offIn,
    prev.widthOut, prev.widthIn,
    prev.demandBase, prev.termBase⟩
  exact ⟨prev.parentRep.arena, prev.parentRep.stride, prev.parentRep.node, prev.parentRep.site,
    (newRead 58 (by decide)).trans (geometry.newIncidence 4),
    (newRead 59 le_rfl).trans (geometry.newIncidence 5)⟩

/-- Both pointer banks as emitted by the native incidence/table-head publisher. -/
structure HeadBank (L : Layout) (i rows : ℕ) (m : Memory w) : Prop where
  incidence : ∀ c : Fin 6, m (incidenceHead L i c) = word (incidenceBase L i rows c)
  tables : ∀ c : Fin L.shape.tables, m (tableHead L i c) = word (tableBase L i c)

theorem HeadBank.ofNative {L : Layout} {i : Fin L.levels} {rows : ℕ} {m : Memory w}
    (run : BlockHeaderRun.HeadsRun L i rows m) :
    HeadBank L i rows (after m (eventLog [BlockHeaderRun.headReport L i m])) := by
  simpa only [eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    (show HeadBank L i rows (after m (BlockHeaderRun.headReport L i m).events) from
      ⟨run.incidence, run.tables⟩)

theorem HeadBank.keep {L : Layout} {i rows : ℕ} {m m' : Memory w} (data : HeadBank L i rows m)
    (same : ∀ n < levelHeaderWords L, m' (levelStart L i + n) = m (levelStart L i + n)) :
    HeadBank L i rows m' := by
  constructor
  · intro c
    rw [incidenceHead, Nat.add_assoc, same _ (by unfold levelHeaderWords; have := c.isLt; omega),
      ← Nat.add_assoc]
    exact data.incidence c
  · intro c
    change m' (levelStart L i + L.shape.scalarFields + 6 + c.val) = _
    rw [Nat.add_assoc, Nat.add_assoc, same _ (by unfold levelHeaderWords; have := c.isLt; omega)]
    simpa only [tableHead, Nat.add_assoc] using data.tables c

private theorem header_before {L : Layout} {i j : ℕ} (order : i < j) :
    levelStart L i + levelHeaderWords L ≤ levelStart L j := by
  refine le_trans ?_ (levelStart_mono L order)
  unfold levelStart; rw [Nat.succ_mul]; unfold levelWords; omega

private theorem HeadBank.keep_pointers {L : Layout} {i rows : ℕ} {m m' : Memory w}
    (data : HeadBank L i rows m)
    (same : ∀ n, L.shape.scalarFields ≤ n → n < levelHeaderWords L →
      m' (levelStart L i + n) = m (levelStart L i + n)) : HeadBank L i rows m' := by
  constructor
  · intro c
    rw [incidenceHead, Nat.add_assoc, same _ (by omega)
      (by unfold levelHeaderWords; have := c.isLt; omega)]
    simpa only [incidenceHead, Nat.add_assoc] using data.incidence c
  · intro c
    change m' (levelStart L i + L.shape.scalarFields + 6 + c.val) = _
    rw [Nat.add_assoc, Nat.add_assoc, same _ (by omega)
      (by unfold levelHeaderWords; have := c.isLt; omega)]
    simpa only [tableHead, Nat.add_assoc] using data.tables c

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f} {v : SelectedLevel B f hf}

/-- The scalar relabel and successor publisher retain the old pointers and produce
the new incidence/table heads in the same memory. -/
theorem headBanks_of_substep {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {rows : ℕ} {m : Memory w} (run : BlockHeaderRun.Substep v L i j six m)
    (order : i.val < j.val) (old : HeadBank L i rows m) :
    HeadBank L i rows (BlockHeaderRun.finalMemory v L i j m) ∧
      HeadBank L j v.outputSlots (BlockHeaderRun.finalMemory v L i j m) := by
  refine ⟨old.keep_pointers ?_, ⟨run.heads.incidence, run.heads.tables⟩⟩
  have span := header_before (L := L) order
  intro n lower upper
  apply run.outside
  all_goals omega

/-- Read the private frame origin and stride from the twelve published metadata words.
These are positions two and three of the packet starting at header offset fifteen. -/
theorem arena_of_packet {m : Memory w} {head limit degree slots n ain width sites : ℕ}
    (placement : BlockMetadata.Placement)
    (packet : ∀ j : Fin 12, m (head + 15 + j.val) =
      word (BlockMetadata.payload limit slots degree n ain width sites placement j)) :
    m (head + 17) = word n ∧ m (head + 18) = word (frameStride slots n) := by
  constructor
  · have h := packet 2
    change m (head + 15 + 2) = word n at h
    rw [Nat.add_assoc] at h; exact h
  · have h := packet 3
    change m (head + 15 + 3) = word (frameStride slots n) at h
    rw [Nat.add_assoc] at h; exact h

/-- The actual scalar publisher, old and current incidence head banks, table zero,
and the published metadata packet provide the traversal geometry. -/
theorem Geometry.ofPublished {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f} {v : SelectedLevel B f hf}
    {dH : ℕ}
    {L : Layout} {i j : Fin L.levels} {oldRows newRows : ℕ} {m : Memory w}
    (oldScalars : LevelFields.Published L i v dH m) (old : HeadBank L i oldRows m)
    (new : HeadBank L j newRows m)
    (scalarCount : L.shape.scalarFields = 54) (hasTables : 0 < L.shape.tables)
    (room : endAddress L < 2 ^ w)
    (A : Arena) (arena : m (levelStart L i + 17) = word A.start)
    (stride : m (levelStart L i + 18) = word A.stride) :
    Geometry (Fintype.card v.input.Base) v.outputLanes (levelStart L i) (levelStart L j)
      (arrayBase L i)
      A (packedIncidence L w i oldRows) (packedIncidence L w j newRows) m := by
  have span (l : Fin L.levels) : levelStart L l + 61 ≤ levelStart L (l.val + 1) := by
    have hw : 61 ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
    unfold levelStart; rw [Nat.succ_mul]; omega
  have bank (l : Fin L.levels) (rows : ℕ) (h : HeadBank L l rows m) (c : Fin 6) :
      m (levelStart L l + 54 + c.val) = (packedIncidence L w l rows).column c := by
    rw [packed_column]
    simpa only [incidenceHead, scalarCount] using h.incidence c
  refine ⟨(Nat.add_le_add_left (by decide : 60 ≤ 61) _).trans_lt
      ((span i).trans_lt (level_room L room i)),
    (Nat.add_le_add_left (by decide : 59 ≤ 61) _).trans_lt
      ((span j).trans_lt (level_room L room j)),
    oldScalars.vertices, oldScalars.residual, arena, stride, bank i oldRows old,
    bank j newRows new, ?_⟩
  let c : Fin L.shape.tables := ⟨0, hasTables⟩
  simpa [tableHead, tableBase, c, scalarCount, Nat.add_assoc] using old.tables c

/-- Run the native metadata visits over the emitted scalar and pointer banks.
Only the input-length cell of the initial header is needed to calculate the
private argument frame. The result supplies its actual readback at the old header. -/
theorem run_metadata {L : Layout} {first step : ℕ} {pub : Fin 5 → W w} {state : W w} (m : Memory w)
    (entry : LevelFields.Entry L first pub state m) (limit slots : ℕ)
    (placement : BlockMetadata.Fields)
    {oldSites n oldRows newRows dH : ℕ}
    (sitesEq : (LevelFields.sites step).eval pub state m = word oldSites)
    (firstHeader : BlockHeaderPlan.firstHeader.eval pub state m = word (levelStart L 0))
    (nCell : m (levelStart L 0 + 29) = word n)
    (oldScalars : LevelFields.Published L (first + step) v dH m)
    (old : HeadBank L (first + step) oldRows m) (new : HeadBank L (first + (step + 1)) newRows m)
    (scalarCount : L.shape.scalarFields = 54) (hasTables : 0 < L.shape.tables)
    (nextLevel : first + (step + 1) < L.levels) (room : endAddress L < 2 ^ w)
    (pitchBefore : (pub 1 - 1).val < levelStart L (first + step)) :
    ∃ rs, SourceWalk (BlockMetadata.Source pub state)
      (BlockMetadata.visits L.shape step limit slots .refresh placement) m rs ∧
      Geometry (Fintype.card v.input.Base) v.outputLanes (levelStart L (first + step))
        (levelStart L (first + (step + 1))) (arrayBase L (first + step)) ⟨n, frameStride slots n⟩
        (packedIncidence L w (first + step) oldRows)
        (packedIncidence L w (first + (step + 1)) newRows)
        (after m (eventLog rs)) := by
  obtain ⟨rs, walk, packet, _, _, keep, _⟩ := BlockMetadata.publish_metadata m entry limit slots
    .refresh placement oldSites sitesEq (by omega) nextLevel room pitchBefore
  let i : Fin L.levels := ⟨first + step, by omega⟩
  let j : Fin L.levels := ⟨first + (step + 1), nextLevel⟩
  have span := header_before (L := L) (show first + step < first + (step + 1) by omega)
  have headerLen : 60 ≤ levelHeaderWords L := by unfold levelHeaderWords; omega
  let out := after m (eventLog rs)
  have low (a : ℕ) (ha : a < 15) : out (levelStart L i + a) = m (levelStart L i + a) := by
    change out (levelStart L (first + step) + a) = _
    apply keep <;> omega
  have prev : LevelFields.Published L i v dH out :=
    ⟨oldScalars.room, (low 0 (by decide)).trans oldScalars.vertices,
     (low 1 (by decide)).trans oldScalars.degree,
     (low 2 (by decide)).trans oldScalars.lanes, (low 3 (by decide)).trans oldScalars.residual,
     (low 4 (by decide)).trans oldScalars.nextDegree, (low 5 (by decide)).trans oldScalars.expander⟩
  have oldBank : HeadBank L i oldRows out := old.keep_pointers (by
    intro a lower upper; apply keep <;> omega)
  have newBank : HeadBank L j newRows out := new.keep_pointers (by
    intro a lower upper; apply keep <;> omega)
  have firstSpan := header_before (L := L) (show 0 < L.levels by omega)
  change levelStart L 0 + levelHeaderWords L ≤ endAddress L at firstSpan
  have len : BlockMetadata.lengthWord.eval pub state m = word n := by
    change m (BlockHeaderPlan.firstHeader.eval pub state m + word 29).val = _
    rw [firstHeader, addr_val (base := levelStart L 0) (Nat.mod_eq_of_lt (by omega)) (by omega),
      nCell]
  refine ⟨rs, walk, Geometry.ofPublished prev oldBank newBank scalarCount hasTables room _ ?_ ?_⟩
  · have h := packet 2
    change out (levelStart L i + 15 + 2) = BlockMetadata.lengthWord.eval pub state m at h
    rw [Nat.add_assoc, len] at h
    exact h
  · have h := packet 3
    change out (levelStart L i + 15 + 3) =
      (word (2 * slots)) * BlockMetadata.lengthWord.eval pub state m + 1 at h
    rw [Nat.add_assoc, len] at h
    change out (levelStart L i + 18) = ((2 * slots * n + 1 : ℕ) : W w)
    change out (levelStart L i + 18) = ((2 * slots : ℕ) : W w) * (n : W w) + 1 at h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

end CompressorRecords.PortRefresh.TraversalHeaders

end VPVNP
end Computability
end OAI
