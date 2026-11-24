import OAI.Computability.VPVNP.CompressorCursorFrameTransfers
import OAI.Computability.VPVNP.CompressorCalendarArenaTransfers

/-!
# All eight startup reports of the compressed pair

Every report uses the memory left by the previous report and its linker tag
write. The state passed to the online stage carries its controller bank, the
persistent cursor operands and the natural history-arena bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.TransferredStartup

open BurstRAM CursorBounds DescriptorSpace OnlineCursorStartup
open scoped Fin.CommRing

variable {w : ℕ}

/-- The two successive groups of startup reports that prepare the cursor frame and initialize
the calendar. -/
structure Trace (w : ℕ) where
  /-- First four reports, which prepare and copy the cursor operands into the active frame. -/
  frame : CursorFrameTransfers.Trace w
  /-- Last four reports, which compute the stride, install the arena and bank, and arm the
  calendar. -/
  calendar : CalendarArenaTransfers.Trace w

/-- All eight native startup reports indexed in execution order. -/
def Trace.source (t : Trace w) : Fin 8 → Report w :=
  ![t.frame.row, t.frame.raw, t.frame.loaded, t.frame.copied,
    t.calendar.stride, t.calendar.arena, t.calendar.bank, t.calendar.arm]

/-- The nine boundary memories before, between, and after the eight startup calls, including
linker tag writes. -/
def Trace.entry (t : Trace w) (tag : Word w) (m : Memory w) : Fin 9 → Memory w :=
  let prepared := t.frame.post tag m
  ![m,t.frame.postRow tag m,t.frame.postRaw tag m,t.frame.postLoad tag m,prepared,
    t.calendar.postStride tag prepared,t.calendar.postArena tag prepared,
    t.calendar.postBank tag prepared,t.calendar.post tag prepared]

theorem Trace.transfer (t : Trace w) (tag : Word w) (m : Memory w) (i : Fin 8) :
    t.entry tag m i.succ = writeMemory (after (t.entry tag m i.castSucc) (t.source i).events)
      tag ((i.val+1 : ℕ) : Word w) := by fin_cases i <;> rfl

/-- Construct the startup reports, beginning the calendar initialization in the memory produced
by the frame transfers. -/
noncomputable def trace (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) : Trace w :=
  let front := CursorFrameTransfers.trace D L B n a lanes pub tag m
  ⟨front, CalendarArenaTransfers.trace D d L steps pub tag (front.post tag m)⟩

theorem source_closed (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) (i : Fin 8) :
    ((trace D d L B n a lanes steps pub tag m).source i).result = none := by
  fin_cases i <;> rfl

/-- Both groups of native startup calls run, with calendar initialization using the
post-transfer cursor memory. -/
structure Runs (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) : Prop where
  frame : CursorFrameTransfers.Runs D L B n a lanes pub tag m
  calendar : CalendarArenaTransfers.Runs D d L B n a lanes steps pub tag
    ((CursorFrameTransfers.trace D L B n a lanes pub tag m).post tag m)

/-- The pair performs the eight source calls with the actual intervening
transfer writes. A lower tag address and a fitting descriptor allocation
suffice independently of the contents of the incoming memory. -/
theorem run (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) (input : Input D L B n pub)
    (hw : w = wordBits B n) (hB : 1 ≤ B) (lower : tag.val < L.base)
    (hL : roundedDown D.p D.q n*lanes ≤ virtualBits B n)
    (arity : 7 ≤ L.shape.arity) (scalars : 30 ≤ L.shape.scalarFields)
    (positions : initialPositions B n = L.positions) (levels : L.levels = 1+roundedDown D.p D.q n*(steps+1))
    (capacity : CursorRAM.ParametersInit.Capacity B n a (roundedDown D.p D.q n*lanes)
      (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6)) :
    Runs D d L B n a lanes steps pub tag m := by
  have front := CursorFrameTransfers.run D L B n a lanes pub tag m input hw hB hL arity
    ((by decide : 14 ≤ 30).trans scalars) capacity lower
  have cols : incidenceStart L 0 < 2^w := hw ▸ capacity.public_lt 6
  have headFit : levelStart L 0+29 < 2^w := by unfold incidenceStart levelHeaderWords at cols; omega
  exact ⟨front, CalendarArenaTransfers.run D d L B n a lanes steps pub tag _ input lower hL positions
    levels headFit front.count front.active front.saved⟩

/-- The exact native post-memory, including the tag transfer to stage eight.
The first header retains the natural arena base, level count and input length. -/
theorem Runs.output {D d L B n a lanes steps pub tag m}
    (h : Runs (w := w) D d L B n a lanes steps pub tag m) (hn : n < 2^w)
    (hl : 0 < L.levels) (hs : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    let t := trace D d L B n a lanes steps pub tag m
    let out := t.entry tag m (Fin.last 8)
    let head := levelStart L 0
    OnlineWorkspace.Ready d L.shape.arity (pub 2) (CalendarRows.rows D n) (levelWords L) out ∧
      Frame.data (DescriptorParameters.saved L w) out = DescriptorParameters.outputs L B n a (roundedDown D.p D.q n*lanes) w ∧
      (out (head+14)).val = endAddress L ∧ (out (head+28)).val = L.levels ∧ (out (head+29)).val = n ∧
      out tag.val = 8 := by
  intro t out head
  let middle := (CursorFrameTransfers.trace D L B n a lanes pub tag m).post tag m
  obtain ⟨base,count,len,_⟩ := HistoryArenaBase.stored L n middle hn hl hs fit
  have level (j : ℕ) : out (head+j) = HistoryArenaBase.install L n middle (head+j) :=
    h.calendar.levelWords_after _ (Nat.le_add_right ..)
  exact ⟨h.calendar.ready,h.calendar.saved,(congrArg Fin.val (level 14)).trans base,
    (congrArg Fin.val (level 28)).trans count,(congrArg Fin.val (level 29)).trans len,h.calendar.tagged⟩

/-- One length threshold covers the complete physical startup, for every
incoming memory and every linker tag preceding the polynomially bounded
workspace. Only the eight compiler constants and the live dimensions enter
the source instruction tables. -/
theorem eventually_run (D : CalendarRows.Spec) (d : ℕ) (F : Shape) (B a lanes steps : ℕ)
    (hB : 1 ≤ B) (hq : 0 < D.q) (hph : 0 < D.phaseRows)
    (hθ : (D.p : ℝ)/D.q ≤ 1) (hlanes : lanes ≤ B)
    (arity : 7 ≤ F.arity) (scalars : 30 ≤ F.scalarFields) {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (pub : Fin 11 → Word (wordBits B n)) (tag : Word (wordBits B n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits B n → tag.val < base n →
      ∀ m, Runs D d (LevelFields.tightDirectory (cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n)
        (CalendarRows.rows D n)) B n a lanes steps pub tag m := by
  filter_upwards [OnlineCursorStartup.eventually_input D B hB hq hph,
    DescriptorParameters.eventually_tight_capacity D F B a lanes hB hθ hlanes hb] with n input cap
  intro pub tag base_eq length_eq addr_eq lower m
  let P := cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n
  let L := LevelFields.tightDirectory P (CalendarRows.rows D n)
  have levels : L.levels = 1+roundedDown D.p D.q n*(steps+1) := by
    change 1+(steps+1)*Compression.blockCount ((D.p : ℝ)/D.q) n = _
    rw [roundedDown_eq, Nat.mul_comm]
  obtain ⟨hL,hcap⟩ := cap P.positions P.levels
  exact run D d L B n a lanes steps pub tag m (input P pub base_eq length_eq addr_eq) rfl hB lower
    hL arity scalars rfl levels hcap

end CompressorRecords.TransferredStartup

end VPVNP
end Computability
end OAI
