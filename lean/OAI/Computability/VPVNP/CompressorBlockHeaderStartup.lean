import OAI.Computability.VPVNP.CompressorTransferredStartup
import OAI.Computability.VPVNP.CompressorBlockHeaderRun

/-!
# First descriptor header after the pair startup

The eight closed startup calls, including their outer tag transfers, leave the
actual inputs of the two level-zero publishers in the first level. The
publisher addresses and the cursor incidence operands follow from that memory.
The arena bounds and input length survive both publishers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockHeaderStartup

open BurstRAM BlockHeaderRun CursorBounds DescriptorSpace
open scoped Fin.CommRing

variable {w : ℕ}

/-- Memory at the end of the eight transferred startup calls, where the first header publishers
read their operands. -/
noncomputable def post (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word w) (tag : Word w) (m : Memory w) :=
  (TransferredStartup.trace D d L B n a lanes steps pub tag m).entry tag m (Fin.last 8)

private theorem scalar_fits {B n a l dir tag start frame : ℕ}
    (capacity : CursorRAM.ParametersInit.Capacity B n a l dir tag start frame) :
    Scalars.Fits (.terminal a) ((virtualBits B n-l+l)*2^(virtualBits B n-l)) l (wordBits B n) := by
  let V := (virtualBits B n-l+l)*2^(virtualBits B n-l)
  have small : V < 2^wordBits B n := by
    have h₁ : V ≤ V*2^l := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have h₂ : V*2^l ≤ CursorRAM.rowCount (virtualBits B n-l) l a :=
      Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have bounds := capacity.arrays_end
    omega
  obtain ⟨degree,_,lanes⟩ := capacity.shiftResults_lt
  intro i
  fin_cases i <;> simp [Scalars.values,Scalars.Pass.spent,Scalars.Pass.expanderDegree,small,V] at * <;>
    assumption

/-- The level-zero publishers run on the startup post-memory. The planner's
first-header expression evaluates to the same address for every entry cursor. -/
structure Ready (L : Layout) (a low l width n : ℕ) (base : Word w) (m : Memory w) : Prop where
  nonempty : 0 < L.levels
  six : 6 ≤ L.shape.scalarFields
  initial : Initial a low l L nonempty six m
  first : ∀ state, BlockHeaderPlan.firstHeader.eval (Workspace.ports L.shape.arity base).data state m =
    header w L 0
  count : m (Workspace.ports L.shape.arity base).rows.val = (directoryRows L : Word w)
  pitch : m ((Workspace.ports L.shape.arity base).directory-1).val = (levelWords L : Word w)
  count_before : ((Workspace.ports L.shape.arity base).data 3).val < levelStart L 0
  frame : Frame.data (header w L 0+6) m =
    CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1) low l a width
      (incidenceStart L 0)
  arena : ((initialFinal a L m) (levelStart L 0+14)).val = endAddress L
  levels : ((initialFinal a L m) (levelStart L 0+28)).val = L.levels
  length : ((initialFinal a L m) (levelStart L 0+29)).val = n
  positions : ((low+l)*2^low)*2^l = L.positions

set_option maxHeartbeats 800000 in
theorem from_startup (D : CalendarRows.Spec) (d : ℕ) (L : Layout) (B n a lanes steps : ℕ)
    (pub : Fin 11 → Word (wordBits B n)) (tag : Word (wordBits B n)) (m : Memory (wordBits B n))
    (run : TransferredStartup.Runs D d L B n a lanes steps pub tag m)
    (input : OnlineCursorStartup.Input D L B n pub) (nonempty : 0 < L.levels)
    (fields : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^wordBits B n)
    (positions : initialPositions B n = L.positions)
    (capacity : CursorRAM.ParametersInit.Capacity B n a (roundedDown D.p D.q n*lanes)
      (directoryBase L) 1 (incidenceStart L 0) (levelStart L 0+6)) :
    let l := roundedDown D.p D.q n*lanes
    Ready L a (virtualBits B n-l) l (initialWidth B n) n (pub 2) (post D d L B n a lanes steps pub tag m) := by
  let w := wordBits B n
  let l := roundedDown D.p D.q n*lanes
  let low := virtualBits B n-l
  let out := post D d L B n a lanes steps pub tag m
  have hn := input.length ▸ (pub 6).isLt
  obtain ⟨installed,saved,arena,levels,length,_⟩ := run.output hn nonempty fields fit
  have addr : DescriptorParameters.saved L w = header w L 0+6 := by
    change ((levelStart L 0+6 : ℕ) : Word w) = ((levelStart L 0 : ℕ) : Word w)+6
    rw [Nat.cast_add,Nat.cast_ofNat]
  have frame : Frame.data (header w L 0+6) out = DescriptorParameters.outputs L B n a l w := addr ▸ saved
  have hpos : ((low+l)*2^low)*2^l = L.positions := by
    have h := CursorRAM.rowCount_eq_positions capacity.split 0
    simpa only [CursorRAM.rowCount,pow_zero,Nat.mul_one,positions] using h
  have initial := initial_run L nonempty (by omega) fit out a low l frame hpos (scalar_fits capacity)
  have base : pub 2 = (L.base : Word w) := Fin.ext (by rw [Fin.val_natCast,← input.base,Nat.mod_eq_of_lt (pub 2).isLt])
  have rows : out (pub 2+8).val = (directoryRows L : Word w) := by rw [input.directory]; exact installed.count
  refine ⟨nonempty,by omega,initial,fun s ↦ BlockHeaderPlan.firstHeader_eval L (pub 2) out s base rows,rows,installed.pitch,?_,
    frame,?_,?_,?_,hpos⟩
  · change (Workspace.ports L.shape.arity (pub 2)).rows.val < levelStart L 0
    rw [base]
    change (ports L w).rows.val < _
    rw [(ports_values L fit).2.2.2.1]
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  · exact (congrArg Fin.val (initial.scalarTail 14 (by decide) (by omega))).trans arena
  · exact (congrArg Fin.val (initial.scalarTail 28 (by decide) (by omega))).trans levels
  · exact (congrArg Fin.val (initial.scalarTail 29 (by decide) (by omega))).trans length

/-- The same length threshold constructs level zero for every memory and
every tag address below the allocated pair workspace. -/
theorem eventually_ready (D : CalendarRows.Spec) (d : ℕ) (F : Shape) (B a lanes steps : ℕ)
    (hB : 1 ≤ B) (hq : 0 < D.q) (hph : 0 < D.phaseRows)
    (hθ : (D.p : ℝ)/D.q ≤ 1) (hlanes : lanes ≤ B)
    (arity : 7 ≤ F.arity) (fields : 30 ≤ F.scalarFields) {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (pub : Fin 11 → Word (wordBits B n)) (tag : Word (wordBits B n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits B n → tag.val < base n →
      ∀ m, let L := LevelFields.tightDirectory (cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n) (CalendarRows.rows D n)
           let l := roundedDown D.p D.q n*lanes
           Ready L a (virtualBits B n-l) l (initialWidth B n) n (pub 2) (post D d L B n a lanes steps pub tag m) := by
  filter_upwards [TransferredStartup.eventually_run D d F B a lanes steps hB hq hph hθ hlanes arity fields hb,
    OnlineCursorStartup.eventually_input D B hB hq hph,
    DescriptorParameters.eventually_tight_capacity D F B a lanes hB hθ hlanes hb,
    DescriptorParameters.eventually_tight_end D F B steps hB hb] with n run input capacity fit
  intro pub tag baseEq len addr lower m
  let P := cursorLayout F B steps ((D.p : ℝ)/D.q) (base n) n
  exact from_startup D d _ B n a lanes steps pub tag m (run pub tag baseEq len addr lower m)
    (input P pub baseEq len addr) (by change 0 < 1 + (steps+1)*Compression.blockCount ((D.p : ℝ)/D.q) n; omega) fields fit rfl
    (capacity P.positions P.levels).2

end CompressorRecords.BlockHeaderStartup

end VPVNP
end Computability
end OAI
