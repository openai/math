import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorSourceLaunch
import OAI.Computability.VPVNP.CompressorSourceSequence
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# Preparing script-window packets from their source operands

During online planning the recipe sees the same persistent data and
level stride as the physical source computation. Its block-header state
is determined by the actual calendar ordinal. Structural read footprints
therefore suffice to replay each operand formula and to obtain the typed
worker launch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM Schedule BlockPlanner DescriptorSpace SourceTransport PhaseRecipe
open scoped Fin.CommRing

theorem PhaseRecipe.Expr.eval_eq_of_reads {w : ℕ} {data : ℕ → Prop} {pub : Fin 5 → Word w} {s : Word w}
    {m m' : Memory w} (e : Expr) (reads : e.ReadsFrom data pub s m) (h : Agree data m m') :
    e.eval pub s m = e.eval pub s m' := by
  induction e with
  | lit | publicWord | state => rfl
  | load a ih =>
    change m (a.eval pub s m).val = m' (a.eval pub s m').val
    exact (h _ reads.2).trans (congrArg (fun i : Word w ↦ m' i.val) (ih reads.1))
  | binary op a b ih₁ ih₂ => exact congrArg₂ op.eval (ih₁ reads.1) (ih₂ reads.2)

namespace BlockPlanner.Window

variable {w : ℕ} {A : Script} {visits : List BlockPlanner.Visit} (W : Window A visits)
variable (L : Layout) (base : Word w)
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0
local notation "gap" => Fin.val (Schedule.Ports.directory pt - 1)

/-- The recipe may read the immutable pitch and row total in addition to
the data suffix. The tag, active frame and current row are excluded. -/
def operandRegion (A : Script) (L : Layout) (base : Word w) (x : ℕ) :=
  x = (Workspace.ports (arity A.catalog) base).rows.val ∨ x = ((Workspace.ports (arity A.catalog) base).directory - 1).val ∨ levelStart L 0 ≤ x

open private port_bounds from OAI.Computability.VPVNP.CompressorOnlineFootprint
open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot

private theorem calendar_agree (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base)
    (fit : H < 2^w) (ref m : Memory w) (j : Fin A.size) (suffix : Agree (H ≤ ·) ref m)
    (rows : ref (pt).rows.val = m (pt).rows.val) (pitch : ref gap = m gap) :
    Agree (operandRegion A L base) ref (Online.calendarMemory (d := A.size) pt m j) := by
  obtain ⟨hdir,_,ht,_⟩ := port_bounds A L base hg hb fit
  have hd : directoryBase L ≤ H := by
    change directoryBase L ≤ levelsBase L + 0*levelWords L
    dsimp only [levelsBase]; omega
  have hf : base.val + (11 + arity A.catalog) < 2^w := by
    rw [hb,hg]; exact (by dsimp only [directoryBase,plannerTag,frameBase] at hd; omega)
  have hv := field_addresses (arity A.catalog) base hf
  have gapval : gap = directoryBase L - 1 := by
    rw [Fin.val_sub_one_of_ne_zero]
    · rw [hdir]
    · intro h
      have h₀ : directoryBase L = 0 := hdir.symm.trans (h ▸ rfl)
      simp [directoryBase,plannerTag,frameBase] at h₀
  intro x hx
  rcases hx with rfl | rfl | h
  · have hne : (pt).rows.val ≠ (pt).tag.val := by rw [hv.2.2.1,hv.1]; omega
    simpa only [Online.calendarMemory,writeMemory,ite_eq_right hne] using rows
  · have hne : gap ≠ (pt).tag.val := by rw [gapval,ht]; dsimp only [directoryBase,plannerTag,frameBase]; omega
    simpa only [Online.calendarMemory,writeMemory,ite_eq_right hne] using pitch
  · have hne : x ≠ (pt).tag.val := by
      rw [ht]; dsimp only [directoryBase,plannerTag,frameBase] at hd; omega
    simpa only [Online.calendarMemory,writeMemory,ite_eq_right hne] using suffix x h

/-- Source operand evidence. The state here is the first level of the
specified block, rather than the header of the local substep. -/
structure Evaluated (i : Fin visits.length) (t : ℕ) (ref : Memory w) (v : SourceOnline.Visit A w) : Prop where
  index : v.phase = W.index i
  start : (A.visit v.phase).initial.eval (pt).data (levelStart L (A.levelsPerBlock*t) : Word w) ref = v.start
  stop : (A.visit v.phase).stop.eval (pt).data (levelStart L (A.levelsPerBlock*t) : Word w) ref = v.stop
  params : ∀ j, ((A.visit v.phase).params j).eval (pt).data (levelStart L (A.levelsPerBlock*t) : Word w) ref = v.params j
  startReads : (A.visit v.phase).initial.ReadsFrom (operandRegion A L base) (pt).data
    (levelStart L (A.levelsPerBlock*t) : Word w) ref
  stopReads : (A.visit v.phase).stop.ReadsFrom (operandRegion A L base) (pt).data
    (levelStart L (A.levelsPerBlock*t) : Word w) ref
  paramReads : ∀ j, ((A.visit v.phase).params j).ReadsFrom (operandRegion A L base) (pt).data
    (levelStart L (A.levelsPerBlock*t) : Word w) ref

/-- The same packet is launched in every scheduler memory satisfying the
actual ordinal, row count, pitch and persistent-data invariants. -/
theorem prepared (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (i : Fin visits.length) (t : ℕ) (p : SourceWalk.Packet (SourceOnline.Visit A w) w)
    (ref : Memory w) (raw : Agree (H ≤ ·) ref p.input)
    (total : ref (pt).rows.val = (directoryRows L : Word w)) (pitch : ref gap = (levelWords L : Word w))
    (live : A.initial.length+t*A.block.length+(W.position i).val < directoryRows L)
    (ev : Evaluated W L base i t ref p.stage) :
    SourceOnline.Prepared A L base (A.initial.length+t*A.block.length+(W.position i).val) (directoryRows L) p := by
  intro m suffix ord rows _ stride
  have active : m (pt).ordinal.val < m (pt).rows.val := Fin.lt_def.mpr (ord ▸ rows ▸ live)
  have room := ord ▸ live
  have count : m (pt).rows.val = (directoryRows L : Word w) := by
    apply Fin.ext; rw [Fin.val_natCast,← rows,Nat.mod_eq_of_lt (m _).isLt]
  have phase := A.block_phase t (W.position i)
  have pc : p.stage.phase = (W.position i).natAdd A.initial.length := ev.index
  refine ⟨phase.1.trans (congrArg Fin.val pc.symm),?_⟩
  have hdir := (port_bounds A L base hg hb fit).1
  have dir : (pt).data 1 = (directoryBase L : Word w) := by
    change (pt).directory = _; apply Fin.ext; rw [Fin.val_natCast,← hdir,Nat.mod_eq_of_lt (pt).directory.isLt]
  have entry := LevelFields.eval_calendar_entry (Online.calendar A.plan) (pt).data m L dir
    (show (Online.calendar A.plan).rowPitch = L.shape.arity+3 from congrArg (·+3) hg) count stride
  have state : A.recipeState base m = (levelStart L (A.levelsPerBlock*t) : Word w) := by
    change LevelCalendar.header (Online.calendar A.plan) (pt).data m = _
    have ptr := entry.pointer
    change LevelCalendar.header (Online.calendar A.plan) (pt).data m =
      (levelStart L (A.levelsPerBlock*(Online.calendar A.plan).level (m (pt).ordinal.val).val) : Word w) at ptr
    rwa [ord,phase.2] at ptr
  have ag := calendar_agree L base hg hb fit ref m p.stage.phase
    (fun x h ↦ (raw x h).trans (suffix x h)) (total.trans count.symm) (pitch.trans stride.symm)
  have same (e : Expr) (r : e.ReadsFrom (operandRegion A L base) (pt).data (levelStart L (A.levelsPerBlock*t)) ref) :
      A.operand base m p.stage.phase e = e.eval (pt).data (levelStart L (A.levelsPerBlock*t)) ref := by
    unfold Script.operand
    rw [state]; exact (e.eval_eq_of_reads r ag).symm
  apply SourceOnline.launch_of_evaluation A base L hg hb fit m p.stage room active
  · exact (same _ ev.startReads).trans ev.start
  · exact (same _ ev.stopReads).trans ev.stop
  · intro j; exact (same _ (ev.paramReads j)).trans (ev.params j)

end BlockPlanner.Window
end CompressorRecords

end VPVNP
end Computability
end OAI
