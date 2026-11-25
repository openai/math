import OAI.Hierarchy.DescentRecordedPeriod
import OAI.Hierarchy.DescentRegisteredFinalEvent
import OAI.Hierarchy.DescentRegisterInstructionRun
import OAI.Hierarchy.DescentSnapshotRankCapture
import OAI.Hierarchy.DescentExteriorSnapshotCalendar

namespace OAI
/-! # Snapshot ranks along an actual path of the registered native program -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentExteriorReplay ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist len w : ℕ} {q ε : ℝ}

/-- The one new public rank bank written at a reset. All previous rank banks
are handled by the chronological frame. -/
def Path.Event.rankPublication {I U : MarkedWorld F d P bits} {z₀ D₀ z D : ℕ}
    {entry : Reached I G q ε S k 0 z₀ D₀ wire hist}
    {exit : Reached U G q ε S k len z D wire hist} {p : Path entry exit}
    {i : ℕ} (e : p.Event i) (directory : Bank) (endAddress : ℕ) (m : Memory w) : Prop := by
  cases e with
  | ordinary => exact True
  | @reset _ _ _ _ _ _ _ _ _ _ src _ before closed after joined =>
    let vertex := closed.frame.host.symm.toEmbedding.trans src.vertex
    exact directory.Fits w endAddress ∧ ∀v : closed.next.V,
      directory.read m ((closed.reset.rawHostRank closed.terminals vertex v).val : Computability.VPVNP.BurstRAM.Word w) =
        ((closed.reset.denseHostRank closed.terminals vertex v).val : Computability.VPVNP.BurstRAM.Word w)

section Recorded
variable {I U V : MarkedWorld F d P bits} {a i j g₁ g₂ g₃ D₁ D₂ D₃ : ℕ}
  {r₁ : Reached I G q ε S k a g₁ D₁ wire hist}
  {r₂ : Reached U G q ε S k i g₂ D₂ wire hist}
  {r₃ : Reached V G q ε S k j g₃ D₃ wire hist}

omit [Fintype P] in
private theorem Path.snapshot_recorded_before (scale : ℕ) (p : Path r₁ r₂) (tail : Path r₂ r₃) :
    (p.append tail).recorded scale → p.recorded scale := by
  induction tail with
  | here => exact id
  | ordinary _ _ ih => exact ih
  | reset _ _ ih => exact fun h => ih h.1

variable {origin : Reached I G q ε S k 0 g₁ D₁ wire hist} {p : Path origin r₃} {age : ℕ}

def Path.Event.resetRecorded (e : p.Event age) (scale : ℕ) : Prop :=
  match e with
  | .ordinary .. => True
  | .reset _ batch _ _ => batch.Recorded scale

omit [Fintype P] in
theorem Path.Event.resetRecorded_of_whole (e : p.Event age) (scale : ℕ) (recorded : p.recorded scale) :
    e.resetRecorded scale := by
  cases e with
  | ordinary => trivial
  | reset before batch after joined =>
    exact (Path.snapshot_recorded_before scale (before.reset batch) after (joined.symm ▸ recorded)).2
end Recorded

omit [Fintype P] in
private theorem Path.next_snapshot_frame {I U : MarkedWorld F d P bits} {age g₀ D₀ g D : ℕ}
    {initial : Reached I G q ε S k 0 g₀ D₀ wire hist}
    {current : Reached U G q ε S k age g D wire hist}
    (p : Path initial current) (A : Snapshots k) (code : DateCode w) {lo hi header : ℕ}
    (m : Memory w) (old : p.snapshotRanks A lo m) (grows : lo≤hi)
    (native : RegisterTimeline.Protected code lo header)
    (early : ∀j<age,∀r,A.compact j=some r → header<r.base) :
    p.snapshotRanks A hi (code.nextMemory m) := by
  obtain ⟨out,ran,keep⟩ := native.run m
  rw [DateCode.nextMemory_eq code ran]
  apply p.snapshotRanks_banks A old grows
  intro j hj bank slot x lower upper
  have fit := p.snapshotRanks_old_bank A old j hj bank slot
  exact keep x (upper.trans_le fit.2.2) (ne_of_gt ((early j hj bank slot).trans_le lower))

namespace RegisterTimeline
variable {Choice : Type*} (traces : Choice→RunTrace G q ε S k wire hist len bits d)
    {n degree : ℕ} (menu : Menu n degree) (first : Position) (c : Choice) (mem : Memory w)
    (A : Snapshots k) (directory : ℕ→Bank)
local notation "trace₀" => traces c
local notation "steps" => issued (w:=w) traces menu
local notation "cursor" => calendar (w:=w) traces menu first
local notation "cpu" => instruction (w:=w) traces menu first
local notation "tape" => DateCode.history cpu mem
variable (native : ∀i,Protected (instruction (w:=w) traces menu first i) (calendar (w:=w) traces menu first i).floor menu.header)
    (early : ∀i,∀r,A.compact i=some r → menu.header<r.base)
    (slot : ∀i (e : (traces c).path.Event i),
      A.compact i=if e.isReset then some (directory i) else none)
    (written : ∀i (e : (traces c).path.Event i),
      e.rankPublication (directory i) (calendar (w:=w) traces menu first (i+1)).floor (DateCode.history (instruction (w:=w) traces menu first) mem (i+1)))

include native early slot written in
omit [Fintype P] in
theorem snapshot_ranks_prefix {U : MarkedWorld F d P bits} {age g D : ℕ}
    {current : Reached U G q ε S k age g D wire hist}
    (p : Path (trace₀).first current) (tail : Path current (trace₀).last)
    (joined : p.append tail=(trace₀).path) :
    p.snapshotRanks A (cursor age).floor (tape age) := by
  induction p with
  | here => trivial
  | @ordinary _ i _ _ _ _ src prev _ he T ballot norm dst ticket ih =>
    let e : (trace₀).path.Event i := .ordinary prev ticket tail joined
    have past := ih ((Path.here.ordinary ticket).append tail)
      ((Path.append_cut_assoc prev (Path.here.ordinary ticket) tail).symm.trans joined)
    have saved := Path.next_snapshot_frame prev A (cpu i) (tape i) past
      (selected_floor steps i (cursor i)) (native i) (fun j _ r hit => early j r hit)
    exact ⟨saved,slot i e⟩
  | @reset _ i _ _ _ _ _ _ _ _ _ src prev ctl closed ih =>
    let e : (trace₀).path.Event i := .reset prev closed tail joined
    have past := ih ((Path.here.reset closed).append tail)
      ((Path.append_cut_assoc prev (Path.here.reset closed) tail).symm.trans joined)
    have saved := Path.next_snapshot_frame prev A (cpu i) (tape i) past
      (selected_floor steps i (cursor i)) (native i) (fun j _ r hit => early j r hit)
    have found := written i e
    exact ⟨saved,directory i,slot i e,found⟩

include native early slot written in
omit [Fintype P] in
theorem issued_snapshot_ranks :
    (trace₀).path.snapshotRanks A (cursor len).floor
      (DateCode.history (RunTrace.machine traces (fun i _=>cpu i)) mem len) := by
  rw [history_from_cuts traces menu first c mem len le_rfl]
  exact snapshot_ranks_prefix traces menu first c mem A directory native early slot written (trace₀).path .here rfl

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
