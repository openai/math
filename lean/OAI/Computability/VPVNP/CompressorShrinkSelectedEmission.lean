import OAI.Computability.VPVNP.CompressorShrinkCurrentResident

/-! # The shrinking directory produced by the selected native term and placement passes -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
namespace CompressorRecords.ShrinkScheduledTail

open BurstRAM Compression DescriptorSpace BlockPlanner SourceOnline BlockHeaderRun
open SelectedDirectoryHistory PairSimulation.TraversalRows
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f} {i : Fin S.steps} {w g : ℕ}
variable {X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)}
variable {sel : SelectedScore.Selection B X} {tape : List Bool}
variable {workspace : Word w} {positions blocks t cap n : ℕ} {m : Memory w}
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B workspace.val positions blocks
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => first + i.val
local notation "head" => levelStart L cur
local notation "nxt" => levelStart L (cur + 1)
local notation "start" => tableBase L cur (0 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "pt" => Workspace.ports (Schedule.arity (Script.catalog scr)) workspace
local notation "v" => shrinkLevel B f hf i X sel tape
variable {ms ps : List (Packet (BlockProgram.script B) w)}
variable (r : Result (g := g) B workspace positions blocks t cap i X m ms ps)

private theorem and_rec {a b : Prop} {motive : a ∧ b → Sort*}
    (f : ∀ x y, motive ⟨x, y⟩) (h : a ∧ b) : And.rec (motive := motive) f h = f h.1 h.2 := by
  cases h
  rfl

/-- The actual selected placement and preimage collection supply both the
ordered child lists and the five operands installed in the header. Between
the collector and the tail the other kernels retain its occupied table. -/
def Result.selectedEmission (T : IncidenceDirectory w) {selectors : Word w} {p₀ : Fin 14 → Word w}
    {source : Memory w} {p : SelectedStage.Passes w} {q : SelectedFinish.Passes w}
    (built : SelectedFinish.Built B X term 10 selectors p₀ sel source p q)
    (slotRoom : SelectedFinish.stop X term 10 ≤ nxt) (nxtFit : nxt < 2 ^ w)
    (termFit : ShrinkInput.termEnd X start 10 < 2 ^ w)
    (keep : ∀ x, start ≤ x → x < SelectedFinish.stop X term 10 → m x = q.final (p.final source) x)
    (header : ShrinkHeaderReads.Header i X T start L first m)
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w))
    (rows : m (pt).rows.val = (directoryRows L : Word w))
    (length : m (levelStart L 0 + 29) = (n : Word w)) : Emission L cur v m (post m ps) := by
  let finish := SelectedFinish.stop X term 10
  have room : finish < 2 ^ w := slotRoom.trans_lt nxtFit
  let d := selectedShrinkDirectory B f hf i X term 10 selectors
    p₀ sel source p q tape built room.le
  let shr := SelectedFinish.shr X term 10 p₀ source p
  have bank : d.pub = SelectedFinish.params X term 10 shr := by
    simp only [d, selectedShrinkDirectory, SelectedFinish.Built.selectedDirectory,
      ShrinkPreimages.selectedDirectory]
    simp only [and_rec]
    rfl
  have termLo : start ≤ (term).val := by
    obtain ⟨a, b, c, d'⟩ := ShrinkInput.range_bounds X start
    have bound := a.trans (b.trans (c.trans d'))
    unfold ShrinkInput.termEnd at termFit
    change start ≤ (ShrinkInput.stop X start + 2 * _ )%(2 ^ w)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have headLo : head + 54 ≤ start := by
    change head + 54 ≤ head + 66 + 6 * slotCapacity L + 0 * tableWords L
    omega
  have dirLo : start ≤ (d.pub 1).val := by
    rw [bank]
    change start ≤ (SelectedArena.placementWord X term 10 0).val
    have fits : SelectedArena.Fits X term (10 : Word w) := by
      change SelectedArena.endAddr X term 10 < 2 ^ w
      change SelectedArena.endAddr X term 10 + ShrinkPreimages.newCount X
        + ShrinkPreimages.oldCount X
         < 2 ^ w at room
      omega
    rw [SelectedArena.column_value X term 10 fits]
    unfold SelectedArena.placementBase SelectedArena.origin
    omega
  let live := d.transport (m' := m) (fun x hx =>
    (keep x (dirLo.trans (Directory.cells_interval d hx).1) (Directory.cells_interval d hx).2).symm)
  let widened : LevelDirectory v m nxt := {live with inputEnd := live.inputEnd.trans slotRoom}
  exact r.emission T widened shr bank (headLo.trans dirLo) header pitch termFit rows length

end CompressorRecords.ShrinkScheduledTail

end

end VPVNP
end Computability
end OAI
