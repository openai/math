import OAI.Computability.VPVNP.CompressorSelectorSitePacket
import OAI.Computability.VPVNP.CompressorShrinkPhysicalWorkerInput
import OAI.Computability.VPVNP.CompressorShrinkTermForward

/-! # Installing the actual shrinking term worker

The gather establishes the physical demand rows in its post-memory. The
next visit has the fixed shrinking motif table and the two strided address
regions selected by that same input prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkCurrentBranch

open BurstRAM Compression DescriptorSpace BlockPlanner SelectedTerms PairSimulation.LocalHistory
open scoped Classical Fin.CommRing
attribute [local irreducible] BlockProgram.script

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (T : IncidenceDirectory w) (start fuel : ℕ) {m : Memory w} (p : ShrinkBranch.Prefix X T start fuel m)
variable (fit : ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel)

local notation "o" => (PassOrigin.shrink i rfl X : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X))
local notation "I" => workerInput B f hf i X T start fuel p fit
local notation "src" => ShrinkInput.demandHead (w := w) X start
local notation "dst" => ShrinkInput.termHead (w := w) X start
local notation "N" => ShrinkTermInputs.motifCount X
local notation "script" => BlockProgram.script B

private theorem start_le_dense (space : ShrinkInput.termEnd X start 10 < 2^w) : start ≤ (src).val := by
  have earlier : start ≤ ShrinkInput.widthBase X start := by
    have greedy := GreedyArena.greedyStop_eq start (Fintype.card X.Base) (S.degreeExponent i.castSucc)
    change start ≤ (((((ShrinkInput.placementBase X start+_)+_)+_)+_)+_)+_
    change ShrinkInput.placementBase X start = start+_+_ at greedy
    omega
  have bound : ShrinkInput.stop X start < 2^w := by unfold ShrinkInput.termEnd at space; omega
  change start ≤ (ShrinkInput.stop X start) % 2^w
  rw [Nat.mod_eq_of_lt bound]
  change start ≤ ShrinkInput.widthBase X start+_+_
  omega

set_option maxHeartbeats 1000000 in
/-- The post-gather worker, table, operand bank and instruction clock of
the shrinking selector packet agree with its installed source worker. -/
theorem sourceWorker (L : Layout) (selection : X.ShrinkSelection B.shrink) (rs : List (Report w))
    (dataStart : levelStart L 0 ≤ start)
    (width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w) :
    ScheduledTrace.SelectorSite.SourceWorker (I) L
      (ShrinkTermOnline.packet B i X T start selection fuel .select p.beforeTerm rs) := by
  have ten : (10 : Word w).val = 10 := Nat.mod_eq_of_lt (fit.wide.trans_lt (10 : Word w).isLt)
  have space := fit.termRoom
  rw [ten] at space
  have bounds := ShrinkInput.termLayout X T start 10 space
  have sep := bounds.2.2.1
  have room := bounds.2.2.2
  have head : levelStart L 0 ≤ (src).val := dataStart.trans (start_le_dense i X start space)
  have dest : levelStart L 0 ≤ (dst).val := head.trans ((Nat.le_add_right ..).trans sep)
  have fits : N < 2^w := by omega
  have code : (script).catalog (ShrinkTermOnline.index B i .select) =
      TermWorker.motifPass (grid o).block (grid o).demandOrder.entries (grid o).e :=
    congrArg BlockPlanner.Visit.worker (ShrinkTermOnline.index_visit B i .select)
  refine ⟨code,rfl,?_,?_,rfl,width,?_,?_,fun _ _ => rfl⟩
  · exact Nat.mod_eq_of_lt fits
  · intro j
    rfl
  · intro j
    change levelStart L 0 ≤ ((src).val+j.val*2)%(2^w)
    have hj := Nat.mul_le_mul_right 2 (show j.val ≤ N from j.isLt.le)
    rw [Nat.mod_eq_of_lt (by omega)]
    exact head.trans (Nat.le_add_right ..)
  · intro j
    change levelStart L 0 ≤ ((dst).val+j.val*10)%(2^w)
    have hj := Nat.mul_le_mul_right 10 (show j.val ≤ N from j.isLt.le)
    rw [Nat.mod_eq_of_lt (by omega)]
    exact dest.trans (Nat.le_add_right ..)

end CompressorRecords.ShrinkCurrentBranch

end

end VPVNP
end Computability
end OAI
