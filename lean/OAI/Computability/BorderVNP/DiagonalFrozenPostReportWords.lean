import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.DiagonalJointVisitCalls
import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch

/-! # The signed control words read on each actual frozen report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM

/-- The compacted directory and the words returned by the native fragment
launcher on this team's own report memory. -/
abbrev IssuedReportFrame {w : ℕ} (task : SignedTaskArena.Layout) (pub : Arg → Word w) (m : Memory w)
    (offsets ctl rows : ℕ) : Prop :=
  let out := readings m
  ∃ fr : FragmentDirectoryInput pub m,
    (FragmentRows.Layout.fromFrame (pub 0).val out).Fits w out ∧ fr.layout.count=rows ∧
    fr.bucket=task.fragments.bucket (fr.layout.stream out).length ∧ task.fragments.cells=fr.layout.cells ∧
    fr.layout.host.count=task.cube.cables ∧ fr.control=ctl ∧
    (∀ i : Fin 37, out (ctl+i.val)=task.controls i.val) ∧ FragmentRows.SparseGeometry task fr.layout offsets ctl

/-- Read the six post-report conditions directly from the compacted directory
at the returned memory. The row count is the one consumed by the native
fragment program. -/
theorem FragmentDirectoryInput.postReportWords {w : ℕ} {pub : Arg → Word w} {m : Memory w}
    (fr : FragmentDirectoryInput pub m) (task : SignedTaskArena.Layout) {offsets ctl num : ℕ}
    (compacted : fr.layout.count=num) (cells : task.fragments.cells=fr.layout.cells)
    (cables : fr.layout.host.count=task.cube.cables)
    (controls : ∀ i : Fin 37, readings m (ctl+i.val)=task.controls i.val)
    (sparse : FragmentRows.SparseGeometry task fr.layout offsets ctl) (room : num ≤ task.cube.maxRows) :
    let head := (pub 0).val
    let out := readings m
    let actual := FragmentRows.Layout.fromFrame head out
    actual.Fits w out ∧ out (head+92)=ctl ∧ (∀ i : Fin 37, out (ctl+i.val)=task.controls i.val) ∧
      actual.host.count=task.cube.cables ∧ out (head+9)≤task.cube.maxRows ∧ out (head+11)=task.cube.cells := by
  intro head out actual
  have atFrame : fr.layout=actual := fr.loaded
  refine ⟨atFrame ▸ fr.fit, ?_, controls, atFrame ▸ cables, ?_, ?_⟩
  · exact (congrArg FragmentRows.Layout.control atFrame).symm.trans sparse.control
  · exact (congrArg FragmentRows.Layout.count atFrame).symm.le.trans (compacted.trans_le room)
  · exact (congrArg FragmentRows.Layout.cells atFrame).symm.trans cells.symm

end RoutingISA.Evaluator.ScheduleClock

namespace Diagonal

open Branch Crossing Cover Packing ExternalSew PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open TeamScales Filter DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena
open TeamContraction TeamContraction.ProcessorSlots GeometryAdvice BorderVNP.Cube BorderVNP.Cube.Physical
open RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open scoped Classical BorderVNP.Epoch.Cube

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- On the chosen frozen task, the reserved row table contains all public
directory entries. Each returning visited report thus has its complete
fragment frame, including an empty compacted directory. -/
theorem JointSchedule.frozen_post_report_words (n l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories)
    (pp lp : ℕ → ℕ × ℕ) {offsets ctl R : ℕ}
    (U : Fin (R+1) → PinStart SparseExterior.driver n (b.physical.word n)) :
    let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
    ∀ (u : Fin (R+1)) (p : (U u).Prefix task.id),
    let pub := (U u).pub
    let head := (pub 0).val
    let reported := (PinStart.visits task.id U p).reports.val.2.2
    let out := readings reported
    let actual := FragmentRows.Layout.fromFrame head out
    IssuedReportFrame task pub reported offsets ctl (dir.directory pp lp).length →
    actual.Fits (b.physical.word n) out ∧ out (head+92)=ctl ∧ (∀ i : Fin 37, out (ctl+i.val)=task.controls i.val) ∧
      actual.host.count=task.cube.cables ∧ out (head+9)≤task.cube.maxRows ∧ out (head+11)=task.cube.cells := by
  intro task u p pub head reported out actual receipt
  obtain ⟨fr,_,count,_,cells,cables,_,controls,geo⟩ := receipt
  exact fr.postReportWords task count cells cables controls geo
    ((dir.directory_length_le pp lp).trans (Nat.le_add_right dir.candidates (task.cube.header.d.choose 2)))

end Diagonal

end BorderVNP
end Computability
end OAI
