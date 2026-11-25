import OAI.Hierarchy.DescentExteriorRotationSlot
import OAI.Hierarchy.DescentExteriorReelPrograms

import OAI.Hierarchy.DescentExteriorDateTables
import OAI.Hierarchy.DescentExteriorPublished
import OAI.Hierarchy.DescentExteriorPrintedCalendar

namespace OAI
/-! # The physically retained per-date rotation words give the complete matrix execution -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts DescentExteriorMatrixUpdate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail wire hist : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (path : Path initial current) (plan : Reel) (fence : ℕ) {bw : ℕ}

/-- Its contents are one row-code scan and a literal publicly computed data interval per date. -/
def Path.savedRotations (tail : ℕ) (m : Memory bw) : Prop := by
  induction path with
  | here=>exact True
  | @ordinary A age zi Di zn Dn src prev fee he T c norm dst ticket ih=>
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact ih ∧ plan.Slot age fence (ordinaryMap S k tail age ticket.hubRows.choose) rot m
  | @reset A age zi Di n h C f g cut tail' src prev ctl b ih=>
    exact ih ∧ plan.Slot age fence (resetMap S k tail' age b.age) b.frame.basis m

omit [Fintype P] in
theorem Path.savedRotations_move {m o : Memory bw} (saved : path.savedRotations plan fence tail m)
    (low : ∀a,a < fence → o a=m a) : path.savedRotations plan fence tail o := by
  induction path with
  | here=>trivial
  | ordinary prev ticket ih=>exact ⟨ih saved.1,saved.2.move low⟩
  | reset prev b ih=>exact ⟨ih saved.1,saved.2.move low⟩

omit [Fintype P] in
theorem Path.savedRotations_raise {m : Memory bw} (saved : path.savedRotations plan fence tail m)
    {top : ℕ} (increase : fence ≤ top) : path.savedRotations plan top tail m := by
  induction path with
  | here=>trivial
  | ordinary prev ticket ih=>exact ⟨ih saved.1,saved.2.raise increase⟩
  | reset prev b ih=>exact ⟨ih saved.1,saved.2.raise increase⟩

theorem Path.matrixInputs_of_saved (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (p : ℕ) (hp : 0<p)
    (a : Archive I) (seed : a.Particles initial) (r : path.recorded p) (m : Memory bw)
    (saved : path.savedRotations plan fence tail m) (high : ∀i' < i,fence ≤ plan.output i') :
    path.matrixInputs base radix p hp a seed r (plan.cells (S.groupWidth k tail 0+k)) m := by
  induction path with
  | here=>trivial
  | @ordinary A age zi Di zn Dn src prev fee he T c norm dst ticket ih=>
    obtain ⟨archive,row⟩:=saved
    have got:=row.read (fun j hj=>high j (by omega))
    refine ⟨ih r archive (fun j hj=>high j (by omega)),got.1,?_⟩
    rw [ordinaryMap_eq S k tail age ticket.hubRows.choose prev.frozen_age]
    exact got.2
  | @reset A age zi Di n h C f g cut tail' src prev ctl b ih=>
    have tails : tail=tail':=by simpa only [Nat.log2_two_pow] using congrArg Nat.log2 (base.symm.trans ctl.base)
    subst tail'
    obtain ⟨archive,row⟩:=saved
    have got:=row.read (fun j hj=>high j (by omega))
    refine ⟨ih r.1 archive (fun j hj=>high j (by omega)),got.1,?_⟩
    rw [resetMap_eq S k tail age b.age prev.frozen_age]
    exact got.2

end
end Hierarchy.DescentSixParty.Chronology

end OAI
