import OAI.Hierarchy.DescentCalendarPrintedRotationSlots
import OAI.Hierarchy.DescentExternalRotationROM

namespace OAI
/-! # Recover the exterior interpreter's whole history from the physically saved rotation words -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open DescentExteriorMatrixUpdate ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k tail wire hist bw : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (p : Path initial current) (reset : ℕ→Bool) (location : ℕ→ℕ)

def Path.RotationWords (m : Memory bw) : Prop :=by
  induction p with
  | here=>exact True
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst t ih=>
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact ih ∧ reset age=false ∧ m (location age)=((matrixCode rot).val:Computability.VPVNP.BurstRAM.Word bw)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl b ih=>
    exact ih ∧ reset age=true ∧ m (location age)=((matrixCode b.frame.basis).val:Computability.VPVNP.BurstRAM.Word bw)

omit [Fintype P] in
theorem Path.RotationWords.move {m o : Memory bw} (old : p.RotationWords reset location m)
    (keep : ∀j < i,o (location j)=m (location j)) : p.RotationWords reset location o :=by
  induction p with
  | here=>trivial
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst t ih=>
    exact ⟨ih old.1 (fun j hj=>keep j (by omega)),old.2.1,(keep age (by omega)).trans old.2.2⟩
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl b ih=>
    exact ⟨ih old.1 (fun j hj=>keep j (by omega)),old.2.1,(keep age (by omega)).trans old.2.2⟩

variable (base : ℕ)
local notation "fence" => Calendar.stop S k tail base
local notation "reel" => Calendar.reel S k tail base reset location

omit [Fintype P] in
theorem Path.printed_rotations (m : Memory bw) (old : p.RotationWords reset location m)
    (groupBits : S.baseGroups=2^tail) (previous : ∀age<S.length,location age<base)
    (room : fence+S.length+2<2^bw)
    (resident : ∀age (alive : age<S.length),(Calendar.entry S k tail base reset (w:=bw) age alive).Resident m) :
    p.savedRotations reel fence tail m :=by
  induction p with
  | here=>trivial
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst ticket ih=>
    have alive:=ticket.hubRows.choose
    exact ⟨ih old.1,Calendar.ordinary_slot S k tail base reset location m age alive
      previous room (resident age alive) old.2.1 _ old.2.2⟩
  | @reset _ age _ _ n h C f g cut t src prev ctl b ih=>
    have same : t=tail :=(Nat.pow_right_inj (by decide : 1<2)).mp (ctl.base.symm.trans groupBits)
    subst t
    have alive:=b.age
    exact ⟨ih old.1,Calendar.reset_slot S k tail base reset location m age alive
      previous room (resident age alive) old.2.1 _ old.2.2⟩

omit [Fintype P] in
/-- Starting on the attained date memory, the one table installer returns all rotations in the
format that the original exterior interpreter reads. It also retains every old date-bank value. -/
theorem Path.issue_rotations (m : Memory bw) (old : p.RotationWords reset location m)
    (groupBits : S.baseGroups=2^tail) (previous : ∀age<S.length,location age<base)
    (alive : i≤S.length) (room : fence+S.length+2<2^bw) :
    let sheet:=Calendar.sheet S k tail base reset bw
    sheet.program.Exec m (sheet.output m) (4+10*(S.length*Calendar.stride S k tail)) ∧
      p.savedRotations reel fence tail (sheet.output m) ∧
      ∀a,a<base ∨ fence≤a → sheet.output m a=m a :=by
  intro sheet
  obtain ⟨exec,_,_,res,frame⟩:=Calendar.issue S k tail base reset m (by omega)
  exact ⟨exec,p.printed_rotations reset location base (sheet.output m)
    (Path.RotationWords.move p reset location old (fun j hj=>frame _ (.inl (previous j (hj.trans_le alive)))))
    groupBits previous room res,frame⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
