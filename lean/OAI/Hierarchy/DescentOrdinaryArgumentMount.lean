import OAI.Hierarchy.DescentOrdinaryReferenceFrame
import OAI.Hierarchy.DescentDatedPhysicalOperandBanks

namespace OAI
/-! # The original reference and six-party operand books at a dated ordinary vertex -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryBorn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
def refChart:=v.reference.withBase (v.refsStart floor)
def refTime:=(4+10*(v.refChart floor).digitSize)+(4+10*(v.refChart floor).tableSize)

theorem ref_end : (v.refChart floor).endAddress=v.birthStart floor:=v.reference.end_eq _
theorem mount_order : v.refsStart floor≤v.birthStart floor ∧ v.birthStart floor≤v.vectorStart floor:=
  ⟨Nat.le_add_right ..,((v.bornBook.order (v.birthStart floor)).1.trans (v.bornBook.order (v.birthStart floor)).2)⟩

def mountProgram (oldDonor : Bank) (w : ℕ) :=
  ((v.refChart floor).program w).seq (v.bornBook.program oldDonor (v.birthStart floor) w)
def mountTime (oldDonor : Bank) :=v.refTime floor+v.bornBook.ticks oldDonor (v.birthStart floor)
def mountImage {w} (oldDonor : Bank) (m : Memory w) :=
  v.bornBook.image oldDonor (v.birthStart floor) ((v.refChart floor).output m)

theorem mount_run {w} (oldDonor : Bank) (m : Memory w) (early : oldDonor.Fits w (v.refsStart floor))
    (fit : v.vectorStart floor<2^w) :
    (v.mountProgram floor oldDonor w).Exec m (v.mountImage floor oldDonor m) (v.mountTime floor oldDonor) ∧
    CheapCode (v.mountProgram floor oldDonor w) ∧
    (∀i,i<v.refsStart floor ∨ v.vectorStart floor≤ i → v.mountImage floor oldDonor m i=m i) ∧
    (v.refChart floor).Issued (v.mountImage floor oldDonor m) :=by
  obtain ⟨first,last⟩:=v.mount_order floor
  have eqn:=v.ref_end floor
  have a:=(v.refChart floor).any m (eqn.le.trans_lt (last.trans_lt fit))
  have b:=v.bornBook.any oldDonor (v.birthStart floor) ((v.refChart floor).output m) ⟨early.1,early.2.1,early.2.2.trans first⟩ fit
  refine ⟨?_,cheap_seq a.2.1 b.2.1,?_,?_⟩
  · intro p r k board pc reg pub exit installed datum cfg mem start same
    exact Procedure.Exec.then a.1 b.1 board pc reg pub exit installed datum cfg mem start same
  · intro i outside
    exact (b.2.2 i (outside.imp_left (·.trans_le first))).trans
      (a.2.2.2 i (outside.imp_right (fun hi=>eqn.le.trans (last.trans hi))))
  · exact (v.refChart floor).issued_through m _ ((v.refChart floor).rooms eqn.le (last.trans_lt fit))
      (fun i hi=>b.2.2 i (.inl hi))

theorem mount_reads {w} (oldDonor : Bank) (m : Memory w) (early : oldDonor.Fits w (v.refsStart floor))
    (chips : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (extent : v.bornBook.rows≤oldDonor.size) (held : Reads oldDonor chips v.bornBook.lanes m)
    (fit : v.vectorStart floor<2^w) (x t j a f) :
    Reads (v.bornBook.bank (v.birthStart floor) x t j a f) (fun h g=>component v.bornBook.bits
      (pointerAt v.bornBook.demand v.bornBook.grain v.bornBook.scale
        (chipDonor v.bornBook.format (chips h g) (finProdFinEquiv (x,t))) j a.val) f)
        v.bornBook.lanes (v.mountImage floor oldDonor m) :=by
  have ord:=v.mount_order floor
  have installed:=(v.refChart floor).any m ((v.ref_end floor).le.trans_lt (ord.2.trans_lt fit))
  apply v.bornBook.issued oldDonor (v.birthStart floor) _ ⟨early.1,early.2.1,early.2.2.trans ord.1⟩ chips extent _ fit
  intro row_
  exact (installed.2.2.2 _ (.inl (((Nat.add_lt_add_left ((row _ _ _ row_).isLt.trans_le extent) _).trans_le early.2.2)))).trans (held row_)
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
