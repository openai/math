import OAI.Hierarchy.DescentRetainedHomeMoverLayout
import OAI.Hierarchy.DescentRetainedPrimitiveMover
import OAI.Hierarchy.DescentRetainedControlRead
import OAI.Hierarchy.DescentRetainedTargetPlacementRun

namespace OAI
/-! # Drive the retained primitive mover from the elected basis and the measured old-home packet -/
namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRetainedSetup DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentRetainedHomeMover.Layout)
abbrev prior:=z.toLayout.prior
abbrev role:=z.toLayout.role
abbrev role_zero:=z.toLayout.role_zero

variable (floor : ℕ) (prev : Fin z.transfer.blocks→Bank) (key count inverse : Bank)
variable (which : Fin z.shapes→Option ℕ) (packet : Expr)
local notation "lo" => z.controlBase floor
local notation "mid" => z.bookBase floor
local notation "hi" => z.placementBase floor

def channels (target : Fin z.shapes) (j : Fin z.transfer.channels) : Expr :=
  z.control.targetStream which lo target (.lookup (z.transfer.hostBank floor j) .row)
def query (i : Fin (z.transfer.nodes*z.shapes)) :=
  let p : Fin z.transfer.nodes×Fin z.shapes:=finProdFinEquiv.symm i
  DescentOperandFamilyBook.expr z.role z.transfer.decodedLanes mid p.1 (z.channels floor which p.2)
def kept (t : Fin z.shapes):= (which t).isSome
def movedImage {w : ℕ} (m : Memory w):=z.transfer.movedImage floor (z.prior prev) key m
def ordered {w : ℕ} (m : Memory w):=z.control.image which lo packet (z.movedImage floor prev key m)
def prepared {w : ℕ} (m : Memory w):=DescentOperandFamilyBook.image z.role z.transfer.decodedLanes mid (z.ordered floor prev key which packet m)
def finalMem {w : ℕ} (m : Memory w):=DescentRetainedTargetPlacement.Chart.image z.placement z.batch hi (z.kept which) (z.query floor which) count inverse
  (z.prepared floor prev key which packet m)
def program (w : ℕ) :=(((z.transfer.moved floor w (z.prior prev) key).seq (z.control.program which lo w packet)).seq
  (DescentOperandFamilyBook.program z.role z.transfer.decodedLanes mid w)).seq
  (DescentRetainedTargetPlacement.Chart.program z.placement z.batch hi w (z.kept which) (z.query floor which) count inverse)
def ticks (w : ℕ) :=z.transfer.movedTicks floor w (z.prior prev) key+z.control.ticks which lo w packet+
  DescentOperandFamilyBook.ticks z.transfer.nodes z.transfer.channels z.transfer.stripWord z.transfer.decodedLanes+
  DescentRetainedTargetPlacement.Chart.ticks z.placement z.batch hi (z.query floor which) count inverse

theorem bounds : floor≤lo ∧ lo≤ mid ∧ mid≤hi ∧ hi≤z.endAddress floor:=by
  obtain ⟨a,b,c,d,e,_⟩:=z.transfer.order floor
  refine ⟨a.trans (b.trans (c.trans (d.trans e))),?_,Nat.le_add_right ..,?_⟩
  · rw [bookBase,z.control.translate]
    exact Nat.le_add_right ..
  · rw [endAddress,DescentRetainedTargetPlacement.Chart.affine]
    exact Nat.le_add_right ..

theorem channels_fit {w : ℕ} (space : z.endAddress floor<2^w) (t : Fin z.shapes) (j : Fin z.transfer.channels) :
    (z.channels floor which t j).Fits w mid:=by
  obtain ⟨_,a,b,c⟩:=z.bounds floor
  have upper:=b.trans_lt (c.trans_lt space)
  have old:=Strip.fits (w:=w) (z.transfer.mixed floor) z.transfer.hosts z.transfer.grouped z.transfer.matrixLanes z.transfer.decodedLanes z.transfer.stripWord j (a.trans_lt upper)
  let e : Expr:=.lookup (z.transfer.hostBank floor j) .row
  exact (z.control.paths_fit which lo e (.lit 0) t (ProtocolRAMGeneratedWrite.fits_mono e a ⟨old.1,trivial⟩) trivial upper).1

theorem query_fit {w : ℕ} (space : z.endAddress floor<2^w) (i : Fin (z.transfer.nodes*z.shapes)) :
    (z.query floor which i).Fits w hi:=by
  apply DescentOperandFamilyBook.expr_fits
  · exact z.channels_fit floor which space _
  · exact (z.bounds floor).2.2.2.trans_lt space

structure Room (w : ℕ) : Prop where
  previous : ∀j,(prev j).Fits w floor
  saved : key.Fits w floor
  countFit : count.Fits w floor
  inverseFit : inverse.Fits w floor
  packetFit : packet.Fits w floor
  lanes : 0<z.lanes
  blocks : 0<z.blocks
  roof : z.endAddress floor<2^w

variable {w : ℕ}
theorem any (m : Memory w) (r : z.Room floor prev key count inverse packet w) :
    (z.program floor prev key count inverse which packet w).Exec m
      (z.finalMem floor prev key count inverse which packet m) (z.ticks floor prev key count inverse which packet w) ∧
    CheapCode (z.program floor prev key count inverse which packet w) ∧
    ∀j,j<floor ∨ z.endAddress floor≤j→z.finalMem floor prev key count inverse which packet m j=m j:=by
  obtain ⟨a,b,c,d⟩:=z.bounds floor
  have three:=d.trans_lt r.roof
  have two:=c.trans_lt three
  have one:=b.trans_lt two
  have done₁:=z.transfer.moved_any floor (z.prior prev) key m (fun j=>r.previous _) r.saved one
  have seen:=ProtocolRAMGeneratedWrite.fits_mono _ a r.packetFit
  have done₂:=z.control.any which lo packet (z.movedImage floor prev key m) seen two
  have done₃:=DescentOperandFamilyBook.any z.role z.transfer.decodedLanes mid (z.ordered floor prev key which packet m) three
  have base:=a.trans (b.trans c)
  have keep {B : Bank} (ok : B.Fits w floor) : B.Fits w hi:=⟨ok.1,ok.2.1,ok.2.2.trans base⟩
  have done₄:=DescentRetainedTargetPlacement.Chart.any z.placement (z.batch) hi (z.kept which) (z.query floor which) count inverse
    (z.prepared floor prev key which packet m) r.lanes r.blocks (z.query_fit floor which r.roof)
    (keep r.countFit) (keep r.inverseFit) r.roof
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then done₁.1 done₂.1) done₃.1) done₄.1,
    cheap_seq (cheap_seq (cheap_seq done₁.2.2 done₂.2.1) done₃.2.1) done₄.2.2,?_⟩
  intro j h
  exact (done₄.2.1 j (h.imp_left (·.trans_le base))).trans ((done₃.2.2.1 j (h.imp (·.trans_le (a.trans b)) (d.trans ·))).trans
    ((done₂.2.2 j (h.imp (·.trans_le a) ((c.trans d).trans ·))).trans (done₁.2.1 j (h.imp_right ((b.trans (c.trans d)).trans ·)))))

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
