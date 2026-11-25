import OAI.Hierarchy.DescentContactOutputRead

namespace OAI
/-! # Address bounds for all four installed contact output operands -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactSenderMass DescentContactDonorSelection
open DescentOrdinaryAtomFieldRAM.ROM DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

private theorem headerFits (C : DescentResetSignedHaloMatrix.Shelf) (r : C.Fits w) (floor : ℕ)
    (before : C.high≤floor) (x : Expr) (fits : x.Fits w floor) :
    (body C.header x (List.finRange (C.degree+1))).Fits w floor :=by
  have prev:=C.headerRoom r
  have move {B : Bank} (f : B.Fits w C.high) : B.Fits w floor:=⟨f.1,f.2.1,f.2.2.trans before⟩
  generalize List.finRange (C.degree+1) = terms
  induction terms with
  | nil => trivial
  | cons j js ih =>
    have readCell : (cell C.header x j).Fits w floor :=
      ⟨move (prev.pageFits j),⟨move prev.tableFits,⟨⟨move prev.offFits,trivial⟩,trivial⟩⟩,
        ⟨move prev.shiftFits,fits⟩⟩
    exact ⟨move prev.joinApply,ih,move prev.joinShift,readCell⟩

private theorem viewed (C : DescentContactPreROM.Layout) (x : Expr) (top : ℕ)
    (held : x.Fits w top) (before : C.markerBase≤top) (room : top<2^w) :
    (C.priorView x).Fits w top :=by
  apply ProtocolRAM.Calendar.CatalogueRows.fits_atRow _ _ held
  apply ProtocolRAMGeneratedWrite.fits_mono _ before
  exact ⟨DescentContactProbePitch.table_fits _ _ _ _ _ _ (before.trans_lt room) 0,trivial⟩

variable (A : Shape) (donorStart first : ℕ)
set_option quotPrecheck false
local notation "D₀" => A.donor
local notation "N" => (D₀).lows*(2*(D₀).cap)
local notation "M" => (D₀).batch
local notation "b" => (D₀).fieldBits
local notation "t" => A.metaBits
local notation "C" => (D₀).markers donorStart A.shapes A.markerBits
local notation "top" => A.projected first
local notation "mass" => DescentContactMaskShape.massEnd (D₀) first
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
    (r : A.donor.Space donorStart u w) (past : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (room : A.endAddress first<2^w)

include r past room in
theorem inputFits (q : Fin A.sockets) : A.InputFits donorStart first u q w:=by
  let sh:=(D₀).halo donorStart u.routes.roster
  obtain ⟨first₀,middle₀,halo₀,choice₀,top₀,last₀⟩:=A.cuts first
  have small : A.choicePage first<2^w:=top₀.trans_lt (last₀.trans_lt room)
  have oldToMarker : (C).markerBase≤(C).endAddress:=(C).ordered.2.2.2.1.trans (C).ordered.2.2.2.2
  have early : first≤(A.choicePage first):=first₀.trans (middle₀.trans (halo₀.trans (choice₀.trans le_rfl)))
  have oldTop : (C).markerBase≤(A.choicePage first):=oldToMarker.trans (past.trans early)
  have preTop : (D₀).endAddress donorStart≤(A.choicePage first):=(C).ordered.1.trans
    ((C).ordered.2.1.trans ((C).ordered.2.2.1.trans oldTop))
  have move (p : Expr) {j : ℕ} (before : j≤(A.choicePage first)) (fit : p.Fits w j) : p.Fits w (A.choicePage first) :=
    ProtocolRAMGeneratedWrite.fits_mono p before fit
  have roomSh:= (D₀).haloFits donorStart u r
  have shTop : sh.high≤(A.choicePage first):=((D₀).halo_end donorStart u.routes.roster).le.trans preTop
  have markerEnd : A.marker first≤(A.choicePage first):=middle₀.trans (halo₀.trans (choice₀.trans le_rfl))
  have massEnd : mass≤(A.choicePage first):=(Nat.le_add_right ..).trans markerEnd
  have mark (j : Fin N) : (A.markAt donorStart q j).Fits w (A.choicePage first):=by
    apply move _ (past.trans early)
    exact ⟨(C).output_fits _ (past.trans_lt (early.trans_lt small)),trivial⟩
  have own (j : Fin N) : (A.ownAt donorStart q j).Fits w (A.choicePage first):=
    viewed _ _ _ (move _ preTop ((D₀).priorSensor_fits donorStart u r _ j 0)) oldTop small
  have flag (j : Fin N) : (A.markFlag donorStart first q j).Fits w (A.choicePage first) :=
    DescentContactWidthPage.general_fits _ _ _ _ _ (mark j) (halo₀.trans (choice₀.trans le_rfl)) small
  have ownShape : (A.ownShape donorStart first).Fits w (A.choicePage first) :=
    DescentContactWidthPage.general_fits _ _ _ _ _ (move _ oldTop ((C).shapeView_fits (oldTop.trans_lt small)))
      (choice₀.trans le_rfl) small
  have other (j : Fin N) : (A.otherAt donorStart first q j).Fits w (A.choicePage first) :=
    DescentContactWidthPage.general_fits _ _ _ _ _ (mark j) ((Nat.le_add_right ..).trans
      (halo₀.trans (choice₀.trans le_rfl))) small
  have old (side : Bool) (j : Fin N) : (A.oldAt donorStart first u side j).Fits w (A.choicePage first):=by
    let pair:=finProdFinEquiv.symm j
    let chip:=Expr.lookup (u.signed pair.1 pair.2) .row
    have before : donorStart≤(A.choicePage first):=((D₀).ordered donorStart).1.trans
      (((D₀).ordered donorStart).2.1.trans (((D₀).ordered donorStart).2.2.trans preTop))
    have chipFits : chip.Fits w (A.choicePage first):=
      move _ before ⟨(r.sender.route pair.1 pair.2).source,trivial⟩
    apply DescentContactWidthPage.general_fits _ _ _ _ _ _ le_rfl small
    apply viewed _ _ _ _ oldTop small
    cases side
    · apply headerFits sh roomSh _ shTop
      exact DescentContactWidthPage.general_fits _ _ _ _ _ chipFits
        (roomSh.static_.trans ((Nat.le_add_right ..).trans ((sh.extents roomSh).2.2.1.trans shTop))) small
    · apply headerFits sh roomSh _ shTop
      exact DescentContactWidthPage.general_fits _ _ _ _ _ chipFits markerEnd small
  have invoice : (A.ownMass donorStart first q).Fits w (A.choicePage first):=by
    apply DescentContactWidthPage.general_fits _ _ _ _ _ _ (choice₀.trans le_rfl) small
    apply viewed _ _ _ _ oldTop small
    apply move _ massEnd
    exact ⟨(DescentContactSenderMass.Date.calendar ((D₀).sender donorStart) first).output_fits
      («N» := N+1) (field:=b) q.val q.isLt (massEnd.trans_lt small),trivial⟩
  exact ⟨own,flag,other,ownShape,old,invoice⟩

include r past room in
theorem fieldsAt_fits (q : Fin A.sockets) (f : Fin 4) :
    (A.fieldsAt donorStart first u q f).Fits w top :=by
  let req:=fun z : Fin A.sockets=>(A.socketWing z).2
  have raw:=A.inputFits donorStart first u r past room q
  have lim:=A.cuts first
  have small : top<2^w:=lim.2.2.2.2.2.trans_lt room
  have move (e : Expr) (fits : e.Fits w (A.choicePage first)) : e.Fits w top :=
    ProtocolRAMGeneratedWrite.fits_mono e lim.2.2.2.2.1 fits
  have ends (j : Fin N) (s : Bool) : (A.endsAt donorStart first u q j s).Fits w top:=by
    apply DescentContactCoordinateJoint.fits
    · split <;> first | exact move _ raw.here | exact move _ (raw.remote j)
    · exact move _ (raw.halo s j)
  have banks (i : Fin (A.sockets+1)) (k : Fin 2) :
      (bank (DescentResetDonorBook.page req b t M) A.choiceBits (A.choicePage first) (DescentResetDonorBook.ix i k)).Fits w top :=
    bank_room _ _ _ _ _ (DescentResetDonorBook.size req b t M _) le_rfl small
  have witness (j : Fin N) (s : Option Bool) : (A.witnessAt donorStart first u q j s).Fits w top:=by
    cases s with
    | none=>exact ends j _
    | some d=>exact ⟨banks q.succ 1,ends j d,banks q.succ 0,
        DescentContactCoordinateJoint.scaled_fits _ (move _ (raw.used j)) _⟩
  have selected (s : Option Bool) : (A.selectAt donorStart first u q s).Fits w top:=by
    apply DescentContactDonorCargo.fold_fits _ _ _ _ _ (banks 0 0) (banks 0 1)
    exact fun j=>⟨banks q.succ 1,witness j s,banks q.succ 0,move _ (raw.own j)⟩
  fin_cases f <;> first | exact move _ raw.mass | exact selected _

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
