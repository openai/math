import OAI.Hierarchy.DescentContactOutputCasts
import OAI.Hierarchy.DescentContactOutputRead

namespace OAI
/-! # The selector consumes the five attained fields of the sparse donor rectangle -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentContactSenderMass
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
set_option quotPrecheck false
local notation "D" => A.donor
local notation "H" => A.sparseHosts
local notation "G" => (D).groups
local notation "M" => (D).batch
local notation "b" => (D).fieldBits
local notation "t" => A.metaBits
local notation "N" => (D).lows*(2*(D).cap)
local notation "C" => (D).markers donorStart A.shapes A.markerBits
local notation "P" => A.marker first
local notation "U" => A.choicePage first
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
local notation "shelf" => (D).halo donorStart u.routes.roster

structure RawIndicators (q : Fin A.sockets) where
  own : Fin N→Fin H→Fin G→Cell b
  marker : Fin N→Fin H→Fin G→Cell A.markerBits
  shape : Fin H→Fin G→Cell b
  halo : Bool→Fin N→Fin H→Fin G→Cell (D).cargoBits
  mass : Fin H→Fin G→Cell b

def rawHalo (s : Bool) (j : Fin N) :=
  let pair:=finProdFinEquiv.symm j
  let chip:=Expr.lookup (u.signed pair.1 pair.2) .row
  (C).priorView (if s then DescentResetSignedHaloMatrix.Right.port (shelf) (DescentContactMaskShape.massEnd (D) first) chip
    else (shelf).port chip)

def rawMass (q : Fin A.sockets) := (C).priorView (.lookup (DescentContactMaskShape.bank (D) donorStart first q) .row)

namespace RawIndicators
variable {A} {q : Fin A.sockets}
def indicators (x : RawIndicators A q) : Indicators A q where
  own:=x.own
  used j h g:=DescentContactMarkerShape.flag A.markerBits b (x.marker j h g) 0
  remote j h g:=DescentContactMarkerShape.shape A.shapes A.markerBits t (x.marker j h g) 0
  here h g:=DescentContactWidthPage.recode t (x.shape h g)
  halo s j h g:=DescentContactWidthPage.recode t (x.halo s j h g)
  mass h g:=DescentContactWidthPage.recode t (x.mass h g)
end RawIndicators

structure RawRead (q : Fin A.sockets) (x : RawIndicators A q) (m : Memory w) : Prop where
  own : ∀j,A.PresentAt P m (A.ownAt donorStart q j) (x.own j)
  marker : ∀j,A.PresentAt P m (A.markAt donorStart q j) (x.marker j)
  shape : A.PresentAt P m (C).shapeView x.shape
  halo : ∀s j,A.PresentAt P m (A.rawHalo donorStart first u s j) (x.halo s j)
  mass : A.PresentAt P m (A.rawMass donorStart first q) x.mass

theorem inputs_of_raw (q : Fin A.sockets) (x : RawIndicators A q) (m : Memory w)
    (raw : A.RawRead donorStart first u q x m) (room : U<2^w) :
    A.InputFits donorStart first u q w ∧ A.InputRead donorStart first u q x.indicators (A.halos first m) :=by
  have read:=A.casts first m room
  have own j:=read.raw _ _ (raw.own j)
  have flag j:=read.flag _ _ (raw.marker j)
  have shape j:=read.shape _ _ (raw.marker j)
  have here:=read.count _ _ raw.shape
  have old s j:=read.halo _ _ (raw.halo s j)
  have mass:=read.count _ _ raw.mass
  exact ⟨⟨fun j=>(own j).1,fun j=>(flag j).1,fun j=>(shape j).1,here.1,fun s j=>(old s j).1,mass.1⟩,
    fun j=>(own j).2,fun j=>(flag j).2,fun j=>(shape j).2,here.2,fun s j=>(old s j).2,mass.2⟩

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
