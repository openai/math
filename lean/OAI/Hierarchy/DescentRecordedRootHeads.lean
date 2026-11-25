import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentResetPreparedOperands
import OAI.Hierarchy.DescentPreparedReservations

namespace OAI
/-! # Address bounds for the previous capacity and selected depth in a reset root -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSIMDLookup ProtocolRAM

/-- The scalar header is followed by the stencil readers and the final stencil output. -/
theorem header_before_output (S : StencilBook) (base : ℕ) : S.afterHeader base ≤ S.endAddress base := by
  let C := S.readers base
  let L := S.last base
  have first : S.afterHeader base ≤ C.first := Nat.le_add_right ..
  have planes : C.first ≤ C.planeBase := Nat.le_add_right ..
  have readers : C.planeBase ≤ C.stop := Nat.le_add_right ..
  have table : C.stop ≤ L.table := Nat.le_add_right ..
  have mask : L.table ≤ L.mask := Nat.le_add_right ..
  have scratch : L.mask ≤ L.scratch := Nat.le_add_right ..
  have out : L.scratch ≤ L.out := Nat.le_add_right ..
  exact ((((((first.trans planes).trans readers).trans table).trans mask).trans scratch).trans out).trans
    (Nat.le_add_right ..)
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPackedColony DescentPackedColony.Phase.Arena DescentPlainTerminal.Suffix
open DescentSixParty DescentSixParty.Chronology DescentResetGates DescentSharedLeafLookup DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (base bankStart hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n) → Cell bit) (page : RootPage r (2^n))
set_option quotPrecheck false
local notation "book₀" => a.issuedBook E stencil old base bankStart hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive page
local notation "src₀" => a.issuedSources E stencil old base bankStart hubWidth peers oldId priorCapacity f fee full total portPitch

/-- Both broadcast operands fit in the root header, including the old count and the double
lookup into the strided estimator depth table. -/
theorem issuedHeads_fit (geom : StencilBook.Geometry stencil old base bankStart w)
    (previous : stencil.endAddress base ≤ a.origin) (host : oldId.Fits w a.origin)
    (capFits : priorCapacity.Fits w a.origin) (top : a.headerEnd book₀ < 2^w) :
    (src₀).priorCap.Fits w (a.headerEnd book₀) ∧ (src₀).relativeDepth.Fits w (a.headerEnd book₀) := by
  let finish := a.headerEnd book₀
  have limits := (book₀).limits a.projectionEnd H (2^c) M
  have start : a.origin ≤ finish :=
    a.origin_le_projection.trans (limits.1.trans (limits.2.1.trans limits.2.2))
  have middle := (stencil.header_before_output base).trans (previous.trans start)
  obtain ⟨_,depth,_,_,_,_,_,_,baseBefore⟩ := stencil.banks old base bankStart geom
  have first := baseBefore.trans middle
  have liftBank {b : Bank} {i j : ℕ} (le : i ≤ j) (fits : b.Fits w i) : b.Fits w j :=
    ⟨fits.1,fits.2.1,fits.2.2.trans le⟩
  let rack := Expr.lookup oldId .row
  let far := (stencil.header base).levelAt old.levels rack
  have rackFits : rack.Fits w finish := ⟨liftBank start host,trivial⟩
  have farFits : far.Fits w finish := ⟨liftBank first geom.old.levels,liftBank middle depth,rackFits⟩
  let date := Expr.branch .lt rack old.count
    (.op .add (.op .sub (Cutoff.level (.lit c) far) (.lit c)) (.lit 1)) (.lit 0)
  have dateFits : date.Fits w finish :=
    ⟨rackFits,ProtocolRAMGeneratedWrite.fits_mono _ first geom.old.count,
      ⟨⟨⟨trivial,farFits,farFits,trivial⟩,trivial⟩,trivial⟩,trivial⟩
  have rom := a.prepared_broadcast_room_of_top book₀ top page
  exact ⟨⟨rom.repeatFit,⟨rom.cut,trivial⟩,ProtocolRAMGeneratedWrite.fits_mono _ start capFits⟩,
    ⟨rom.repeatFit,⟨rom.cut,trivial⟩,dateFits⟩⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
