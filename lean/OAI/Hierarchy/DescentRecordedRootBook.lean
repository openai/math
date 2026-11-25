import OAI.Hierarchy.DescentPhysicalRootBook
import OAI.Hierarchy.DescentRotorReservationSources

namespace OAI
/-! # Printed root tables addressed from the actual reset stencil and estimator fields -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPackedColony DescentPackedColony.Phase.Arena DescentPlainTerminal.Suffix
open DescentSixParty DescentSixParty.Chronology DescentResetGates DescentSharedLeafLookup DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr)
    (f fee full total portPitch : ℕ)
local notation "Y" => 2^n
local notation "groups" => 2^c
local notation "levels" => Nat.clog 2 (E.dim+2)

def issuedSources : RootSources D (2^r) cap :=
  let scalarEnd:=DescentSharedBookScan.Public.stop a.projectionEnd r (2^n) D H (2^Ht)
  let broadcastTable:=DescentSharedLeafLookup.Public.header scalarEnd H groups M field oldId
  let share:=DescentRotorPeerIssue.broadcast broadcastTable.cut broadcastTable.broadcast
  let rack:=Expr.lookup oldId .row
  let far:=(stencil.header stencilBase).levelAt old.levels rack
  let depth:=Expr.branch .lt rack old.count
    (.op .add (.op .sub (DescentPlainTerminal.Suffix.Cutoff.level (.lit c) far) (.lit c)) (.lit 1)) (.lit 0)
  let order:=fun i j : Fin (2^r)=> stencil.orderExpr old stencilBase splitBank hubWidth i.val j.val
  let init:=a.rootSources peers order (fun _ _ _=>.lit 0) (share priorCapacity) (share depth)
  {init with extraSize:=DescentReservationHeader.reserveEntries H levels total,
             extraWord:=DescentReservationHeader.reserveEntry H portPitch E.dim E.high levels total fee (2^f*full) (2^n)}

def issuedBook (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n)) :
    RootBook n r D (2^r) cap field :=
  let src:=a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
  let pair:=fun table hdr=> ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c)
    table levels total (.lookup oldId .row)
  src.reserved board packet f Ht C groupDigits batches layerBits primitive H factor hubWidth old.roster old.hubs
    a.projectionEnd groups M stencil.n pair bookPage

/-- The source expressions installed for the matrix rows, shared with the later sender
directory. Each comparison and reservation read uses this book's actual static address. -/
def atlasSources (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n)) : RootSources D (2^r) cap :=
  let src:=a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
  let b:=a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
    board packet C groupDigits batches layerBits factor primitive bookPage
  let table:=DescentRootOrderCast.bank (b.castAt a.projectionEnd H groups M) stencil.n M
  let feePage:=b.auxAt a.projectionEnd H groups M
  let header:=b.rankHeader a.projectionEnd H groups M bookPage
  {src with oldOrder:=fun i j=>.lookup table (src.oldOrder i j)
            reservation:=ClosedReset.Recorded.reservationFields E header peers H portPitch c (E.dim-c) feePage levels total (.lookup oldId .row)}

theorem issued_literals (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n)) :
    let book:=a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
      board packet C groupDigits batches layerBits factor primitive bookPage
    book.previousNeighbors=old.roster ∧ book.previousHubs=old.hubs ∧ book.shapes=2^Ht ∧
    book.originalBits=some stencil.n ∧ book.extraSize=DescentReservationHeader.reserveEntries H levels total ∧
    book.extraWord=DescentReservationHeader.reserveEntry H portPitch E.dim E.high levels total fee (2^f*full) (2^n) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
