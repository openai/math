import OAI.Hierarchy.DescentPhysicalRootBook

namespace OAI
/-! # Matrix operands of the physical reserved root book -/
namespace Hierarchy.DescentFallbackPeriod.Projected.RootSources
open DescentSIMDLookup DescentPackedColony DescentSharedLeafLookup DescentResetHostSize
open DescentSixParty.Chronology DescentResetGates DescentPackedPrivateMenu
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {n h r D cap field bit : ℕ}

/-- On the matrix shelf, order comparisons use the cast table at the real book's
cast address, and reservation fields use its own auxiliary and rank pages. -/
theorem reserved_matrix_reads (src : RootSources D (2^r) cap) (board : NonlinearExpanders.Graph n h)
    (packet f Ht C groupDigits batches layerBits : ℕ) (primitive : CanonicalTag (2^n) → Cell bit)
    (hostBound factor hubBits : ℕ) (neighbors hubs : Bank) (base groups batch cmp : ℕ)
    (pair : ℕ → Header → Fin D → Fin D → Fin 6 → Expr) (p : RootPage r (2^n))
    (side : Bool) (root : Code r) (j : Fin (DescentRotorWindowArchive.count D (2^r) cap)) :
    let book := src.reserved (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch cmp pair p
    (book.good side root (.inl false)).2.reads j =
      ({src with
        oldOrder := fun i v => .lookup (DescentRootOrderCast.bank
          (book.castAt base hostBound groups batch) cmp batch) (src.oldOrder i v)
        reservation := pair (book.auxAt base hostBound groups batch)
          (book.rankHeader base hostBound groups batch p)} : RootSources D (2^r) cap).matrixRow hostBound j := by
  intro book
  let first := src.physical (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch cmp
  let chosen : RootSources D (2^r) cap := {src with
    reservation := pair
      (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch p)}
  let raw := ({chosen with oldOrderBits:=some cmp} : RootSources D (2^r) cap).wired (field:=field)
    board packet f Ht C groupDigits batches layerBits primitive hostBound factor hubBits neighbors hubs
    base groups batch
  let readAt (sites : ℕ × ℕ × Header) :=
    ({src with
      oldOrder := fun i v => .lookup (DescentRootOrderCast.bank sites.1 cmp batch) (src.oldOrder i v)
      reservation := pair sites.2.1 sites.2.2} : RootSources D (2^r) cap).matrixRow hostBound j
  have cast : raw.castAt base hostBound groups batch = book.castAt base hostBound groups batch :=
    chosen.physical_cast_site (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch cmp
  have sites := src.reservation_sites (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch cmp pair p
  trans readAt (raw.castAt base hostBound groups batch,first.auxAt base hostBound groups batch,
    first.rankHeader base hostBound groups batch p)
  · change (({chosen with
        oldOrderBits := some cmp
        oldOrder := fun i v => .lookup
          (DescentRootOrderCast.bank (raw.castAt base hostBound groups batch) cmp batch) (src.oldOrder i v)} :
        RootSources D (2^r) cap).matrixRow hostBound j) = _
    dsimp only [readAt,matrixRow]
    rcases DescentRotorWindowArchive.ix.symm j with (((i|ji)|ij)|(ord|fieldSlot)) <;> rfl
  · change readAt (raw.castAt base hostBound groups batch, first.auxAt base hostBound groups batch,
        first.rankHeader base hostBound groups batch p) =
      readAt (book.castAt base hostBound groups batch, book.auxAt base hostBound groups batch,
        book.rankHeader base hostBound groups batch p)
    apply congrArg readAt
    exact Prod.ext cast (Prod.ext sites.1 sites.2.1)

end
end Hierarchy.DescentFallbackPeriod.Projected.RootSources

end OAI
