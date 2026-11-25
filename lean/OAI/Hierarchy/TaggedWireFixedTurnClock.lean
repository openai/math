import OAI.Hierarchy.TaggedWireOriginalWork
import OAI.Hierarchy.TaggedWireTurnClock
import OAI.Hierarchy.TaggedWireLinearRoleRoom
import OAI.Hierarchy.TaggedWireRoleTurnBoard

namespace OAI
/-! # A fixed linear clock for the actual eleven-column signed turn program -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups

/-- The coefficient precedes all heights, catalogues, coordinates, role pages,
and purchased endpoints. Both old and new sides charge every padded ordinal. -/
theorem fixed_clock (S : PurchaseSampler) (W k attempts depth : ℕ) :
    ∃ rate : ℕ,∀ (h R H : ℕ) (_order : Fin R≃Edges S h (2^W) k)
      (dir : Directory (reserved h W (copies k attempts)) H) (v : BoughtSockets.Directory attempts)
      (b : CatalogueRows.Board) (start out base bits siteBase superBase K G slots : ℕ)
      (paidBank active reserve used : Bank),
      let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
      let z:=shape (R:=R) S dir edges
      let core:=CoreCatalogue.source base R bits siteBase superBase K G slots k attempts
      let paid:=paidInputs b (coreInputs base (z.free start) R bits superBase K k attempts)
        (boughtInputs v S h W k depth K)
      let board:=turnBoard (R:=R) S dir (edges:=edges) start out core paid
      board.extendedTime (Inventory.ofOriginal (z.stop start) board.old paidBank active reserve used)≤rate*2^h := by
  let e:=CoreCatalogue.coreFactor S (2^W) k+boughtFactor (2^W) k attempts S.degree depth
  let u:=paidWidthWork W k attempts
  let n:=oldWork k u (coreWidthWork k attempts)
  let count:=oldFactor (2^W) k e+e+1
  refine ⟨turnRate n u*count,?_⟩
  intro h R H order dir v b start out base bits siteBase superBase K G slots paidBank active reserve used
  let edges:=R+attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)
  let z:=shape (R:=R) S dir edges
  let core:=CoreCatalogue.source base R bits siteBase superBase K G slots k attempts
  let paid:=paidInputs b (coreInputs base (z.free start) R bits superBase K k attempts) (boughtInputs v S h W k depth K)
  let board:=turnBoard (R:=R) S dir (edges:=edges) start out core paid
  have p (s : Bool) : (board.finish s).Work u :=
    paid_work b v S h W k depth K base (z.free start) R bits superBase s
  have q (s : Bool) : (board.before s).Work n :=
    full_original_work (z.chart start) b v S start board.old (z.ext start) (z.axis start)
      base (z.free start) R bits siteBase superBase K G slots h W k depth s
  have raw : edges≤e*2^h := padded_edges (attempts:=attempts) S depth order
  have old : board.old≤oldFactor (2^W) k e*2^h := old_bound raw
  have width : board.old+board.edges+1≤count*2^h := by
    change board.old+edges+1≤(oldFactor (2^W) k e+e+1)*2^h
    simpa only [Nat.add_mul,Nat.one_mul] using
      Nat.add_le_add (Nat.add_le_add old raw) (Nat.two_pow_pos h)
  exact (board.turn_clock (z.stop start) paidBank active reserve used q p).trans
    ((Nat.mul_le_mul_left (turnRate n u) width).trans_eq (Nat.mul_assoc ..).symm)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
