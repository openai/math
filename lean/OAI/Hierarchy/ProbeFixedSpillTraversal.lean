import OAI.Hierarchy.ProtocolRAMCoreSpillRoom
import OAI.Hierarchy.ProtocolRAMCatalogueCoreMount
import OAI.Hierarchy.ProbeFixedSpillCost
import OAI.Hierarchy.ProbeFixedEventCosts

namespace OAI
/-! # Repeated native early spills on the same immutable priced catalogue -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open ReportSockets PurchaseCT CatalogueRows CoreRoute
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}

private theorem reindex_walk {b t w edges : ℕ} (eq : b=t) (v : Traversals) (m : Memory w)
    (walk : Fin b→List (Fin edges)) (reads : v.Reads m walk) :
    v.Reads m (fun j : Fin t=>walk ((finCongr eq).symm j)) := by
  cases eq;exact reads

namespace FixedProtocolFormat
variable (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "G" => Commodity (Fin (2^z)) N k
local notation "fmt" => v.nativeFormats P z width

def spillOrder (z «W» k : ℕ) : Orders z (2^«W») k :=
  ⟨(PurchaseInventory.slotEquiv z _ k).trans (finCongr (PurchaseInventory.card_commodity z _ k).symm),
    Fintype.equivFin _⟩

def spillPath (π : Equiv.Perm (Fin (2^z))) (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (i : G) := (commodityWalk (S:=v.sampler) π i).map (fun e=>P.catalogue.coreIndex (order.symm e))

theorem spill_price (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth)=P.catalogue.boughtRows) (i : G) :
    let ord:=P.catalogue.ordinal v.sampler π v.depth marks order size
    ((v.spillPath P z π order i).map (extendedLength ord (lenCode v.sampler π v.depth marks v.radius))).sum=
      routeCap N v.radius (PurchaseInventory.lane i) :=
  core_spill_cost π marks (P.catalogue.ordinal v.sampler π v.depth marks order size) v.radius i

theorem spill_read (π : Equiv.Perm (Fin (2^z))) (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory W) (x : Source) (source : Readable x v.sampler z v.W k jobs order π m) (p : Recipes)
    (center : Columns z (2^v.W)×Fin k→ℕ)
    (rom : Installed p (spillOrder z v.W k) (fun i=>PurchaseInventory.slot i) center m)
    (menu : Fintype.card (Actions N k)≤2^W) (goods : Fintype.card G≤2^W)
    (edges : P.catalogue.rows≤2^W) (owner parity : Bank) (a : Attempt) :
    (earlyTraversal p x v.sampler z v.W k jobs (spillOrder z v.W k) owner parity).Reads m
      (fun j : Fin (fmt a).pricedArea.goods=>v.spillPath P z π order ((v.nativeSlots P z width a).symm j)) := by
  let o:=spillOrder z v.W k
  let B:=P.catalogue.coreMount π (fun _=>0 : Site z (2^v.W) k→Fin 1) order m
  have real:=earlyTraversal_reads p x π _ B order o (fun _=>rfl) m source center rom menu goods edges owner parity
  let shape := (PurchaseInventory.card_commodity z N k).trans (v.stock_goods P z width a).symm
  exact reindex_walk shape _ m (fun j=>B.ordinary (o.core.symm j)) real

theorem boundary_read (π : Equiv.Perm (Fin (2^z))) (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory W) (x : Source) (source : Readable x v.sampler z v.W k jobs order π m)
    (L : FeedLayout z N k) (owner parity : Bank) (l : Fin (FeedLayout.lanes N k))
    (room : laneWidth (decodeLane l)*2^z<2^W) (edges : P.catalogue.rows≤2^W) :
    (boundaryTraversal x v.sampler z v.W k jobs L owner parity (L.column l)).Reads m
      (fun j=>v.spillPath P z π order ((PurchaseInventory.slotEquiv z N k).symm (finProdFinEquiv (l,j)))) := by
  let B:=P.catalogue.coreMount π (fun _=>0 : Site z (2^v.W) k→Fin 1) order m
  exact boundary_reads x π _ B order (fun _=>rfl) m source L l room edges owner parity

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
