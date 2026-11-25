import OAI.Hierarchy.ProbeFixedDirectInvoice
import OAI.Hierarchy.ProbeFixedSpillTraversal

namespace OAI
/-! # The charge at each ordinary or reserve interval on the actual core routes -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory ReportSockets PurchaseCT CatalogueRows CoreRoute
open scoped BigOperators Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "G" => Commodity (Fin (2^z)) N k
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners
local notation "L" => FeedLayout.atEvent («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit

def feedTraversals (x : Source) (owner parity : Boundary→Bank) (b : Boundary) :=
  boundaryTraversal x v.sampler z v.W k jobs (L b) (owner b) (parity b)

def repairTraversals (x : Source) (p : Recipes) (owner parity : Attempt→Bank) (a : Attempt) :=
  earlyTraversal p x v.sampler z v.W k jobs (spillOrder z v.W k) (owner a) (parity a)

theorem true_feed_invoice (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth)=P.catalogue.boughtRows)
    (m : Memory W) (x : Source) (source : Readable x v.sampler z v.W k jobs order π m)
    (owner parity : Boundary→Bank) (room : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^z<2^W)
    (edges : P.catalogue.rows≤2^W) (b : Boundary) :
    let ord:=P.catalogue.ordinal v.sampler π v.depth marks order size
    let len:=extendedLength ord (lenCode v.sampler π v.depth marks v.radius)
    let routes:=v.feedTraversals P z width x owner parity b
    ((((L b).columns.map (fun c=>c.paidSlice (routes c))).map (fun t=>t.toll m len width)).sum≤(rec m (.feed b)).install) := by
  intro ord len routes
  apply v.receipt_feed P z width r banks src tab dest owners m b len routes
    (fun j=>v.spillPath P z π order ((PurchaseInventory.slotEquiv z N k).symm j))
  · intro l
    exact v.boundary_read P z π order m x source (L b) (owner b) (parity b) l (room l) edges
  · intro i _
    simp only [Equiv.symm_apply_apply]
    exact (v.spill_price P z π marks order size i).le

theorem true_repair_invoice (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth)=P.catalogue.boughtRows)
    (m : Memory W) (x : Source) (p : Recipes) (source : Readable x v.sampler z v.W k jobs order π m)
    (center : Columns z (2^v.W)×Fin k→ℕ) (rom : Installed p (spillOrder z v.W k) (fun i=>PurchaseInventory.slot i) center m)
    (menu : Fintype.card (Actions N k)≤2^W) (goods : Fintype.card G≤2^W) (edges : P.catalogue.rows≤2^W)
    (owner parity : Attempt→Bank) (a : Attempt) (bound : ℕ) (mask mate : Expr)
    (tree : Fin (fmt a).pricedArea.rows→List (Fin P.catalogue.rows)) :
    let ord:=P.catalogue.ordinal v.sampler π v.depth marks order size
    let len:=extendedLength ord (lenCode v.sampler π v.depth marks v.radius)
    let routes:=v.repairTraversals z x p owner parity a
    let forest:=v.nativeTrees P z width a
    let f:=fmt a
    let role:=(StripChart.header F bs a).fieldTerm
    let ids:=StripChart.id F bs P.catalogue a
    let label:=v.directLabel P z width r banks src tab dest owners a
    f.occurrences≤2^W → forest.catalystMate=some (mask,mate) → forest.Reads m tree →
    bound<2^W → f.board.batch.copies<2^W →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≤bound) →
    (∀i : Fin f.pricedArea.rows,f.board.batch.copies*(m (f.pricedArea.broadcast+i.val)).val<2^W) →
    (∀i : Fin f.occurrences,(m (f.pricedArea.direct+i.val)).val≠0→addressPrice len (label.edge.eval m (i.val:Word W)).val+
      (if mask.eval m (i.val:Word W)=0 then 0 else addressPrice len (mate.eval m (i.val:Word W)).val)≤
        v.paidRate P z width r banks src tab dest owners m a i) →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≠0→((tree i).map len).sum≤v.cost.atAttempt a) →
    ((f.paidSlices sink P.catalogue.idBase role ids forest routes bound).map (fun t=>t.toll m len width)).sum≤
      (rec m (.attempt a)).install := by
  intro ord len routes forest f role ids label fit hasMate location word copies bits product cash treeCost
  apply v.attempt_invoice P z width r banks src tab dest owners a m len routes bound mask mate tree
    (fun j=>v.spillPath P z π order ((v.nativeSlots P z width a).symm j)) fit hasMate location
    (v.spill_read P z width π order m x source p center rom menu goods edges (owner a) (parity a) a)
    word copies bits product cash treeCost
  intro i _
  exact (v.spill_price P z π marks order size ((v.nativeSlots P z width a).symm i)).le

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
