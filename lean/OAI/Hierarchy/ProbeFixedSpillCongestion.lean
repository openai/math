import OAI.Hierarchy.ProbeFixedClockInvoice
import OAI.Hierarchy.ProbeArchiveRowBound
import OAI.Hierarchy.ProbeBoundaryOccupancy
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # Per-edge occupancy of the original early-spill and boundary-feed programs -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalogueRows PurchaseCT StripChart
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "D" => 2^v.W
local notation "N" => Stages z D
local notation "W" => Native.wordBits z D Native.copies
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "G" => Commodity (Fin (2^z)) N k
local notation "fmt" => v.nativeFormats P z width
local notation "L" => FeedLayout.atEvent («N»:=N) v.mesh (v.privateArena P z width) fmt P.joint.initial width v.keepLimit

private def coreLabels {α : Type*} (b : Board) (order : Fin b.coreRows ≃ α) : α ↪ Fin b.rows :=
  ⟨fun e => b.coreIndex (order.symm e), fun _ _ eqn => order.symm.injective (Fin.ext (congrArg (fun z : Fin b.rows => z.val) eqn))⟩

/-- The coefficient is fixed with the public geometry before the height is selected. -/
def overflowFactor (K : ℕ) := (1+publicStages v.W*(2*k))*(2*publicStages v.W+2)*K

theorem repair_spill_load (π : Equiv.Perm (Fin (2^z))) (order : Fin P.catalogue.coreRows ≃ Edges v.sampler z D k)
    (m : Memory W) (x : Source) (p : Recipes) (source : Readable x v.sampler z v.W k jobs order π m)
    (center : Columns z D×Fin k → ℕ) (rom : Installed p (spillOrder z v.W k) PurchaseInventory.slot center m)
    (menu : Fintype.card (Actions N k) ≤ 2^W) (goods : Fintype.card G ≤ 2^W)
    (edges : P.catalogue.rows ≤ 2^W) (owner parity : Attempt → Bank) (a : Attempt) (K : ℕ)
    (e : Fin P.catalogue.rows) :
    let A := (fmt a).pricedArea
    let t := v.repairTraversals z x p owner parity a
    (∀ j : Fin A.goods, (m (A.output+A.goods+A.goods+j.val)).val ≤ K*width) →
    (PaidWidths.paidSpill A t.positions t.owner t.parity t.edge t.sourceRow).load m e ≤ v.overflowFactor K*width := by
  intro A t cap
  have read := v.spill_read P z width π order m x source p center rom menu goods edges (owner a) (parity a) a
  have bound := t.core_spill_bound (S:=v.sampler) (h:=z) (d:=D) (k:=k)
    A m e π (coreLabels P.catalogue order) (v.nativeSlots P z width a).symm
    (K*width) read cap
  simpa only [fixed_stage_count,overflowFactor,Nat.mul_assoc] using bound

private def rowInLane (l : Fin (FeedLayout.lanes N k)) : Fin (2^z) ↪ G where
  toFun j := (PurchaseInventory.slotEquiv z N k).symm (finProdFinEquiv (l,j))
  inj' _ _ e := (Prod.mk.inj (finProdFinEquiv.injective ((PurchaseInventory.slotEquiv z N k).symm.injective e))).2

theorem boundary_spill_load (π : Equiv.Perm (Fin (2^z))) (order : Fin P.catalogue.coreRows ≃ Edges v.sampler z D k)
    (m : Memory W) (x : Source) (source : Readable x v.sampler z v.W k jobs order π m)
    (room : ∀ l : Fin (FeedLayout.lanes N k), laneWidth (decodeLane l)*2^z < 2^W)
    (edges : P.catalogue.rows ≤ 2^W) (owner parity : Boundary → Bank) (b : Boundary)
    (l : Fin (FeedLayout.lanes N k)) (K : ℕ) (e : Fin P.catalogue.rows) :
    let c := (L b).column l
    let t := v.feedTraversals P z width x owner parity b c
    (∀ j : Fin c.rows, (m (c.overflow+j.val)).val ≤ K*width) →
    (c.paidSlice t).load m e ≤ v.overflowFactor K*width := by
  intro c t cap
  have read := v.boundary_read P z π order m x source (L b) (owner b) (parity b) l (room l) edges
  have bound := t.boundary_spill_bound (S:=v.sampler) (h:=z) (d:=D) (k:=k)
    c m e π (coreLabels P.catalogue order) (rowInLane (v:=v) (z:=z) l)
    (K*width) read cap
  simpa only [fixed_stage_count,overflowFactor,Nat.mul_assoc] using bound

/-- All source expressions in the original fixed core fit below each public output page. -/
theorem wide_spill_safe {F : Type} [Field F] {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width out : ℕ) (above : (v.widePlacement h width).joint.initial ≤ out)
    (word : out < 2^(Native.wordBits h (2^v.W) Native.copies)) :
    let K := WideMemory.K h v.W
    let groups := (WideMemory.dir h v.W k v.wideJobs).groups
    let H := WideMemory.H h v.W k v.wideJobs
    let R := WideMemory.R v.sampler h v.W k
    Safe (source v.sampler h v.W k v.wideJobs v.depth K groups H R) v.sampler h v.W k v.wideJobs
      (Native.wordBits h (2^v.W) Native.copies) out :=
  source_safe v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) (Native.wordBits h (2^v.W) Native.copies) out
    ((v.wideGeometryPrefix h width).2.2.trans above) word

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
