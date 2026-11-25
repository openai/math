import OAI.Hierarchy.ProbeFixedWideRowBoards
import OAI.Hierarchy.ProbeFixedCatalystBirth

namespace OAI
/-! # Real packed chain births on the original wide route and its chronological inner states -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage PurchaseFrozen
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (h width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "coreEnd" => CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth
  (WideMemory.K h v.W) (packed).groups (WideMemory.H h v.W k v.wideJobs) (P).catalogue.coreRows

variable (π : Equiv.Perm (Fin (2^h))) (mem : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "seen[" m "]" => CoreRoute.Seen order v.radius groups packed socket v.depth π m

def wide_birth_rows (boot : seen[mem]) (whole : Calendar.mounted C (events v.mesh) mem) (room : (A).endAddress v.mesh<2^W)
    (p : Fin (v.mesh.inject+v.mesh.cool)) (a : Fin v.mesh.outerFuel) (j : Fin v.mesh.reserveSteps)
    (t : Fin v.mesh.innerFuel) :
    PurchasedBirth ((S).outer p a).market.shelf (S).sampler π v.depth ((S).stratumHeader p a)
      (innerState C mem p a j t) k := by
  let outer:=Attempt.outer p.val a.val
  let first:=entryMemory C mem outer
  have sourcePrefix:=v.wideGeometryPrefix h width
  have coreLow : coreEnd≤(A).first:=sourcePrefix.2.2.trans (v.catalyst_initial_le_first P h width)
  have keep:=entryMemory_low C A mem outer whole
    (fun e x low=>(v.event_prefix P h width r banks src tab dst owners e x low).1)
  have word : coreEnd<2^W := coreLow.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have old : CoreRoute.Seen order v.radius groups packed socket v.depth π first :=
    boot.frame word (fun i hi=>keep i (hi.trans_le coreLow))
  have born:=v.catalyst_birth (K:=WideMemory.K h v.W) (G:=(packed).groups) (H:=WideMemory.H h v.W k v.wideJobs)
    (R:=(P).catalogue.coreRows) h width (P).joint (P).catalogue socket r banks src tab dst owners mem π
    p a j t whole p.isLt a.isLt j.isLt t.isLt sourcePrefix.2.1 sourcePrefix.2.2 old.board.columns.geometry old.board.rom.keys
  have step:=(inner_slot C mem p a j t p.isLt a.isLt j.isLt t.isLt whole).choose_spec
  rw [←step.entryMemory]
  exact born

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
