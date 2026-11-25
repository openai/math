import OAI.Hierarchy.TaggedWideInstalledBanks
import OAI.Hierarchy.TaggedWideNativeMenu

namespace OAI
/-! # The installed dyadic cut on the aligned public terminal rows -/

noncomputable section
set_option quotPrecheck false

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows ProtocolRAMEmit
open Tagged TaggedShorterBudget Tagged.WideStack ProtocolRAMReportedPorts
open TaggedShorterSupergroups Filter
open scoped Classical BigOperators Topology

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (hW : 0<v.W)
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "geometry" => typeMenu κ A v.W m k jobs ell hW (fun _=>short+ell)
local notation "menu" => (geometry).menu u δ ξ
local notation "roleCount" => copies k jobs
local notation "groupDir" x => stageDir (x).h v.W roleCount (2*roleCount)
  (show 2*roleCount≤2^(2*roleCount) from Nat.lt_two_pow_self.le)
local notation "portCount" x => 2^(superAddress v.W (2*roleCount) (x).h)
local notation "slotCountAt" x => purchaseSlots (x).h v.W k jobs ell

/-- Install the common class purchase on the actual aligned terminal records. The
volume comes from the single resolution of the printed area/cash ledger. -/
def printed_installed (prices : v.PhysicalCounts u A δ ξ m) (positive : 0≤κ)
    (x : WideParent κ A) (i : Fin (m+1))
    (buy : Purchased F menu x i (slotCountAt x)
      (purchaseCandidates x.h v.W k jobs (slotCountAt x) ((menu).height i x)
        (purchaseModules v.W u δ ξ menu x i)) (purchaseModules v.W u δ ξ menu x i) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : 1+(menu).height i x+(menu).height i x≤(menu).payload i x)
    (π : Equiv.Perm (Fin (2^x.h))) (b : Board) (marks : Marks x.h v.W k jobs)
    (order : Fin b.coreRows≃Edges v.sampler x.h (2^v.W) k)
    (size : jobs*(PurchaseFrozen.count x.h (2^v.W) k*
      PurchaseFrozen.paths x.h v.sampler.degree (publicTiles k v.W-1))=b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row) (bits : Catalogue v.sampler π (publicTiles k v.W-1) marks→ℕ)
    («rec» : Alignment b v.sampler π (publicTiles k v.W-1) marks v.radius raw (fun j=>(raw j).width)
      (b.ordinal v.sampler π (publicTiles k v.W-1) marks order size))
    (read : ∀e,(raw ((b.ordinal v.sampler π (publicTiles k v.W-1) marks order size) e)).width=bits e)
    (R : ℕ) (paid : TermBudget p q Q Λ (2^x.h) x.w v.radius (∑_j:Columns x.h (2^v.W)×Fin k,R)
      (scaleOf v.sampler π (publicTiles k v.W-1) marks)
      (fun e=>(lenCode v.sampler π (publicTiles k v.W-1) marks v.radius e:ℝ)) (fun e=>(bits e:ℝ)/x.w))
    (keep : («rec».geometry x.w R).links.Keep (2^x.h))
    (idRead : ∀j,(raw j).link=j.val)
    (widthRoom : ∀j,(raw j).width≤2^ell*x.w)
    (port : Bool→Fin b.rows→Fin (portCount x))
    (anchor : {j : Fin b.rows // 0<pieces (atScale (b.transport order) (fun _=>0) 0 raw) x.w j}×Bool ↪
      Fin (groupDir x).groups × Fin (portCount x))
    (owner : ∀j side,(anchor (j,side)).1.val=(raw j.val).group)
    (pin : ∀j side,(anchor (j,side)).2=port side j.val) :
    Leaf.Installed F (groupDir x).groups (portCount x) (2^ell) x.w m i.val
      (atScale (b.transport order) (fun _=>0) 0 raw) := by
  let rows:=atScale (b.transport order) (fun _=>0) 0 raw
  have volume:=prices (Real.logb x.h x.w) ⟨by linarith [x.formats.2.2.1],x.formats.2.2.2⟩
    (groups:=(groupDir x).groups) π b marks order size raw bits «rec» read paid keep i.val
  refine installedPurchase v.W m k jobs ell short hW x i buy groupsFit metadata rows
    (fun a b h=>Fin.ext ((idRead a).symm.trans (h.trans (idRead b)))) ?_
    port anchor owner pin (pieces_of_bit_bound rows x.w (2^ell) x.formats.2.1 ?_)
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using volume
  · intro j
    change (if _ then (raw j).width else 0)≤_
    split_ifs
    · exact widthRoom j
    · exact Nat.zero_le _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
