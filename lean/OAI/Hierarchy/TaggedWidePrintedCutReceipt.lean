import OAI.Hierarchy.TaggedWideInstalledPurchase
import OAI.Hierarchy.TaggedWideFundedCutPins

namespace OAI
/-! # Terminal value of the cut bought on each real funded transport class -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows ProtocolRAMEmit
open Tagged TaggedShorterBudget Tagged.WideStack ProtocolRAMReportedPorts
open TaggedShorterSupergroups Filter
open Computability.VPVNP.BurstRAM PrivateRAM
open Tagged.WideControlJoin ProtocolStackContraction CoreBoard.PhysicalTerm
open scoped Classical BigOperators Topology Fin.CommRing

private def scatterWord {F : Type} [Field F] (b : Tagged.WideStack.Board F)
    (f : TaggedShorterScatter.Field (TaggedShorterGroups.capacity b.Group b.D b.halfBatch b.modules) b.D) : ℕ :=
  TaggedShorterScatter.contents (n := b.address) b.counts b.bound b.positive
    (by have := b.batch; omega) b.place f

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (hW : 0<v.W)
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "geometry" => typeMenu κ A v.W m k jobs ell hW (fun _=>short+ell)
local notation "menu" => (geometry).menu u δ ξ
local notation "roleCount" => copies k jobs
local notation "groupDir" x => stageDir (x).h v.W roleCount (2*roleCount)
  (show 2*roleCount≤2^(2*roleCount) from Nat.lt_two_pow_self.le)
local notation "portCount" x => 2^(superAddress v.W (2*roleCount) (x).h)
local notation "slotCountAt" x => purchaseSlots (x).h v.W k jobs ell

variable {Ex Se E H J Tail : Type} [Fintype Ex] [Fintype Se] [Fintype E] [Fintype H] [Fintype J] [Fintype Tail]
    {gate : Gate}

set_option maxHeartbeats 600000 in
omit [Fintype E] [Fintype H] [Fintype J] in
/-- The public cap and the original group price install the actual purchased compactors.
The native scatter fields, together with the unchanged public socket coordinates,
are sufficient at every private and chronological assignment of the terminal sum. -/
theorem printed_cut_receipt
    (prices : v.PhysicalCounts u A δ ξ m) (positive : 0≤κ)
    (x : WideParent κ A)
    (buy : ∀i : Fin (m+1),Purchased F menu x i (slotCountAt x)
      (purchaseCandidates x.h v.W k jobs (slotCountAt x) ((menu).height i x)
        (purchaseModules v.W u δ ξ menu x i)) (purchaseModules v.W u δ ξ menu x i) C)
    (groupsFit : GroupRoom v.W k jobs u δ ξ menu x)
    (metadata : ∀i : Fin (m+1),1+(menu).height i x+(menu).height i x≤(menu).payload i x)
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
    (pin : ∀j side,(anchor (j,side)).2=port side j.val)
    (cap : E→ℕ) (tail : ((Bool × ((e:E) × Fin (cap e))) ⊕ (H ⊕ J)) ≃ Tail)
    (t : Fin (m+1)) (base : ℕ)
    (room : base+(TaggedShorterGroups.capacity (Fin (groupDir x).groups) (slotCountAt x)
      (2^((menu).height t x-1)) (purchaseModules v.W u δ ξ menu x t) +
      2*(TaggedShorterGroups.capacity (Fin (groupDir x).groups) (slotCountAt x)
      (2^((menu).height t x-1)) (purchaseModules v.W u δ ξ menu x t)*2*slotCountAt x))≤gate.u)
    (width : (menu).height t x≤gate.W) (out : Memory gate.W) (one : 1<2^gate.W) :
    let installed := fun i : Fin (m+1) => v.printed_installed m ell short hW prices positive x i
      (buy i) groupsFit (metadata i) π b marks order size raw bits «rec» read R paid keep idRead widthRoom
      port anchor owner pin
    let bank := (installed t).bank
    let positions := Leaf.Pos (Leaf.banks installed)
    ∀ (_stored : ∀f,out (gate.addr (frozenRow base room f)).val=
        (scatterWord bank f : Word gate.W))
    (ext : Ex→Bool) (sel : Se→Bool)
    (z : ∀i,(Leaf.banks installed i).Slots) (y : PrivatePorts cap) (hist : H→Bool) (pbits : J→Bool),
    let same := (purchase_capacity (groupDir x).groups (slotCountAt x) (2^((menu).height t x-1))
      (purchaseModules v.W u δ ξ menu x t)).symm
    let readPin := frozenReadPin (Ex:=Ex) (Se:=Se) (P:=positions ⊕ Tail) (gate:=gate) (Fin (groupDir x).groups) (slotCountAt x) (2^((menu).height t x-1))
      (purchaseModules v.W u δ ξ menu x t) ((menu).height t x) ((menu).payload t x) base room width
      (fun q j => (Sum.inl ⟨t,q,j⟩ : positions ⊕ Tail))
    ((buy t).cut (Purchased.readAt same readPin)).closed
      (CalendarTerms.readPins (Equiv.sumCongr (Equiv.refl positions) tail) ext sel (gate.terminal out) (Leaf.write (Leaf.banks installed) cap z y hist pbits)) =
        bank.settings.close (z t) := by
  intro installed bank positions stored ext sel z y hist pbits same readPin
  let values := CalendarTerms.readPins (Equiv.sumCongr (Equiv.refl positions) tail) ext sel
    (gate.terminal out) (Leaf.write (Leaf.banks installed) cap z y hist pbits)
  exact ((buy t).cut_cast_closed same readPin values).trans
    (Leaf.frozen_cut_receipt (b := bank) (ins := installed) (cap := cap) (tail := tail) (t := t)
      (base := base) (room := room) (bits := width) (out := out) (one := one) (stored := stored)
      (ext := ext) (sel := sel) (z := z) (y := y) (h := hist) (p := pbits))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
