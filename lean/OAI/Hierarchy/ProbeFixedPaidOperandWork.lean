import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProtocolRAMStripForestHeaderWork

namespace OAI
/-! # Height-independent native work of every paid strip operand -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage CoreBoard AdaptiveProbe StripDirectory StripChart CatalogueRows BoughtSockets PurchaseFrozen
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private def roleCount (N depth k : ℕ) := max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))
private def linkCount (N depth k : ℕ) := max (Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount N) k))
  (Fintype.card (Strip.TreeLink (ChainStrip.edgeCount depth) k))

private def primaryWork :=
  let d := 2^v.W
  let n := 2*rounds d+1
  let x := 56+8*ReportSockets.copies k v.wideJobs
  let y := purchasedColumnWork d k v.wideJobs
  let t := chainWork n v.sampler.degree (n*(2*k)) y
  (2*(x+(x+7)+0+6)+3) + (2*(y+t+4+6)+3) + 1

/-- One cost bound for every attempt, permutation height, width, and settlement address. -/
def paidOperandWork : ℕ :=
  let N := 2*rounds (2^v.W)+1
  let D := roleCount N v.depth k
  let L := linkCount N v.depth k
  let u := primaryWork v
  let flag := wordWork (2^v.W) k v.wideJobs
  (1+D*(7+(4*(u*8)+22)+2)+1+1) + finalTreeWork D L u flag

variable (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "b" => (P).catalogue
local notation "s" => v.located (v.seed P h width) P width
local notation "bs" => withPorts s v.mesh b (P).routes
local notation "N" => Stages h (2^v.W)
local notation "H" => v.publicHeader P h width

set_option cleanup.letToHave false in
set_option maxHeartbeats 700000 in
private theorem wide_primary_work (a : Attempt) : DatePortWork s v.mesh b (P).routes (primaryWork v) a := by
  let top:=2*rounds (2^v.W)+1
  let x:=56+8*ReportSockets.copies k v.wideJobs
  let y:=purchasedColumnWork (2^v.W) k v.wideJobs
  let t:=chainWork top v.sampler.degree (top*(2*k)) y
  let payload:=2*(x+(x+7)+0+6)+3
  let purchase:=2*(y+t+4+6)+3
  have sam : (s).sampler=v.sampler := rfl
  have maxCost : primaryWork v=payload+purchase+1 := rfl
  cases a with
  | outer phase trial =>
    intro r
    have est := payloadWork v.sampler b (P).routes.core (P).routes.column (P).routes.directory.remapBase
      (P).routes.directory.sitesBase (P).routes.directory.superBase (P).routes.oldGroups (P).routes.bins
      (P).routes.height h v.W k v.wideJobs ((Fintype.equivFin _) r)
    have actual : ((payloadPortsAt s v.mesh (P).routes).primary b r).work ≤ payload := by
      unfold payloadPortsAt
      rw [sam]
      simpa only [payloadEdge,Equiv.symm_apply_apply,payload,x,wideJobs] using est
    rw [maxCost]
    exact actual.trans ((Nat.le_add_right payload purchase).trans (Nat.le_add_right _ 1))
  | inner phase trial j u =>
    intro r
    have est := purchaseWork (P).routes.directory ((s).outer phase trial).market.shelf v.sampler b
      (P).routes.core (P).routes.column ((s).stratumHeader phase trial) (P).routes.oldGroups
      (P).routes.bins (P).routes.height h v.W k v.depth (birth v.mesh phase trial) ((Fintype.equivFin _) r)
    have actual : ((boughtPortsAt s v.mesh b (P).routes phase trial).primary b r).work ≤
        2*(y+chainWork N v.sampler.degree (count h (2^v.W) k) y+4+6)+3 := by
      unfold boughtPortsAt
      rw [sam]
      simpa only [purchaseEdge,Equiv.symm_apply_apply,y,wideJobs] using est
    have stages : N=top := template_length ..
    rw [stages,count_eq] at actual
    rw [maxCost]
    exact actual.trans ((Nat.le_add_left purchase payload).trans (Nat.le_add_right _ 1))

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
/-- The paid label, broadcast edge, source row, mask, and mate have uniformly bounded
work even when the locations and candidate rows move with the permutation height. -/
theorem wide_paid_operand_work (r : ℕ) (routes : RouteSettlement.Banks) (src tab dst : ℕ)
    (owners : Bank) (a : Attempt) :
    let stamp := v.stamp P h width r routes src tab dst owners a
    let tree := v.nativeTrees P h width a
    stamp.edge.work ≤ v.paidOperandWork ∧ tree.edge.work ≤ v.paidOperandWork ∧
      tree.sourceRow.work ≤ v.paidOperandWork ∧ ∀ mask mate, tree.catalystMate = some (mask,mate) →
        mask.work ≤ v.paidOperandWork ∧ mate.work ≤ v.paidOperandWork := by
  let u := primaryWork v
  let flags := wordWork (2^v.W) k v.wideJobs
  let top := 2*rounds (2^v.W)+1
  let D := roleCount N v.depth k
  let L := linkCount top v.depth k
  have stages : N = top := template_length ..
  have roles : D = roleCount top v.depth k := congrArg (fun n => roleCount n v.depth k) stages
  have links : linkCount N v.depth k = L := congrArg (fun n => linkCount n v.depth k) stages
  have one : 1 ≤ u := Nat.le_add_left 1 _
  have ports := v.wide_primary_work h width a
  have tag (i : Fin D) : (StripChart.id F (v.nativeBoards P h width) b a i).work ≤ 4*(u*8)+22 := by
    apply id_work_of_raw (v.nativeBoards P h width) b F a u i
    have reading : rawEdge (v.nativeBoards P h width) (b).rows a i=rawEdge bs (b).rows a i := by
      cases a <;> rfl
    rw [reading]
    exact raw_port_work s v.mesh b (P).routes a u one ports i
  let head := StripChart.header F (v.nativeBoards P h width) a
  have choose := choose_work_bound D 0 (4*(u*8)+22) _ head.fieldTerm tag
  have stamp : (v.stamp P h width r routes src tab dst owners a).edge.work ≤ 1+D*(7+(4*(u*8)+22)+2)+1+1 :=
    Nat.add_le_add_right (Nat.add_le_add_right choose 1) 1
  have original := (P).routes.directory.source_work v.sampler h v.W k v.depth (P).routes.oldGroups (P).routes.bins (P).routes.height
  have flag : (b).bought.flag.work ≤ flags := original.2.2.2.1
  let mountedHeader := StripChart.header F (v.mounted (v.seed P h width) P width) a
  have all := final_tree_work_at_header (z:=h) (W:=v.W) (k:=k) (depth:=v.depth)
    s v.mesh b (P).routes F mountedHeader (H).payloadTree.base a u flags L one flag
    ((Nat.le_max_left ..).trans_eq links) ((Nat.le_max_right ..).trans_eq links) ports
  have label_le : 1+D*(7+(4*(u*8)+22)+2)+1+1 ≤ v.paidOperandWork := by
    rw [roles]; exact Nat.le_add_right ..
  have tree_le : finalTreeWork D L u flags ≤ v.paidOperandWork := by
    rw [roles]; exact Nat.le_add_left ..
  obtain ⟨edge, row, mates⟩ := all
  refine ⟨stamp.trans label_le, edge.trans tree_le, row.trans tree_le, ?_⟩
  intro mask mate equal
  obtain ⟨left,right⟩ := mates mask mate equal
  exact ⟨left.trans tree_le,right.trans tree_le⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
