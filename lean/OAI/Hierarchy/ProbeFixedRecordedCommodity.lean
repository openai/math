import OAI.Hierarchy.ProbeFixedWideSignedCore
import OAI.Hierarchy.ProtocolRAMStripParentFlag

namespace OAI
/-! # Signed parent flags at the terminal read of each original commodity occurrence -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StockCommit StripChart StripDirectory BoughtSockets CatalogueRows CoreRoute
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "B" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "cat" => (P).catalogue
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => wordBits h D Native.copies
local notation "roleCount" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "head" => (P).routes.directory.header h D k v.sampler.degree v.depth
local notation "occ" => StripChart.header F B

private theorem inner_parent_date (c : Mesh) {p a j t : ℕ}
    (scheduled : Event.attempt (.inner p a j t)∈events c) :
    p < c.inject+c.cool ∧ a < c.outerFuel := by
  obtain ⟨phase,hp,visit⟩:=List.mem_flatMap.mp scheduled
  rcases List.mem_append.mp visit with attempts|feed
  · obtain ⟨trial,ha,next⟩:=List.mem_flatMap.mp attempts
    rcases List.mem_cons.mp next with outer|reserve
    · cases outer
    · obtain ⟨slice,_,next⟩:=List.mem_flatMap.mp reserve
      rcases List.mem_append.mp next with repairs|feed
      · obtain ⟨step,_,hit⟩:=List.mem_map.mp repairs
        cases hit
        exact ⟨List.mem_range.mp hp,List.mem_range.mp ha⟩
      · simp at feed
  · simp at feed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Every commodity uses its own flat occurrence in the published parent
purchase, including a zero flag when that candidate was dormant. -/
theorem recorded_commodity_id (m : Memory w) (a : Attempt) (dated : Event.attempt a∈events v.mesh)
    (i : Fin roleCount) (row : Fin (occ a).count) (room : (cat).rows<2^w)
    (directory : (head).Loaded m) (ports : (occ a).Loaded m) :
    (StripChart.id F B cat a i).eval m (row.val:Word w)=
      ((cat).commonID (StripChart.edge F B (cat).rows a i)).eval m (row.val:Word w) := by
  cases a with
  | outer p t =>
    exact outer_common F B v.mesh cat (P).routes p t i m m _ _ _ room rfl
  | inner p t j u =>
    let a:=Attempt.inner p t j u
    obtain ⟨hp,ht⟩:=inner_parent_date v.mesh dated
    let phase : Fin (v.mesh.inject+v.mesh.cool):=⟨p,hp⟩
    let trial : Fin v.mesh.outerFuel:=⟨t,ht⟩
    let candidate : Fin (head).ports:=((occ a).enum.symm row).1
    have ball : (occ a).ballTerm.eval m (row.val:Word w)=(candidate.val:Word w) := by
      have read:=(StripDirectory.header_pair (occ a) m ports ((occ a).enum.symm row).1 ((occ a).enum.symm row).2).1
      have inverse : (occ a).enum ⟨((occ a).enum.symm row).1,((occ a).enum.symm row).2⟩=row := (occ a).enum.apply_symm_apply row
      rw [inverse] at read
      exact read
    have count : (head).count=(cat).boughtRows := rfl
    have indexFit : (head).rows*(head).ports≤2^w := by
      change (head).count≤_
      rw [count]
      exact (Nat.le_add_left ..).trans room.le
    have dateRoom : (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel≤2^w :=
      (Nat.le_mul_of_pos_right (head).rows (Nat.zero_lt_of_lt candidate.isLt)).trans indexFit
    have pastRow : Fin (head).rows:=finProdFinEquiv (phase,trial)
    have candidateRoom : (head).ports≤2^w :=
      (Nat.le_mul_of_pos_left (head).ports (Nat.zero_lt_of_lt pastRow.isLt)).trans indexFit
    have origin:=v.sourcePair_uses h width (WideMemory.K h v.W)
      (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
      (WideMemory.R v.sampler h v.W k) (CoreCatalogue.pointBits h v.W) 0 (v.wideJoint h width)
      0 (CatalystArchive.TerminalLayout.settlement 0 ⟨0,0⟩) 0 0 0 ⟨0,0⟩ phase trial
    apply inner_common F B v.mesh cat (P).routes phase trial j u i m m _ _ _ candidate count room rfl ball
    apply parent_flag F (withPorts B v.mesh cat (P).routes) v.mesh cat (P).routes phase trial j u
      m m _ candidate dateRoom candidateRoom directory rfl _ rfl ball rfl
    exact origin.2.1

/-- At the actual signed origin the core and economic boot load the two tables.
Any subsequent output preserving those low addresses reads those same words. -/
theorem recorded_commodity_id_below (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (wordRoom : (A).endAddress v.mesh<2^w) (m : Memory w)
    (same : ∀x<(A).first,m x=v.wideSignedMidAt h width size stock M π o raw x)
    (a : Attempt) (dated : Event.attempt a∈events v.mesh)
    (i : Fin roleCount) (row : Fin (occ a).count) (room : (cat).rows<2^w) :
    (StripChart.id F B cat a i).eval m (row.val:Word w)=
      ((cat).commonID (StripChart.edge F B (cat).rows a i)).eval m (row.val:Word w) := by
  obtain ⟨_,_,seen,econ,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock M π o raw wordRoom
  have first : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
  have core := (v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have snap:=seen.frame (core.trans_lt (first.trans_lt wordRoom)) (fun x hx=>same x (hx.trans_le core))
  have portsLow:=((E).ports.end_le 0).trans (v.catalyst_ports_le_first P h width)
  have port:= (econ.ports 0).frame (fun x _ hx=>same x (hx.trans_le portsLow))
  apply v.recorded_commodity_id h width m a dated i row room snap.board.rom.outer
  exact (v.catalyst_header P h width a) ▸ port

theorem wide_recorded_commodity_id_at (size : ℕ) (extent : (A).endAddress v.mesh ≤ size)
    (stock : Bank) (M : ℕ) (π : Equiv.Perm (Fin (2^h))) (o : Orders h D k) (raw : Boot.Tape h D)
    (wordRoom : (A).endAddress v.mesh<2^w)
    (live : Calendar.mounted (v.wideSignedChart h width stock) (events v.mesh)
      (v.wideSignedMidAt h width size stock M π o raw))
    (a : Attempt) (dated : Event.attempt a∈events v.mesh)
    (i : Fin roleCount) (row : Fin (occ a).count) (room : (cat).rows<2^w) :
    let m:=v.wideSignedCheckoutAt h width size stock M π o raw
    (StripChart.id F B cat a i).eval m (row.val:Word w)=
      ((cat).commonID (StripChart.edge F B (cat).rows a i)).eval m (row.val:Word w) :=
  v.recorded_commodity_id_below h width size extent stock M π o raw wordRoom _
    (fun x hx=>v.wide_signed_checkout_below h width stock M π o raw size x hx live) a dated i row room

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
