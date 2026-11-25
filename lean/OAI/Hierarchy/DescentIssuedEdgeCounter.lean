import OAI.Hierarchy.DescentPrivateEdgeCounter
import OAI.Hierarchy.DescentPrivateIssued

namespace OAI
/-! # The hardware increment of one authentic ordinary stage, including padded edge capacity -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentStageEdgeReceipt DescentKernelHistory DescentPacking DescentHistoryOrder DescentPrivateEdgeCounter
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D w hist z' D' : ℕ}
variable {a : Reached W G q ε S k i z D w hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {b : Reached n.result G q ε S k (i+1) z' D' w hist}
local notation "raw" => rawGraph he T c
local notation "input" => (BitDescription.scannedRows he T).state c
local notation "live" => (Fintype.card W.graph.Edge+10*Fintype.card (BitDescription.scannedRows he T).pairs)

private theorem sum_pad (f : ℕ→ℕ) {n cap : ℕ} (enough : n≤cap) (pad : ∀j,n≤j→j<cap→f j=0) :
    (∑i : Fin cap,f i.val)=∑i : Fin n,f i.val := by
  rw [Fin.sum_univ_eq_sum_range f,Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset (Finset.range_mono enough)
  intro j hjCap hjLive
  exact pad j (Nat.le_of_not_gt (fun lo=>hjLive (Finset.mem_range.mpr lo))) (Finset.mem_range.mp hjCap)

/-- Both sides use the same dense old/arm/supply ordinal. On padding only width matters. -/
theorem OrdinaryLink.counter_read (ticket : OrdinaryLink a he T c n b) (B : Banks)
    {bw cap : ℕ} (m : Memory bw) (src dst width : ℕ→ℕ)
    (space : Room B bw cap)
    (memory : Loaded B m (fun j : Fin cap=>src j=dst j) (fun j=>width j))
    (enough : live≤cap) (pad : ∀i,live≤ i→i<cap→width i=0)
    (src_read : ∀e,src (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=
      rawOwner he T c n input (originalId _) ((raw).src e))
    (dst_read : ∀e,dst (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=
      rawOwner he T c n input (originalId _) ((raw).dst e))
    (width_read : ∀e,width (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)= (raw).width e) :
    let out:=result B m (fun j : Fin cap=>src j=dst j) (fun j=>width j)
    (program B bw cap).Exec m out (cost B cap) ∧ out B.out=m B.oldTotal+(ordinaryFee ticket:Computability.VPVNP.BurstRAM.Word bw) := by
  refine ⟨run B m _ _ space memory,?_⟩
  rw [read B m _ _ space]
  congr 2
  calc
    _ = ∑i : Fin live,if src i=dst i then width i else 0 :=
      sum_pad (fun j : ℕ=>if src j=dst j then width j else 0) enough
        (fun j lo hi=>by simp [pad j lo hi])
    _ = ordinaryFee ticket := ticket.raw_row_fee src dst width src_read dst_read width_read

end
end Hierarchy.DescentSixParty.Chronology

end OAI
