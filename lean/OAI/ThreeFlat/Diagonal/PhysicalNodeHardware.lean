import OAI.ThreeFlat.Diagonal.PhysicalNodeChargeWork
import OAI.ThreeFlat.Diagonal.NavigationCountedLoop

namespace OAI
/-! # Native node-row publisher hardware independent of the physical bank addresses -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.HistoryStageBody.Physical
open scoped BigOperators Classical
noncomputable section
variable {W : ℕ}

private def hardwareBanks : Banks := ⟨0,0,0,0,0,0,0,0⟩

def nodeSize (cc hc mc : ℕ) :=
  resources (NavigationNodeRows.procedure (W:=1) hardwareBanks cc hc mc)

theorem node_size (b : Banks) (c h m : ℕ) :
    resources (NavigationNodeRows.procedure (W:=W) b c h m)=nodeSize c h m := by
  simp only [nodeSize,NavigationNodeRows.procedure,resources_seq,resources_scan,HeaderScan.binds_closed,
    charge_work b hardwareBanks]
  all_goals rfl

/-- A fixed cap bounds the number of labels, registers and public cells of the
node scanner, uniformly in the register placement and all histogram choices. -/
def nodeHardwareBound (cap : ℕ) :=
  ∑ x : Fin (cap+1)×Fin (cap+1)×Fin (cap+1),nodeSize x.1.val x.2.1.val x.2.2.val

private theorem curve_le_sum {ι : Type*} [Fintype ι] (cost : ι→ℕ) (x : ι) :
    cost x≤∑y : ι,cost y :=
  Finset.single_le_sum (s:=Finset.univ) (f:=cost) (fun y _=>Nat.zero_le (cost y)) (Finset.mem_univ x)

theorem node_hardware_le {cap c h m : ℕ} (b : Banks) (hc : c≤cap) (hh : h≤cap) (hm : m≤cap) :
    resources (NavigationNodeRows.procedure (W:=W) b c h m)≤nodeHardwareBound cap := by
  rw [node_size]
  let x : Fin (cap+1)×Fin (cap+1)×Fin (cap+1) :=
    ⟨⟨c,Nat.lt_succ_of_le hc⟩,⟨h,Nat.lt_succ_of_le hh⟩,⟨m,Nat.lt_succ_of_le hm⟩⟩
  let cost (y : Fin (cap+1)×Fin (cap+1)×Fin (cap+1)) :=
    nodeSize y.1.val y.2.1.val y.2.2.val
  change cost x ≤ ∑ y, cost y
  exact curve_le_sum cost x

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
