import OAI.Hierarchy.ProbeStagePublicGroups

namespace OAI
/-! # The three native stage banks and their allocation record -/

noncomputable section
namespace Hierarchy.ProtocolRAMPurchaseAllocation
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProbeStage

structure CT where
  group : Bank
  input : Bank
  output : Bank

structure Layout where
  start : ℕ
  rows : ℕ
  groups : ℕ
  sockets : ℕ
  degree : ℕ
  height : ℕ
  first : ℕ

namespace Layout

structure CTLoaded (L : Layout) (ct : CT) {G : Type*} (p : Tiles (Fin L.rows) G L.sockets)
    (e : G ↪ Fin L.groups) {w : ℕ} (mem : Memory w) : Prop where
  group : Native.Resident ct.group mem (fun r => (e (p.group r)).val)
  input : Native.Resident ct.input mem (fun r => (p.input r).val)
  output : Native.Resident ct.output mem (fun r => (p.output r).val)

end Layout
end Hierarchy.ProtocolRAMPurchaseAllocation

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native ProtocolRAMPurchaseAllocation
open scoped Fin.CommRing Classical
variable {z d w : ℕ}

def banks (t : StageAt z d) : CT :=
  ⟨stageBank z d (stageNumber t) 0,stageBank z d (stageNumber t) 1,stageBank z d (stageNumber t) 2⟩

def allocation (t : StageAt z d) (start D depth first : ℕ) : Layout :=
  ⟨start,2^z,Fintype.card (stageAt z d t).Group,(stageAt z d t).span,D,depth,first⟩

/-- The genuine published stage bank gives the same fixed group numbering on every permutation. -/
theorem resident_numbered (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) (start D depth first : ℕ)
    (input : Memory (wordBits z d copies)) (done : After (d:=d) π input (rounds d)) :
    (allocation t start D depth first).CTLoaded (banks t) (advisedStage z d π t)
      (groupNumber t).toEmbedding (images z d input (rounds d)) := by
  obtain ⟨group,source,target⟩ := stage_numbered π t input done
  exact ⟨group,source,target⟩

end Hierarchy.ProtocolRAM.PurchaseCT
end

end OAI
