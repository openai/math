import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.ContractionMemory
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Sequencing the native restored-roster pass with its dependent terminal writers -/
noncomputable section
namespace Hierarchy.TraceReceiverProgram
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open Diagonal
open scoped BigOperators Classical

/-- The terminal may choose the proof of its bound after it reads the real
restored S17 directory. Its code and its bound remain common to all embeddings. -/
theorem then_budget {W : ℕ} (p q : Procedure W) (input : Memory W) (mid final : Memory W→Prop)
    (startup total : ℕ)
    (restore : p.Spec (·=input) (fun _ z=>mid z) startup)
    (writer : ∀ z,mid z→∃ k,startup+k≤total ∧ q.Spec (·=z) (fun _ out=>final out) k) :
    (p.seq q).Spec (·=input) (fun _ z=>final z) total := by
  intro pp rr kk M pc reg pub exit rom data cfg m here hm
  have tail : q.Spec mid (fun _ out=>final out) (total-startup) := by
    intro a b c N loc registers pubMap stop installed words state z entry ok
    obtain ⟨k,small,run⟩:=writer z ok
    obtain ⟨t,paid,next,out,adv,finish,good⟩:=
      run N loc registers pubMap stop installed words state z entry rfl
    exact ⟨t,by omega,next,out,adv,finish,good⟩
  obtain ⟨t,paid,stop,out,adv,done,seed,restored,good⟩:=
    Procedure.Spec.seq restore tail (fun _ _ e=>e) M pc reg pub exit rom data cfg m here hm
  obtain ⟨k,room,_⟩:=writer seed restored
  exact ⟨t,by omega,stop,out,adv,done,good⟩

/-- The whole prefix copy and gather pin guard fit strictly below every T
workspace write, even including all the initially zero hidden scratch. -/
theorem input_window {w age p H : ℕ} (large : 7≤w) (lower : 4*w≤age^10)
    (pins : p≤2^w) (hidden : H≤2^w) : BitLayout.cellsBase p H≤TickWorkspace.base age 1 := by
  have room : 2^(w+1)≤TickWorkspace.stride age := by
    change 2^(w+1)≤(2^(age^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ] at room
  have pos : 2≤2^w:=Nat.pow_le_pow_right (by decide : 0<2) (show 1≤w by omega)
  change 2+p+H≤2*TickWorkspace.stride age
  omega

end Hierarchy.TraceReceiverProgram
end

end OAI
