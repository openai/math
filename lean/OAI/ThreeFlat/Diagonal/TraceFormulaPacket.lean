import OAI.ThreeFlat.Diagonal.TraceCompose
import OAI.ThreeFlat.Diagonal.TraceFetchCircuit

namespace OAI
/-! # Compiling a single Boolean formula to a transcript -/

namespace ThreeFlat.Diagonal.TracePair

open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

noncomputable def formulaPacket {σ : Type*} [Fintype σ] (e : Expr σ) : TraceCompose.Packet σ :=
  let f : Frame σ Unit := (Frame.initial id).step (fun _ => e)
  ⟨f.circuitSize (), f.circuit ()⟩

@[simp] theorem formulaPacket_eval {σ : Type*} [Fintype σ] (e : Expr σ) (x : σ → Bool) :
    (formulaPacket e).2.eval x = e.eval x := by
  have h : (Frame.initial id).eval x = x := funext fun _ => by simp
  simp [formulaPacket,h]

theorem formulaPacket_size_le {σ : Type*} [Fintype σ] (e : Expr σ) :
    (formulaPacket e).1 ≤ 4*e.size := by
  let f : Frame σ Unit := (Frame.initial id).step (fun _ => e)
  apply (f.circuitSize_le ()).trans
  apply Nat.mul_le_mul_left
  simpa [f] using (Frame.step_size_le (Frame.initial (id : σ → σ)) (fun _ : Unit => e) e.size
    (fun _ => le_rfl))

end ThreeFlat.Diagonal.TracePair

end OAI
