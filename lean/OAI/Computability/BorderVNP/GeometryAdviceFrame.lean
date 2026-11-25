import OAI.Computability.BorderVNP.GeometryAdvicePipeline
import OAI.Computability.BorderVNP.GeometryAdviceRate

/-! # Physical evaluation of every output of the Section 6 geometry frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryFrameEncoding

variable {σ : Type*} [Fintype σ] {w u o b : ℕ}

set_option maxRecDepth 4000 in
/-- Starting with the advised bits installed on the actual processor tapes, the fixed
native program accepts exactly the valid assignments of the original shared Boolean
frame. The accepting trace is unique. Every output word is the value of the original
MSB-first wires and the complete runtime obeys the charged serialization bound. -/
theorem frame_execute (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : BroadcastFrame) (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (frame : VerifierNetwork.Frame σ (Outputs o b)) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool)
    (x : Fin u → Bool) (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val) :
    let t := compile frame pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
      ((∃ es bits, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some es) ↔
        frame.eval input (.inr ()) = true) ∧
      (frame.eval input (.inr ()) = true →
        ∃ es z mz, Runs pub mac reconstruct s m es z mz ∧
          traceCost es ≤ GeometryAdviceRate.ticks t.size u o b w ∧
          (∀ i : Fin o, mz (l.dest+i) = word w (ParseBatchSort.value fun j => frame.eval input (.inl (i,j)))) ∧
          (∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
            fs = es ∧ bits = es.map TeamRAM.Event.choices)) := by
  intro t input layout h
  have eq : GeometryOutput.validBit t (Sum.elim x Fin.elim0) = frame.eval input (.inr ()) :=
    GeometryOutput.compiled_valid frame pins _
  have valid (hv : frame.eval input (.inr ()) = true) :=
    reconstruct_runs pub mac s m f a L P l base start src t x fit space layout h (eq.trans hv)
  constructor
  · constructor
    · rintro ⟨es,bits,accepted⟩
      by_contra bad
      obtain ⟨⟨z,mz,r⟩,_⟩ := (Code.execute_iff_runs (by decide : reconstruct.withoutAccept = true)).mp accepted
      exact reconstruct_invalid pub mac s m f a L P l base start src t x fit space layout h
        (eq.trans (Bool.eq_false_iff.mpr bad)) r
    · intro hv
      obtain ⟨es,z,mz,r,_,_,_⟩ := valid hv
      exact ⟨es,_,r.execute⟩
  · intro hv
    obtain ⟨es,z,mz,r,charge,choice,out⟩ := valid hv
    refine ⟨es,z,mz,r,?_,?_,?_⟩
    · simpa only [cost,GeometryOutput.stagedTicks,GeometryOutput.packetCount,
        GeometryAdviceRate.ticks,GeometryAdviceRate.packetWords,Nat.add_assoc] using charge
    · intro i
      rw [out.words i]
      exact congrArg (word w) (congrArg ParseBatchSort.value (funext fun j => bit_eval frame pins i j _))
    · intro bits fs
      rw [Code.execute_iff_runs (by decide : reconstruct.withoutAccept = true)]
      constructor
      · rintro ⟨⟨_,_,other⟩,order⟩
        obtain ⟨rfl,_,_⟩ := unique_returns (c := reconstruct) (by decide) r other
          (tail := fs.flatMap TeamRAM.Event.choices) (tail' := []) (by rw [choice]; simp)
        exact ⟨rfl,order.symm⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨⟨z,mz,r⟩,rfl⟩

end GeometryAdvice

end BorderVNP
end Computability
end OAI
