import OAI.Computability.BorderVNP.PackedRetainedControlReturn

/-! # Routing and packet arrays at a complete signed or field profile return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open VPVNP.VerifierNetwork VPVNP.BurstRAM RoutingISA GeometryFrameEncoding DiagonalResidueRAM
open Packing Packing.CellAddressCircuit Packing.RoutingOutputs ParseBatchSort

variable {Γ Z H : Type*} [Fintype Γ] [Fintype Z] [Fintype H] {s m n C d k b J A v o W : ℕ}

/-- Recover every section of the actual returned packet emitter from the
physical words at the end of startup and pin preparation. This also applies
when the caller has kept the complete prefix return instead of its inner
geometry-only trace. -/
theorem packet_image_of_words (B : Fields s m n C d k b (Z ⊕ Bool)) (keys : k≤b) (width : b≤W)
    (old : Fin J → Fin s) (ports : Fin A → Fin n) (controls : Fin v → Fin (2^b))
    (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o b)) (src : Frame Γ (Z ⊕ Bool)) (keep : Frame Γ H)
    (y : Γ → Bool) (constants : ∀ bit, src.eval y (.inr bit) = bit)
    (dest : ℕ) (result : Memory W)
    (returned : ∀ i, readings result (dest+i.val) = value (fun j =>
      (emitter B keys old ports (privateControls B old controls packet) src keep).eval y (i,j))) :
    Image B old ports (src.eval y) dest (readings result) ∧
      (∀ i : Fin (C+(J+C)), readings result (dest+m*3+RoutingOutputs.count m C J A+i.val) =
        value (fun j => (privateViews B old).eval (src.eval y) (i,j))) ∧
      (∀ i : Fin v, readings result (controlsBase dest m C J A+i.val) = (controls i).val) ∧
      ∀ i : Fin o, readings result (packetBase dest m C J A v+i.val) =
        value (fun j => packet.eval (Sum.elim (src.eval y) (keep.eval y)) (.inl (i,j))) := by
  let rest := atExtra (privateControls B old controls packet) (keep.eval y)
  have low (f : Fin b → Bool) : (word W (value f)).val=value f :=
    word_val W _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide) width))
  have raw (i : Fin (m*3+(RoutingOutputs.count m C J A+((C+(J+C))+(v+o))))) :
      result (dest+i.val) = word W (value (fun j => (full B keys old ports rest).eval (src.eval y) (.inl (i,j)))) := by
    apply Fin.ext
    rw [low]
    simpa only [emitter_eval,readings,rest] using returned i
  obtain ⟨image,extra⟩ := of_packed_words B keys width old ports rest (src.eval y) dest result raw
  have data (i : Fin ((C+(J+C))+(v+o))) :
      readings result (dest+m*3+RoutingOutputs.count m C J A+i.val) =
        value (fun j => (privateControls B old controls packet).eval (Sum.elim (src.eval y) (keep.eval y)) (.inl (i,j))) := by
    simpa only [rest,atExtra_eval,readings] using (congrArg Fin.val (extra i)).trans (low _)
  refine ⟨image,fun i => ?_,fun i => ?_,fun i => ?_⟩
  · simpa only [privateControls,GeometryOutput.prepend_first,lift_eval,Fin.val_castAdd] using data (i.castAdd (v+o))
  · have val := data (Fin.natAdd (C+(J+C)) (i.castAdd o))
    simp only [privateControls,GeometryOutput.prepend_rest,joinedControls_first,controlWords,
      Frame.initial_eval,constants,Fin.val_natAdd,Fin.val_castAdd,ParseBatchCounts.value_encode] at val
    have addr : controlsBase dest m C J A+i.val =
      dest+m*3+RoutingOutputs.count m C J A+(C+(J+C)+i.val) := by dsimp [controlsBase,bases,RoutingOutputs.count]; omega
    exact addr ▸ val
  · have val := data (Fin.natAdd (C+(J+C)) (Fin.natAdd v i))
    simp only [privateControls,GeometryOutput.prepend_rest,joinedControls_rest,Fin.val_natAdd] at val
    have addr : packetBase dest m C J A v+i.val =
      dest+m*3+RoutingOutputs.count m C J A+(C+(J+C)+(v+i.val)) := by
      dsimp [packetBase,controlsBase,bases,RoutingOutputs.count]; omega
    exact addr ▸ val

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
