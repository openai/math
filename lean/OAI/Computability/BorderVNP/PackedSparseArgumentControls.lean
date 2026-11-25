import OAI.Computability.BorderVNP.PackedHistoryRoutingControls

/-! # The sparse external-argument directory in the geometry output

The 28 existing control words are followed by nine physical controls for grouping
the live external fragments and preparing the compact cell arguments. The remaining
packet words begin at offset 37. All constant controls share the same two Boolean wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM ParseBatchSort
open Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport

variable {S Z : Type*} [Fintype S] [Fintype Z]
variable {s m n C d k w W J A o : ℕ}

/-- Read the original controls and the nine sparse-argument words from the same
successful native geometry return. No fresh runtime initialization of the extensions
is required. -/
theorem sparse_argument_controls (F : CellAddressCircuit.Fields s m n C d k w (S ⊕ Bool)) (hk : k ≤ w)
    (old : Fin J → Fin s) (ports : Fin A → Fin n) (rest : Frame (S ⊕ Bool) (Outputs o w))
    (source : Frame Z S) (controls : Fin 28 → Fin (2^w)) (extra : Fin 9 → Fin (2^w)) (input : Z → Bool)
    (origin : ℕ) (mem : Memory W) (width : w ≤ W) :
    let emit := controlEmitter F hk old ports (withControls extra rest) source controls
    (∀ i, readings mem (origin+i.val) = value (fun j => emit.eval input (i,j))) →
      (∀ i : Fin 28, readings mem (controlsBase origin m C J A+i.val) = (controls i).val) ∧
      (∀ i : Fin 9, readings mem (controlsBase origin m C J A+28+i.val) = (extra i).val) ∧
      ∀ i : Fin o, readings mem (controlsBase origin m C J A+37+i.val) =
        value (fun j => rest.eval ((withSewnFields source).eval input) (.inl (i,j))) := by
  intro emit out
  obtain ⟨_,raw,base⟩ := profile_controls F hk old ports (withControls extra rest) source controls input origin mem width out
  refine ⟨base,?_,?_⟩
  · intro i
    have part := raw (Fin.natAdd (C+(J+C)) (Fin.natAdd 28 (i.castAdd o)))
    simp only [withPrivateViews,GeometryOutput.prepend_rest,withControls_rest,withControls_first,
      Fin.val_natAdd,Fin.val_castAdd,control_value] at part
    have addr : controlsBase origin m C J A+28+i.val =
        origin+m*3+count m C J A+(C+(J+C)+(28+i.val)) := by dsimp [controlsBase,bases,count]; omega
    rw [addr]
    exact (congrArg Fin.val part).trans (word_val _ _ ((extra i).isLt.trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) width)))
  · intro i
    have part := raw (Fin.natAdd (C+(J+C)) (Fin.natAdd 28 (Fin.natAdd 9 i)))
    simp only [withPrivateViews,GeometryOutput.prepend_rest,withControls_rest,Fin.val_natAdd] at part
    have addr : controlsBase origin m C J A+37+i.val =
        origin+m*3+count m C J A+(C+(J+C)+(28+(9+i.val))) := by dsimp [controlsBase,bases,count]; omega
    rw [addr]
    exact (congrArg Fin.val part).trans (word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide) width)))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
