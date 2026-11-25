import OAI.Computability.BorderVNP.PackedHistoryGeometryExecute
import OAI.Computability.BorderVNP.PackedRoutingCompiled

/-! # Routing and delivery arrays at the end of a native history evaluation

The table interpreter reads the reserved profile, computes the history
state once and runs the routing fields on those same wires. Its actual
output words therefore give the physical image at the allocated base.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA GeometryFrameEncoding VerifierNetwork Packing
open DiagonalResidueRAM RoutingOutputs CellAddressCircuit ParseBatchSort

variable {X Y Z V : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype V]
    {active reserve s m n C d k w J A o W : ℕ}

/-- Shared field and row computations appended once to the final history state. -/
noncomputable def terminalEmitter (F : Fields s m n C d k w Z) (hk : k ≤ w)
    (old : Fin J → Fin s) (ports : Fin A → Fin n) (rest : VerifierNetwork.Frame Z (Outputs o w))
    (source : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ V) Z) :=
  ((full F hk old ports rest).select Sum.inl).subst source

/-- A returning concrete geometry evaluation produces all physically addressed
routing outputs and preserves the ordinary frame and lower live inputs. -/
theorem GeometryReturn.routing_image
    (history : VerifierNetwork.Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active ≤ reserve)
    (F : Fields s m n C d k w Z) (hk : k ≤ w) (hw : w ≤ W)
    (old : Fin J → Fin s) (ports : Fin A → Fin n) (rest : VerifierNetwork.Frame Z (Outputs o w))
    (source : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ V) Z)
    (x : X → Bool) (word : Fin reserve → Bool)
    {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {bank after : Bank W} {mem result : Memory W}
    {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)} :
    let emit := terminalEmitter F hk old ports rest source
    let v := fun j => history.eval (Sum.elim x (readProfile order fit word)) (.inl j)
    let y := source.eval (Sum.elim (Sum.elim x word) v)
    GeometryReturn pub mac bank mem fresh dest clock (emittedWords history order fit emit x word) es after result →
      Runs pub mac GeometryAdvice.reconstruct bank mem es after result ∧ traceCost es ≤ clock ∧
      Image F old ports y dest (readings result) ∧
      (∀ i : Fin o, result (dest+m*3+RoutingOutputs.count m C J A+i.val) =
        DiagonalResidueRAM.word W (value fun j => rest.eval y (.inl (i,j)))) ∧
      ∀ a < fresh, result a = mem a := by
  intro emit v y run
  have raw (i : Fin (m*3+(RoutingOutputs.count m C J A+o))) : result (dest+i.val) =
      DiagonalResidueRAM.word W (value fun j => (full F hk old ports rest).eval y (.inl (i,j))) := by
    apply Fin.ext
    rw [word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hw))]
    simpa only [emit,emittedWords,terminalEmitter,VerifierNetwork.Frame.subst_eval,VerifierNetwork.Frame.select_eval,
      v,y,readings] using run.words i
  obtain ⟨image,other⟩ := of_packed_words F hk hw old ports rest y dest result raw
  exact ⟨run.run,run.time,image,other,run.preserved⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
