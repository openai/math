import OAI.Computability.BorderVNP.PackedHistoryRoutingImage
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # The profile evaluator publishes the real routing image and secondary controls

The emitter uses the sewn state pins and the two shared constant wires. The cable, slot
and owned-cell arrays precede the 28 control words. Neither their literal values nor
addresses derived from the final gate count alter the length of the native program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM ParseBatchSort
open Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport
open BinPackingGames.Foundations.Complexity.CookLevin
open private spliceCore from OAI.Computability.VPVNP.VerifierMachineSplice
open private compile_gates subst_gates prepend_gates from OAI.Computability.BorderVNP.PackedRoutingControls

variable {X Y V S Z : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype S] [Fintype Z]
variable {s m n c d k w W j a o active reserve : ℕ}
variable (F : CellAddressCircuit.Fields s m n c d k w (S ⊕ Bool)) (hk : k ≤ w)
variable (old : Fin j → Fin s) (ports : Fin a → Fin n) (rest : VerifierNetwork.Frame (S ⊕ Bool) (Outputs o w))

/-- Complete terminal word array over the real selected history pins. -/
noncomputable def controlEmitter (source : VerifierNetwork.Frame Z S) (controls : Fin 28 → Fin (2^w)) :=
  (routingEmitter F hk old ports (withPrivateViews F old (withControls controls rest))).subst (withSewnFields source)

/-- The actual profile decoder's output words supply all the sparse rows and the same
addressed secondary control vector, including the local report buffer capacity at slot 8. -/
theorem profile_controls (source : VerifierNetwork.Frame Z S) (controls : Fin 28 → Fin (2^w)) (input : Z → Bool)
    (origin : ℕ) (mem : Memory W) (width : w ≤ W)
    (out : ∀ i, readings mem (origin+i.val) = value (fun b => (controlEmitter F hk old ports rest source controls).eval input (i,b))) :
    let y := (withSewnFields source).eval input
    Image F old ports y origin (readings mem) ∧
    (∀ i : Fin ((c+(j+c))+(28+o)), mem (origin+m*3+RoutingOutputs.count m c j a+i.val) =
      DiagonalResidueRAM.word W (value fun b => (withPrivateViews F old (withControls controls rest)).eval y (.inl (i,b)))) ∧
    ∀ i : Fin 28, readings mem (controlsBase origin m c j a+i.val) = (controls i).val := by
  intro y
  have raw (i : Fin (m*3+(RoutingOutputs.count m c j a+((c+(j+c))+(28+o))))) : mem (origin+i.val) =
      DiagonalResidueRAM.word W (value fun b => (full F hk old ports (withPrivateViews F old (withControls controls rest))).eval y (.inl (i,b))) := by
    apply Fin.ext
    rw [word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) width))]
    simpa only [controlEmitter,routingEmitter,Frame.subst_eval,Frame.select_eval,y,readings] using out i
  obtain ⟨image,fields⟩ := of_packed_words F hk width old ports _ y origin mem raw
  exact ⟨image,fields,controls_at F source input old controls rest origin mem width fields⟩

/-- Choosing the actual secondary control addresses after computing the program size on
a dummy vector is exact, even after the zero-padding test and original history guard. -/
theorem geometryTable_size_controls (history : VerifierNetwork.Frame (X ⊕ Y) (V ⊕ Unit))
    (order : Y ≃ Fin active) (fit : active ≤ reserve) (source : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ V) S)
    (x : X → Bool) (left right : Fin 28 → Fin (2^w)) :
    (geometryTable history order fit (controlEmitter F hk old ports rest source left) x).size =
      (geometryTable history order fit (controlEmitter F hk old ports rest source right) x).size := by
  have same : (controlEmitter F hk old ports rest source left).core.fragment.gates =
      (controlEmitter F hk old ports rest source right).core.fragment.gates := by
    apply subst_gates
    change (full F hk old ports (withPrivateViews F old (withControls left rest))).core.fragment.gates =
      (full F hk old ports (withPrivateViews F old (withControls right rest))).core.fragment.gates
    apply prepend_gates
    apply prepend_gates
    apply prepend_gates
    rfl
  apply compile_gates
  apply subst_gates
  simp only [Crossing.parallelFrame,JointScalar.parallel,Frame.select,Frame.withInput,Frame.subst,
    spliceCore,CircuitBatch.Fragment.append,Frame.initial,CircuitBatch.Frame.initial,CircuitBatch.Fragment.empty,
    List.map_nil,List.append_nil,same]

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
