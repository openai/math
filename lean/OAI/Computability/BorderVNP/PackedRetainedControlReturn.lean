import OAI.Computability.BorderVNP.PackedTerminalRetainedReturn
import OAI.Computability.BorderVNP.PackedHistoryRoutingControls

/-! # Physical length-only controls of the retained packet emitter

The actual geometry decoder returns all control words at their numbered
positions before the packet. Changing the values of these controls leaves
the size of the serialized gate table fixed even when an additional public
history is required for the private packet.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM RoutingISA GeometryFrameEncoding DiagonalResidueRAM
open Packing Packing.CellAddressCircuit Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport
open BinPackingGames.Foundations.Complexity.CookLevin
open private spliceCore from OAI.Computability.VPVNP.VerifierMachineSplice
open private compile_gates subst_gates prepend_gates from OAI.Computability.BorderVNP.PackedRoutingControls

variable {X Y V Z H : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype Z] [Fintype H]
variable {s m n C d k w J P o W active reserve v : ℕ}
variable (B : Fields s m n C d k w (Z ⊕ Bool)) (hk : k≤w) (old : Fin J → Fin s) (ports : Fin P → Fin n)
    (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w)) (src : Frame ((X ⊕ Fin reserve) ⊕ V) Z)
    (keep : Frame ((X ⊕ Fin reserve) ⊕ V) H)
    (hist : Frame (X ⊕ Y) (V ⊕ Unit)) (ord : Y ≃ Fin active) (fit : active≤reserve) (x : X → Bool)

local notation3 "emit" ctrl => emitter B hk old ports (privateControls B old ctrl packet) (withSewnFields src) keep

/-- Arbitrary shared terminal staging can forward the two constant wires.
The stored word uses those actual wire values at the caller's branch. -/
theorem controls_return_of_pins (sewn : Frame ((X ⊕ Fin reserve) ⊕ V) (Z ⊕ Bool))
    (controls : Fin v → Fin (2^w)) (word : Fin reserve → Bool) (hw : w≤W)
    (constants : ∀ b, sewn.eval (branch hist ord fit x word) (.inr b) = b)
    {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {start after : Bank W} {mem result : Memory W}
    {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}
    (run : GeometryReturn pub mac start mem fresh dest clock (emittedWords hist ord fit
      (emitter B hk old ports (privateControls B old controls packet) sewn keep) x word) es after result) :
    ∀ i : Fin v, readings result (controlsBase dest m C J P+i.val) = (controls i).val := by
  let y := branch hist ord fit x word
  obtain ⟨_,raw⟩ := routing_return B hk old ports (privateControls B old controls packet) sewn keep
    hist ord fit x word hw run
  intro i
  have atWord := raw (Fin.natAdd (C+(J+C)) (i.castAdd o))
  simp only [privateControls,GeometryOutput.prepend_rest,joinedControls_first,controlWords,Frame.initial_eval,
    constants,Fin.val_natAdd,Fin.val_castAdd,ParseBatchCounts.value_encode] at atWord
  have addr : controlsBase dest m C J P+i.val = dest+m*3+RoutingOutputs.count m C J P+(C+(J+C)+i.val) := by
    dsimp only [controlsBase,bases,RoutingOutputs.count]; omega
  rw [addr]
  exact (congrArg Fin.val atWord).trans (word_val _ _ ((controls i).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) hw)))

/-- All controls read by the task, sparse fragment, and report stages come
from the same retained public execution as the packet and cable arrays. -/
theorem controls_return (controls : Fin v → Fin (2^w)) (word : Fin reserve → Bool) (hw : w≤W)
    {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {start after : Bank W} {mem result : Memory W}
    {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}
    (run : GeometryReturn pub mac start mem fresh dest clock
      (emittedWords hist ord fit (emit controls) x word) es after result) :
    ∀ i : Fin v, readings result (controlsBase dest m C J P+i.val) = (controls i).val := by
  let y := branch hist ord fit x word
  obtain ⟨_,raw⟩ := routing_return B hk old ports (privateControls B old controls packet) (withSewnFields src) keep
    hist ord fit x word hw run
  apply controls_at B src y old controls (atExtra packet (keep.eval y)) dest result hw
  intro i
  simpa only [privateControls_eval] using raw i

/-- Absolute task addresses may be computed using an all-zero provisional
control vector and then embedded at the actual values. The compiled native
gate count, hence the geometry allocation, agrees exactly. -/
theorem geometryTable_size_controlWords (sewn : Frame ((X ⊕ Fin reserve) ⊕ V) (Z ⊕ Bool)) (a b : Fin v → Fin (2^w)) :
    let rows := fun ctrl => emitter B hk old ports (privateControls B old ctrl packet) sewn keep
    (geometryTable hist ord fit (rows a) x).size=(geometryTable hist ord fit (rows b) x).size := by
  intro rows
  have same : (rows a).core.fragment.gates=(rows b).core.fragment.gates := by
    apply subst_gates
    change (GeometryOutput.prepend (lift (CableTriples.frame B hk le_rfl))
      (GeometryOutput.prepend (lift (tail B hk old ports)) (privateControls B old a packet))).core.fragment.gates = _
    apply prepend_gates
    apply prepend_gates
    apply prepend_gates
    rfl
  apply compile_gates
  apply subst_gates
  simp only [Crossing.parallelFrame,JointScalar.parallel,Frame.select,Frame.withInput,Frame.subst,
    spliceCore,CircuitBatch.Fragment.append,Frame.initial,CircuitBatch.Frame.initial,CircuitBatch.Fragment.empty,
    List.map_nil,List.append_nil,same]

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
