import OAI.Computability.BorderVNP.PackedTerminalRetainedEmitter

/-! # Actual retained-terminal execution, original routing fields, and the compact packet address -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open Packing Packing.CellAddressCircuit Packing.RoutingOutputs GeometryFrameEncoding VPVNP.VerifierNetwork
open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM ParseBatchSort

variable {X Y V Z H : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype Z] [Fintype H]
variable {s m n C d k w J P o W active reserve v : ℕ}

variable (F : Fields s m n C d k w Z) (hk : k≤w) (old : Fin J → Fin s) (ports : Fin P → Fin n)
variable (rest : Frame (Z ⊕ H) (Outputs o w)) (src : Frame ((X ⊕ Fin reserve) ⊕ V) Z) (keep : Frame ((X ⊕ Fin reserve) ⊕ V) H)

/-- Relabeling the additional inputs gives a comparison circuit with the
same number of gates as the actual rest program. -/
noncomputable def wiresOnly (extra : H → Z) : Frame Z (Outputs o w) := rest.subst (Frame.initial (Sum.elim id extra))

theorem emitter_size_relative (extra : H → Z) :
    (emitter F hk old ports rest src keep).size =
      keep.size+(terminalEmitter F hk old ports (wiresOnly rest extra) src).size := by
  rw [emitter_size]
  simp [terminalEmitter,full,wiresOnly]
  omega

/-- The fixed profile interpretation on the real public input and its checked
terminal output pins. -/
noncomputable def branch (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active≤reserve)
    (x : X → Bool) (word : Fin reserve → Bool) : ((X ⊕ Fin reserve) ⊕ V) → Bool :=
  Sum.elim (Sum.elim x word) (fun j => history.eval (Sum.elim x (readProfile order fit word)) (.inl j))

variable (history : Frame (X ⊕ Y) (V ⊕ Unit)) (order : Y ≃ Fin active) (fit : active≤reserve)
variable (x : X → Bool) (word : Fin reserve → Bool)
local notation3 "y₀" => branch history order fit x word

/-- For proofs about the ordinary routing arrays the concrete, retained
execution can use the established exporter with the very same numerical outputs. -/
theorem emitted_eq :
    emittedWords history order fit (emitter F hk old ports rest src keep) x word =
      emittedWords history order fit (terminalEmitter F hk old ports (atExtra rest (keep.eval y₀)) src) x word := by
  funext i
  apply congrArg value
  funext j
  exact (emitter_eval F hk old ports rest src keep y₀ (i,j)).trans (by simp [terminalEmitter,branch])

variable {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {bank after : Bank W} {mem result : Memory W}
variable {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}

/-- The same native execution returns its routing image and every true joined
packet value. The output addresses are those used by the existing row producers. -/
theorem routing_return (width : w≤W)
    (run : GeometryReturn pub mac bank mem fresh dest clock
      (emittedWords history order fit (emitter F hk old ports rest src keep) x word) es after result) :
    Image F old ports (src.eval y₀) dest (readings result) ∧
      ∀ i : Fin o, result (dest+m*3+RoutingOutputs.count m C J P+i.val) =
        DiagonalResidueRAM.word W (value fun j => rest.eval (Sum.elim (src.eval y₀) (keep.eval y₀)) (.inl (i,j))) := by
  rw [emitted_eq] at run
  obtain ⟨_,_,image,other,_⟩ :=
    GeometryReturn.routing_image history order fit F hk width old ports (atExtra rest (keep.eval y₀)) src x word run
  exact ⟨image,fun i => (other i).trans (by simp [branch])⟩

/-- First RAM word of the actual packet output, following the fixed routing,
private-view and control words. -/
def packetBase (origin m C J P v : ℕ) := controlsBase origin m C J P+v

variable (B : Fields s m n C d k w (Z ⊕ Bool)) (controls : Fin v → Fin (2^w))
variable (packet : Frame ((Z ⊕ Bool) ⊕ H) (Outputs o w)) (sewn : Frame ((X ⊕ Fin reserve) ⊕ V) (Z ⊕ Bool))

/-- The native placement stage returns the real packet words at the exact
following contiguous segment. Both current geometry and the old tape are
read on the same reserved profile branch. -/
theorem packet_return (width : w≤W)
    (run : GeometryReturn pub mac bank mem fresh dest clock
      (emittedWords history order fit
        (emitter B hk old ports (privateControls B old controls packet) sewn keep) x word) es after result) :
    Image B old ports (sewn.eval y₀) dest (readings result) ∧
      ∀ i : Fin o, readings result (packetBase dest m C J P v+i.val) =
        value (fun j => packet.eval (Sum.elim (sewn.eval y₀) (keep.eval y₀)) (.inl (i,j))) := by
  obtain ⟨img,other⟩ := routing_return B hk old ports (privateControls B old controls packet) sewn keep
    history order fit x word width run
  refine ⟨img,fun i => ?_⟩
  have raw := other (Fin.natAdd (C+(J+C)) (Fin.natAdd v i))
  simp only [privateControls,GeometryOutput.prepend_rest,joinedControls_rest,Fin.val_natAdd] at raw
  have addr : packetBase dest m C J P v+i.val =
      dest+m*3+RoutingOutputs.count m C J P+(C+(J+C)+(v+i.val)) := by
    dsimp [packetBase,controlsBase,bases,RoutingOutputs.count]; omega
  rw [addr]
  exact (congrArg Fin.val raw).trans (word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) width)))

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
