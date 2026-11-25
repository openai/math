import OAI.Computability.BorderVNP.PackedRoutingSewn
import OAI.Computability.BorderVNP.PackedRoutingOwnedArrays

/-! # Publishing the secondary task controls from the geometry advice

Each bit of a length-dependent control word references one of the same two
constant wires already present in the public sewing stage. Thus the allocation
addresses in the controls do not influence the length of the compiled gate
program. The fixed RAM interpreter places the vector immediately after the
owned-cell and original-site views.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM GeometryFrameEncoding ParseBatchSort
open ParseBatchCounts (numberWords value_encode)
open CellAddressCircuit Diagonal.ExternalSew.FieldExport RoutingISA DiagonalResidueRAM

variable {σ γ : Type*} [Fintype σ] [Fintype γ] {s m n C d k w J A v o W u : ℕ}

/-- Only constant output references depend on the control-word values. -/
noncomputable def controlWords (controls : Fin v → Fin (2^w)) : Frame (σ ⊕ Bool) (Fin v × Fin w) :=
  Frame.initial fun ij => .inr ((numberWords w).symm (controls ij.1) ij.2)

/-- Prefix the caller's remaining results with the control words without adding gates. -/
noncomputable def withControls (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w)) :
    Frame (σ ⊕ Bool) (Outputs (v+o) w) :=
  rest.withInput.select (Sum.elim
    (fun p => Fin.addCases (fun i => Sum.inl (.inr ((numberWords w).symm (controls i) p.2)))
      (fun i => Sum.inr (.inl (i,p.2))) p.1) (fun j => Sum.inr (.inr j)))

@[simp] theorem withControls_first (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w))
    (y : σ ⊕ Bool → Bool) (i : Fin v) (j : Fin w) :
    (withControls controls rest).eval y (.inl (i.castAdd o,j)) = (controlWords controls).eval y (i,j) := by
  simp [withControls,controlWords]

@[simp] theorem withControls_rest (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w))
    (y : σ ⊕ Bool → Bool) (i : Fin o) (j : Fin w) :
    (withControls controls rest).eval y (.inl (Fin.natAdd v i,j)) = rest.eval y (.inl (i,j)) := by simp [withControls]

@[simp] theorem withControls_valid (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w))
    (y : σ ⊕ Bool → Bool) : (withControls controls rest).eval y (.inr ()) = rest.eval y (.inr ()) := by
  simp [withControls]

@[simp] theorem withControls_size (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w)) :
    (withControls controls rest).size = rest.size := rfl

/-- The wired reference is interpreted as the exact unsigned length-dependent word. -/
theorem control_value (source : Frame γ σ) (y : γ → Bool) (controls : Fin v → Fin (2^w)) (i : Fin v) :
    value (fun j => (controlWords controls).eval ((withSewnFields source).eval y) (i,j)) = (controls i).val := by
  simp only [controlWords,Frame.initial_eval,withSewnFields,Frame.subst_eval,constants_eval,Sum.elim_inr,id_eq]
  exact value_encode _

/-- Canonical address for frame 92, after the live placement and the three marker arrays. -/
def controlsBase (origin m C J A : ℕ) := (bases origin m C J).livePairs+2*A+C+J+C

/-- All addressed control words, including the tail capacity, sort directories,
arena starts and field widths, come from the actual geometry output. -/
theorem controls_at (F : Fields s m n C d k w (σ ⊕ Bool)) (source : Frame γ σ) (y : γ → Bool)
    (old : Fin J → Fin s) (controls : Fin v → Fin (2^w)) (rest : Frame (σ ⊕ Bool) (Outputs o w))
    (origin : ℕ) (mz : Memory W) (width : w ≤ W)
    (out : ∀ i : Fin ((C+(J+C))+(v+o)), mz (origin+m*3+count m C J A+i.val) =
      word W (value fun j => (withPrivateViews F old (withControls controls rest)).eval
        ((withSewnFields source).eval y) (.inl (i,j)))) (i : Fin v) :
    readings mz (controlsBase origin m C J A+i.val) = (controls i).val := by
  have raw := out (Fin.natAdd (C+(J+C)) (i.castAdd o))
  simp only [withPrivateViews,GeometryOutput.prepend_rest,withControls_first,
    Fin.val_natAdd,Fin.val_castAdd,control_value] at raw
  have addr : controlsBase origin m C J A+i.val =
      origin+m*3+count m C J A+(C+(J+C)+i.val) := by dsimp [controlsBase,bases,count]; omega
  rw [addr]
  exact (congrArg Fin.val raw).trans (word_val _ _ ((controls i).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) width)))

open BinPackingGames.Foundations.Complexity.CookLevin
open private spliceCore from OAI.Computability.VPVNP.VerifierMachineSplice

private theorem subst_gates {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (a b : Frame Y Z) (source : Frame X Y) (h : a.core.fragment.gates = b.core.fragment.gates) :
    (a.subst source).core.fragment.gates = (b.subst source).core.fragment.gates := by
  simp only [Frame.subst,spliceCore,CircuitBatch.Fragment.append,h]

private theorem prepend_gates {X : Type*} [Fintype X] {p q w : ℕ} (first : Frame X (Fin p × Fin w))
    (a b : Frame X (Outputs q w)) (h : a.core.fragment.gates = b.core.fragment.gates) :
    (GeometryOutput.prepend first a).core.fragment.gates = (GeometryOutput.prepend first b).core.fragment.gates := by
  simp only [GeometryOutput.prepend,Crossing.parallelFrame,JointScalar.parallel,Frame.select,Frame.withInput,
    Frame.subst,spliceCore,CircuitBatch.Fragment.append,h]

private theorem compile_gates {X T : Type*} [Fintype X] {o w : ℕ} (a b : Frame X (Outputs o w))
    (pins : X → T ⊕ Bool) (h : a.core.fragment.gates = b.core.fragment.gates) :
    (compile a pins).size = (compile b pins).size := by
  simp only [compile,Frame.circuitSize,CookCircuit.transcriptSize,CircuitBatch.Frame.toCircuit,
    CircuitBatch.Fragment.toCircuit,h]

/-- Allocators may calculate the program size on a dummy control vector, then
publish addresses derived from that size. The actual gate count is identical. -/
theorem compiled_size_controls (F : Fields s m n C d k w (σ ⊕ Bool)) (hk : k ≤ w) (old : Fin J → Fin s)
    (ports : Fin A → Fin n) (rest : Frame (σ ⊕ Bool) (Outputs o w)) (source : Frame γ σ)
    (pins : γ → (Fin u ⊕ Fin 0) ⊕ Bool) (a b : Fin v → Fin (2^w)) :
    (compile ((full F hk old ports (withPrivateViews F old (withControls a rest))).subst (withSewnFields source)) pins).size =
    (compile ((full F hk old ports (withPrivateViews F old (withControls b rest))).subst (withSewnFields source)) pins).size := by
  apply compile_gates
  apply subst_gates
  apply prepend_gates
  apply prepend_gates
  apply prepend_gates
  rfl

/-- The extended length-only packet points field 92 at the addressed control vector.
The other routing fields are supplied by the ordinary routing extension. -/
def controlsExtension (other : Fin 81 → Word W) (origin m C J A : ℕ) (i : Fin 81) : Word W :=
  if i.val+31 = 92 then word W (controlsBase origin m C J A) else extension other origin m C J i

/-- Every other field retains its previous routing or stage-specific value. -/
theorem controlsExtension_other (other : Fin 81 → Word W) (origin m C J A : ℕ) (i : Fin 81)
    (ne : i.val+31 ≠ 92) : controlsExtension other origin m C J A i = extension other origin m C J i :=
  ite_eq_right ne

/-- The fixed extended-frame installer places the true control pointer at frame 92. -/
theorem installed_control_pointer (other : Fin 81 → Word W) (origin m C J A head : ℕ) (m0 : Memory W)
    (room : controlsBase origin m C J A < 2^W) :
    readings (ExtendedFrame.installed m0 head (controlsExtension other origin m C J A)) (head+92) =
      controlsBase origin m C J A := by
  have h := ExtendedFrame.installed_at m0 head (controlsExtension other origin m C J A) (61 : Fin 81)
  have val := (congrArg Fin.val h).trans (word_val _ _ room)
  simpa only [readings,Nat.add_assoc,show 31+(61 : Fin 81).val = 92 by decide] using val

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
