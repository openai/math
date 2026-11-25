import OAI.Computability.BorderVNP.GeometryAdviceFrame
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Contiguous subarrays of the native geometry result

Prefixing a word array keeps its stable numerical order and preserves the other
frame's validity wire. The existing physical interpreter writes both arrays in
one execution.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP VerifierNetwork GeometryFrameEncoding

variable {σ : Type*} [Fintype σ] {a b o : ℕ}

/-- One physical word array followed by an arbitrary further array and a validity flag. -/
noncomputable def prepend (p : Frame σ (Fin a × Fin b)) (f : Frame σ (Outputs o b)) :
    Frame σ (Outputs (a+o) b) :=
  (Crossing.parallelFrame p f).select (Sum.elim
    (fun q => Fin.addCases (fun i => Sum.inl (i,q.2)) (fun i => Sum.inr (.inl (i,q.2))) q.1)
    (fun _ => Sum.inr (.inr ())))

@[simp] theorem prepend_first (p : Frame σ (Fin a × Fin b)) (f : Frame σ (Outputs o b))
    (x : σ → Bool) (i : Fin a) (j : Fin b) :
    (prepend p f).eval x (.inl (i.castAdd o,j)) = p.eval x (i,j) := by simp [prepend]

@[simp] theorem prepend_rest (p : Frame σ (Fin a × Fin b)) (f : Frame σ (Outputs o b))
    (x : σ → Bool) (i : Fin o) (j : Fin b) :
    (prepend p f).eval x (.inl (Fin.natAdd a i,j)) = f.eval x (.inl (i,j)) := by simp [prepend]

@[simp] theorem prepend_valid (p : Frame σ (Fin a × Fin b)) (f : Frame σ (Outputs o b))
    (x : σ → Bool) : (prepend p f).eval x (.inr ()) = f.eval x (.inr ()) := by simp [prepend]

@[simp] theorem prepend_size (p : Frame σ (Fin a × Fin b)) (f : Frame σ (Outputs o b)) :
    (prepend p f).size = p.size+f.size := by simp [prepend]

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA GeometryAdvice DiagonalResidueRAM
variable {u w : ℕ}

/-- A successful native reconstruction produces the two contiguous addressed arrays with
their original Boolean-frame values, and every address below the scratch allocation is preserved. -/
theorem prefix_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : BroadcastFrame) (st : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : Layout) (base start : ℕ) (src : Fin u → ℕ) (p : Frame σ (Fin a × Fin b))
    (rest : Frame σ (Outputs o b)) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : st.Fits f w (pub 0).val) :
    let t := compile (prepend p rest) pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    Placement pub l base start st.dense src t → PhysicalInput pub m f st L P l base start src t x →
    rest.eval input (.inr ()) = true →
    ∃ es z mz, Runs pub mac reconstruct s m es z mz ∧ traceCost es ≤ GeometryAdvice.cost w u t.size (a+o) b ∧
      (∀ i : Fin a, mz (l.dest+i.val) = word w (ParseBatchSort.value fun j => p.eval input (i,j))) ∧
      (∀ i : Fin o, mz (l.dest+a+i.val) = word w (ParseBatchSort.value fun j => rest.eval input (.inl (i,j)))) ∧
      ∀ addr, addr < base → addr < start → addr < l.temp → addr < l.dest → addr < st.dense → mz addr = m addr := by
  intro t input place h valid
  have hv : validBit t (Sum.elim x Fin.elim0) = true :=
    (compiled_valid (prepend p rest) pins _).trans ((prepend_valid p rest input).trans valid)
  obtain ⟨es,z,mz,run,ct,_,out⟩ := reconstruct_runs pub mac s m f st L P l base start src t x fit space place h hv
  have raw (i : Fin (a+o)) : mz (l.dest+i.val) = word w (ParseBatchSort.value fun j =>
      (prepend p rest).eval input (.inl (i,j))) :=
    (out.words i).trans (congrArg (word w) (congrArg ParseBatchSort.value (funext fun j => bit_eval ..)))
  refine ⟨es,z,mz,run,ct,fun i => ?_,fun i => ?_,?_⟩
  · simpa using raw (i.castAdd o)
  · simpa [Nat.add_assoc] using raw (Fin.natAdd a i)
  · intro addr hv hp ht hd hs
    exact (out.outside addr (Or.inl hv) (Or.inl hp) (Or.inl ht) (Or.inl hd)).trans
      (st.image_outside m (Or.inl hs))

end GeometryOutput

end BorderVNP
end Computability
end OAI
