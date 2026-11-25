import OAI.Computability.VPVNP.JointScalarCore

/-! # Parallel Boolean verifiers on a shared input

The fusion construction tests one local crossing per step. Their input references
can point to the same guessed occupancy bits. Concatenating the verifier programs
retains all outputs and charges each local gate list only once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP.VerifierNetwork

variable {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]

/-- Run two verifier frames on the same input and expose both output arrays. -/
noncomputable def parallelFrame (f : Frame σ τ) (g : Frame σ ρ) : Frame σ (τ ⊕ ρ) :=
  VPVNP.JointScalar.parallel f g

@[simp] theorem parallelFrame_size (f : Frame σ τ) (g : Frame σ ρ) :
    (parallelFrame f g).size = f.size + g.size := by simp [parallelFrame]

@[simp] theorem parallelFrame_eval_inl (f : Frame σ τ) (g : Frame σ ρ) (x : σ → Bool) (i : τ) :
    (parallelFrame f g).eval x (.inl i) = f.eval x i := by simp [parallelFrame]

@[simp] theorem parallelFrame_eval_inr (f : Frame σ τ) (g : Frame σ ρ) (x : σ → Bool) (j : ρ) :
    (parallelFrame f g).eval x (.inr j) = g.eval x j := by simp [parallelFrame]

/-- A finite family of verifier frames with potentially different output arities
has one combined frame. Only a single shared initialization gate is needed. -/
theorem exists_parallelFrames {ι : Type*} [Fintype ι] {out : ι → Type*} [∀ i, Fintype (out i)]
    (f : ∀ i, Frame σ (out i)) :
    ∃ p : Frame σ (Σ i, out i), p.size ≤ 1 + ∑ i, (f i).size ∧
      ∀ x i j, p.eval x ⟨i,j⟩ = (f i).eval x j := by
  classical
  have partials (s : Finset ι) :
      ∃ p : Frame σ (Σ i, out i), p.size ≤ 1 + ∑ i ∈ s, (f i).size ∧
        ∀ i ∈ s, ∀ x j, p.eval x ⟨i,j⟩ = (f i).eval x j := by
    induction s using Finset.induction_on with
    | empty =>
      let start : Frame σ Empty := Frame.initial Empty.elim
      let init : Frame σ Unit := start.step fun _ => .const false
      have h := Frame.step_size_le start (fun _ : Unit => .const false) 1 (fun _ => le_rfl)
      exact ⟨init.select (fun _ => ()), by simpa [init, start] using h, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨p, hsize, h⟩ := ih
      let pick (a : Σ j, out j) : (Σ j, out j) ⊕ out i :=
        if h : a.1 = i then .inr (h ▸ a.2) else .inl a
      refine ⟨(parallelFrame p (f i)).select pick, ?_, ?_⟩
      · simp only [Frame.select_size, parallelFrame_size, Finset.sum_insert hi]
        omega
      · intro j hj x v
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [pick]
        · have hne : j ≠ i := fun e => hi (e ▸ hj)
          simpa [pick, hne] using h j hj x v
  obtain ⟨p, hp, he⟩ := partials Finset.univ
  exact ⟨p, hp, fun x i j => he i (Finset.mem_univ _) x j⟩

end Crossing

end BorderVNP
end Computability
end OAI
