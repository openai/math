import OAI.Computability.VPVNP.VerifierMachineNetwork

namespace OAI
/-! # Selecting the verifier for the current RAM instruction

The instruction table is fixed. Each counter has one Boolean selector and one
row test. Disjoining the selected tests implements a lookup even when the code
has repeated instructions.
-/

namespace ThreeFlat.Diagonal.TraceFetch

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open Computability.VPVNP.VerifierNetwork (Frame)

variable {σ : Type*} {p : ℕ}

/-- Look up one bit using a one-hot program counter. -/
def fetch (pc row : Fin p → Expr σ) : Expr σ :=
  Expr.disjoin (List.ofFn fun i => (pc i).and (row i))

theorem fetch_eval (pc row : Fin p → Expr σ) (x : σ → Bool) (i : Fin p)
    (hpc : ∀ j, (pc j).eval x = decide (i = j)) :
    (fetch pc row).eval x = (row i).eval x := by
  apply Bool.eq_iff_iff.mpr
  simp [fetch, Expr.eval_disjoin_true, List.mem_ofFn, Expr.eval, hpc]

theorem fetch_size_le (pc row : Fin p → Expr σ) {c s : ℕ}
    (hc : ∀ i, (pc i).size ≤ c) (hs : ∀ i, (row i).size ≤ s) :
    (fetch pc row).size ≤ p * (c + s + 2) + 1 := by
  have h := Expr.size_disjoin_le (List.ofFn fun i => (pc i).and (row i)) (c + s + 1) (by
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    simp only [Expr.size]
    have := hc i
    have := hs i
    omega)
  simpa [fetch, Nat.add_assoc] using h

/-- Append the instruction selector to an array of already computed bits. -/
noncomputable def frame {τ : Type*} [Fintype σ] [Fintype τ] (f : Frame σ τ)
    (pc row : Fin p → Expr τ) : Frame σ Unit := f.step fun _ => fetch pc row

@[simp] theorem frame_eval {τ : Type*} [Fintype σ] [Fintype τ] (f : Frame σ τ)
    (pc row : Fin p → Expr τ) (x : σ → Bool) (i : Fin p)
    (hpc : ∀ j, (pc j).eval (f.eval x) = decide (i = j)) :
    (frame f pc row).eval x () = (row i).eval (f.eval x) := by
  simpa [frame] using fetch_eval pc row (f.eval x) i hpc

theorem frame_size_le {τ : Type*} [Fintype σ] [Fintype τ] (f : Frame σ τ)
    (pc row : Fin p → Expr τ) {c s : ℕ}
    (hc : ∀ i, (pc i).size ≤ c) (hs : ∀ i, (row i).size ≤ s) :
    (frame f pc row).size ≤ f.size + p * (c + s + 2) + 1 := by
  simpa [frame, Nat.add_assoc] using
    (f.step_size_le (fun _ : Unit => fetch pc row) _ (fun _ => fetch_size_le pc row hc hs))

end ThreeFlat.Diagonal.TraceFetch

end OAI
