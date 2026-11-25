import OAI.Computability.BorderVNP.ModelHomogenizeGate
import OAI.Computability.VPVNP.CircuitSize

/-! # Homogenization of shared arithmetic circuits

For every original gate the new program retains its components of degrees zero through
`d`. The multiplication step uses one convolution for each of those degrees.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open VPVNP MvPolynomial

variable {R σ : Type*} [CommRing R] {n m : ℕ}

namespace Homogenize

private theorem operand (p : Program R σ n) (q : Program R σ m) (d : ℕ)
    (h : ∀ j i, i ≤ d → HasWire q (homogeneousComponent i (p.run C X j)))
    (a : Ref R σ n) (i : ℕ) (hi : i ≤ d) :
    HasWire q (homogeneousComponent i (a.read C X (p.run C X))) := by
  cases a with
  | gate j => exact h j i hi
  | var x =>
    change HasWire q (homogeneousComponent i (X x))
    rw [homogeneousComponent_of_mem (isHomogeneous_X R x)]
    split
    · exact hasWire_var q x
    · simpa using hasWire_const q 0
  | const a =>
    change HasWire q (homogeneousComponent i (C a))
    rw [homogeneousComponent_of_mem (isHomogeneous_C σ a)]
    split
    · exact hasWire_const q a
    · simpa using hasWire_const q 0

/-- Append a gate component by reading already available components of the two operands. -/
theorem append_component (p : Program R σ n) (op : BinOp) (k : ℕ)
    {a b : MvPolynomial σ R}
    (ha : ∀ i ≤ k, HasWire p (homogeneousComponent i a))
    (hb : ∀ i ≤ k, HasWire p (homogeneousComponent i b)) :
    ∃ l ≤ n + 2*(k+1), ∃ q : Program R σ l,
      Preserves p q ∧ HasWire q (homogeneousComponent k (op.apply a b)) := by
  cases op with
  | mul => exact append_product_component p k ha hb
  | add =>
    obtain ⟨q, hq, h⟩ := append_binary p .add (ha k le_rfl) (hb k le_rfl)
    exact ⟨n+1, by omega, q, hq, by simpa [BinOp.apply] using h⟩
  | sub =>
    obtain ⟨q, hq, h⟩ := append_binary p .sub (ha k le_rfl) (hb k le_rfl)
    exact ⟨n+1, by omega, q, hq, by simpa [BinOp.apply] using h⟩

/-- Each gate of a shared program has all its components through degree `d` available in
a single program of size at most `2*(d+1)^2` times the original size. -/
theorem program_components (p : Program R σ n) (d : ℕ) :
    ∃ m ≤ 2 * (d+1)^2 * n, ∃ q : Program R σ m,
      ∀ j i, i ≤ d → HasWire q (homogeneousComponent i (p.run C X j)) := by
  induction p with
  | nil => exact ⟨0, by simp, .nil, fun j => j.elim0⟩
  | @snoc n p op a b ih =>
    obtain ⟨m, hm, q, h⟩ := ih
    let x := a.read C X (p.run C X)
    let y := b.read C X (p.run C X)
    obtain ⟨m', hm', q', hqq', hnew⟩ :=
      extend_fin q (d+1) (2*(d+1)) (fun i => homogeneousComponent i (op.apply x y)) (by
        intro l r hqr i hi
        obtain ⟨l', hl', r', hrr', hr'⟩ := append_component r op i (a := x) (b := y)
          (fun j hj => hqr _ (operand p q d h a j (by omega)))
          (fun j hj => hqr _ (operand p q d h b j (by omega)))
        exact ⟨l', by omega, r', hrr', hr'⟩)
    refine ⟨m', ?_, q', ?_⟩
    · calc
        m' ≤ m + (d+1) * (2*(d+1)) := hm'
        _ ≤ 2*(d+1)^2*n + (d+1)*(2*(d+1)) := Nat.add_le_add_right hm _
        _ = 2*(d+1)^2*(n+1) := by ring
    · intro j
      refine Fin.lastCases ?_ (fun t => ?_) j
      · intro i hi
        simpa only [Program.run, Fin.lastCases_last, x, y] using hnew i (by omega)
      · intro i hi
        simpa only [Program.run, Fin.lastCases_castSucc] using hqq' _ (h t i hi)

/-- Components of the designated output are available at the same bound as those of
the internal wires, including outputs directly selecting a scalar or variable. -/
theorem circuit_component (c : Circuit R σ n) (d : ℕ) :
    ∃ m ≤ 2 * (d+1)^2 * n, ∃ b : Circuit R σ m,
      b.polynomial = homogeneousComponent d c.polynomial := by
  obtain ⟨m, hm, q, h⟩ := program_components c.program d
  obtain ⟨r, hr⟩ := operand c.program q d h c.output d le_rfl
  exact ⟨m, hm, ⟨q, r⟩, hr⟩

end Homogenize

/-- Taking one homogeneous component of a formal polynomial costs at most a quadratic
factor in its degree. Gate sharing and arbitrary scalar inputs are preserved. -/
theorem circuitSize_homogeneousComponent_le (d : ℕ) (p : MvPolynomial σ R) :
    circuitSize (homogeneousComponent d p) ≤ 2 * (d+1)^2 * circuitSize p := by
  obtain ⟨c, hc⟩ := circuitSize_spec p
  obtain ⟨m, hm, b, hb⟩ := Homogenize.circuit_component c d
  exact circuitSize_le_iff.mpr ⟨m, hm, b, hb.trans (congrArg _ hc)⟩

end BorderVNP
end Computability
end OAI
