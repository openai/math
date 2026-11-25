import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentNamedRead
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenNetwork
import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementClosure

/-! # Boundary names and external widths in a trivalent replacement

The uniform table uses the padded internal width on every wire. A boundary
port keeps its original width by assigning zero to any entry outside that
range. On the original boundary assignments the network evaluates the tree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PlanarPatch.TrivalentTree

open PortGraph

variable {K V S : Type*} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)
variable (h : [] ∈ t.branchAddresses) (D U : ℕ) (e : S ≃ t.Stub)

/-- Local table in the three ordered slots, after renaming stubs and padding their indices. -/
def namedTable [CommSemiring K] : t.internalGraph.StubTable (t.attach h ∘ e) (Fin D) K :=
  fun v a s => if ∀ b, (s b).val < U then
    t.slotTensor v (fun i => Sum.elim (fun p => (a p).val) (fun b => (s b).val)
      ((t.namedSlotEquiv h e v).symm i)) else 0

/-- A nonzero table entry uses a legal value on every exterior port. -/
theorem namedTable_stub_lt [CommSemiring K] {v a s}
    (hn : t.namedTable h D U e v a s ≠ 0) (b) : (s b).val < U := by
  by_contra! hn'
  exact hn (ite_eq_right (fun hall => (hall b).not_ge hn'))

/-- One exterior index outside its original alphabet annihilates the entire open tensor. -/
theorem openValue_namedTable_zero [CommSemiring K] (z : S → Fin D) (b : S)
    (hb : U ≤ (z b).val) :
    t.internalGraph.openValue (t.attach h ∘ e) (t.namedTable h D U e) z = 0 := by
  unfold openValue
  apply Finset.sum_eq_zero
  intro y _
  let v := (t.attach h ∘ e) b
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  by_contra hn
  exact (t.namedTable_stub_lt h D U e hn ⟨b,rfl⟩).not_ge hb

/-- External zero padding preserves the formula bound on all entries. -/
theorem hasFormula_namedTable {F I : Type*} [Field F] (u : TrivalentTree (MvPolynomial I F) d q)
    (h : [] ∈ u.branchAddresses) (D U : ℕ) (e : S ≃ u.Stub) {W : ℕ}
    (hW : 1 ≤ W) (hf : u.FormulaBound W) (v a s) :
    HasFormula W (u.namedTable h D U e v a s) := by
  unfold namedTable
  split
  · exact u.hasFormula_slotTensor hW hf _ _
  · simpa using (HasFormula.const (I := I) (0 : F)).mono hW

/-- With legal exterior values, renaming the stubs preserves the open contraction. -/
theorem openValue_namedTable_eq_network [CommSemiring K] (z : S → Fin D) (hz : ∀ s, (z s).val < U) :
    t.internalGraph.openValue (t.attach h ∘ e) (t.namedTable h D U e) z =
      (t.openNetwork h D (A := fun _ => Fin D) (fun _ a => a.val)).eval (fun p => z (e.symm p)) := by
  unfold openValue OpenNetwork.eval
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) ?_
  intro y _
  refine Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) ?_
  intro v _
  have legal (b : {b // (t.attach h ∘ e) b = v}) : (z b.val).val < U := hz b.val
  simp only [namedTable, legal, implies_true, ite_true, openNetwork]
  change t.slotTensor v _ = t.slotTensor v _
  apply congrArg
  funext i
  simp only [localCoordinate, namedSlotEquiv, Equiv.symm_trans_apply,
    Equiv.sumCongr_symm]
  cases (t.openSlotEquiv h v).symm i <;> rfl

/-- The named, padded network evaluates the pruned tree on each assignment in
the original external width, including the value at its distinguished output. -/
theorem openValue_namedTable [CommSemiring K] (t : TrivalentTree K (fun _ : V => U) U)
    (h : [] ∈ t.branchAddresses) (D : ℕ) (hb : t.Bounded D) (out : V)
    (nd : (out :: t.labels).Nodup) (all : ∀ v, v ∈ out :: t.labels)
    (x : V → Fin U) (hd : U ≤ D) :
    t.internalGraph.openValue (t.attach h ∘ (t.stubNames out nd all).symm)
      (t.namedTable h D U (t.stubNames out nd all).symm) (fun v => (x v).castLE hd) =
      t.eval x (x out) := by
  refine (t.openValue_namedTable_eq_network h D U (t.stubNames out nd all).symm
    (fun v => (x v).castLE hd) (fun v => (x v).isLt)).trans ?_
  apply t.eval_openNetwork h D _ hb x (x out)
  · rfl
  · intro p
    exact (t.leafRead_eq_named x p).symm

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
