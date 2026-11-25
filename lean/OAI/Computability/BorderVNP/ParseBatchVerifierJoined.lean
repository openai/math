import OAI.Computability.BorderVNP.ParseBatchVerifierKeys
import OAI.Computability.BorderVNP.ParseBatchVerifierTreesAssembly

/-! # Joining the shared batch parse verifier and the sparse histogram verifier -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchVerifier

open VPVNP.VerifierNetwork ParseBatchCounts ParseBatchTrees ParseBatch
open BinPackingGames.Foundations.Complexity.CookLevin

variable {m g n r : ℕ}

/-- Actual free inputs, in the order external query, guessed records, guessed marker data. -/
abbrev Pins (m g n r : ℕ) (d : Fin n) :=
  (Fin r × Fin m) ⊕ ((Fin r × RowPins m g n d) ⊕
    ArithmeticPin (2^labelWidth m g n) (histogramWidth m g r d))

private def treeInput (d : Fin n) : BatchPins m g n r d → Pins m g n r d :=
  Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)

private noncomputable def histogramInput (d : Fin n) :
    HistogramPin (Use r d) (labelWidth m g n) (histogramWidth m g r d) → Pins m g n r d
  | .inl ((i,j),k) => .inr (.inl (i,j,labelPins m g n k))
  | .inr v => .inr (.inr v)

/-- Compile one AND of both accepting wires. All occurrence bits are shared
between the two verifiers, including all repeated input uses inside each verifier. -/
noncomputable def joined (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit) :
    Frame (Pins m g n r d) Unit :=
  (Crossing.parallelFrame
    (trees.subst (Frame.initial (treeInput d)))
    ((histogramFrame (histogramLayout m g r d)).subst (Frame.initial (histogramInput d)))).step
    (fun _ => .and (.input (.inl ())) (.input (.inr ())))

/-- The assembled circuit accepts exactly one histogram transcript for each
valid raw parse tuple. Malformed record tuples are always rejected. -/
theorem joined_eval (d : Fin n) (h : Fin g) (trees : Frame (BatchPins m g n r d) Unit)
    (he : ∀ x bs, trees.eval (batchInput d x bs) () = true ↔ Accepted d h x bs)
    (x : Fin r → Fin m → Bool) (raw : Fin r × RowPins m g n d → Bool)
    (aux : ArithmeticPin (2^labelWidth m g n) (histogramWidth m g r d) → Bool) :
    let bs : Guess m g n r d := fun i j k => raw (i,j,k)
    (joined d trees).eval (Sum.elim (fun ij => x ij.1 ij.2) (Sum.elim raw aux)) () = true ↔
      Accepted d h x bs ∧ aux = canonicalGuess (histogramLayout m g r d) (occurrenceBits bs) := by
  let bs : Guess m g n r d := fun i j k => raw (i,j,k)
  let z : Pins m g n r d → Bool := Sum.elim (fun ij => x ij.1 ij.2) (Sum.elim raw aux)
  have ht : (Frame.initial (treeInput (m := m) (g := g) (r := r) d)).eval z = batchInput d x bs := by
    funext v
    cases v <;> simp [treeInput, batchInput, z, bs]
  have hh : (Frame.initial (histogramInput (m := m) (g := g) (r := r) d)).eval z =
      Sum.elim (occurrenceBits bs) aux := by
    funext v
    cases v <;> simp [histogramInput, occurrenceBits, z, bs]
  change (joined d trees).eval z () = true ↔ _
  simp only [joined, Frame.step_eval, StatementCircuit.Expr.eval, Bool.and_eq_true,
    Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr, Frame.subst_eval, ht, hh, he,
    histogramFrame_eval_iff_eq_canonicalGuess, bs]

/-- The joined circuit charges the two subcircuits once and adds only their
single accepting conjunction. -/
theorem joined_size (d : Fin n) (trees : Frame (BatchPins m g n r d) Unit) :
    (joined d trees).size ≤ trees.size +
      3000 * 2 ^ histogramWidth m g r d * (histogramWidth m g r d + 2)^3 + 3 := by
  unfold joined
  apply (Frame.step_size_le _ _ 3 (fun _ => le_rfl)).trans
  simp only [Crossing.parallelFrame_size, Frame.subst_size, Frame.initial_size, zero_add,
    Fintype.card_unit, one_mul]
  gcongr
  exact histogramFrame_size_per_row _

end ParseBatchVerifier

end BorderVNP
end Computability
end OAI
