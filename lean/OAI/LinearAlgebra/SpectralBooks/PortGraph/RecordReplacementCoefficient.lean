import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementTemplate
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentNamedNetwork
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSmall

/-! # Padded local tables on the tree selected by a patch record -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph.PatchShape.RecordTerm

open PlanarPatch UniformDecorations ReplacementTemplate

variable {K w : ℕ} {F : Type} [Field F] {R : PatchShape K} {hc : R.InternallyConnected}
  (u : R.RecordTerm hc w F)

/-- The same old address has the same formal variable in every record. -/
abbrev worldTable (F : Type) [Field F] (w : ℕ) : Tables (MvPolynomial (Address w) F) w :=
  fun θ a => MvPolynomial.X ⟨θ,a⟩

/-- Actual ternary coefficients, or the direct patch table, with all indices
in the new common alphabet. Each stub still uses the original width. -/
def localTable : u.piece.graph.StubTable u.piece.attach (Bits (8*w)) (MvPolynomial (Address w) F) :=
  match u with
  | .direct _ => singleTable (fun s : R.Stub => s.val.side) (R.oldValue (worldTable F w))
  | .pruned total large t hl _ _ _ => t.namedTable (rootMem total large t hl)
      (2^(8*w)) (2^w) (stubEquiv total t hl)

/-- This bound holds separately at each numbered role and each padded tuple. -/
theorem localTable_hasFormula (v a s) : HasFormula (2^(entryExponent K*(w+1))) (u.localTable v a s) := by
  cases u with
  | direct small =>
    apply (singleCoefficient_hasFormula_bound _ R.toPiece.graph R.toPiece.attach
      (K:=K) (w:=w) (by
        change Fintype.card (Fin R.size.val) ≤ K
        simpa only [Fintype.card_fin] using Nat.le_of_lt_succ R.size.isLt)
      R.total_degree_le (R.oldTable (worldTable F w)) (fun _ _ _ => HasFormula.input _) _ _).mono
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_max_left ..))
  | pruned total large t hl _ _ cost =>
    exact t.hasFormula_namedTable _ _ _ _ (Nat.one_le_pow _ _ (by decide)) cost v a s

/-- Every entry with an out-of-range original stub vanishes. -/
theorem localTable_stub_lt {v a s} (hn : u.localTable v a s ≠ 0) (p) : (s p).val < 2^w := by
  cases u with
  | direct small =>
    rcases v with ⟨⟩
    change padStubs _ _ ≠ 0 at hn
    by_contra! h
    apply hn
    apply dite_eq_right
    intro all
    exact (all p.val).not_ge h
  | pruned total large t hl _ _ _ => exact t.namedTable_stub_lt _ _ _ _ hn p

/-- The open contraction of this numbered template at a legal old boundary
tuple is precisely its selected summand of the straightening identity. -/
theorem openValue_cast (x : R.Stub → Bits w) :
    u.piece.graph.openValue u.piece.attach u.localTable
      (fun s => (x s).castLE (Nat.pow_le_pow_right (by decide) (by omega : w ≤ 8*w))) =
      u.value x := by
  cases u with
  | direct small =>
    exact single_openValue_old _ R.toPiece.graph R.toPiece.attach (R.oldTable (worldTable F w)) _ x
  | pruned total large t hl hb _ _ =>
    exact TrivalentTree.openValue_namedTable _ t _ _ hb _
      (stubNames_complete total t hl).1 (stubNames_complete total t hl).2 x _

/-- The equality of open tensors includes padded tuples that the old network
does not sum. A single illegal boundary value kills that summand. -/
theorem openValue_all (x : R.Stub → Bits (8*w)) :
    u.piece.graph.openValue u.piece.attach u.localTable x = padStubs u.value x := by
  by_cases good : ∀ s, (x s).val < 2^w
  · let y (s : R.Stub) : Bits w := ⟨(x s).val,good s⟩
    rw [padStubs, dite_eq_left good]
    exact u.openValue_cast y
  · rw [padStubs, dite_eq_right good]
    obtain ⟨s,hs⟩ := Classical.not_forall.mp good
    unfold openValue
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.prod_eq_zero (Finset.mem_univ (u.piece.attach s))
    by_contra hne
    exact hs (u.localTable_stub_lt hne ⟨s,rfl⟩)

end PortGraph.PatchShape.RecordTerm

end

end SpectralBooks
end LinearAlgebra
end OAI
