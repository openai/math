import OAI.Computability.BorderVNP.CubeISAOwnedPackets

/-! # The closed selector length of a symbol row

Fixing the increasing symbol pair removes precisely one cube coordinate.
Every remaining coordinate contributes one of the two-element symbol sets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

variable {n d blocks : ℕ}

/-- Number of increasing coordinate pairs of alphabet symbols. -/
theorem card_symbols (d : ℕ) : Fintype.card (Symbols d) = d.choose 2 := by
  rw [Fintype.card_subtype]
  simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin]
    using Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin d)))

private def fixedPackets (i : Fin (n+1)) (s : Symbols d) :
    (((Fin n → Symbols d) × Bool) × Fin blocks) ≃ {p : Packet n d blocks // p.1.1 i = s} where
  toFun x := ⟨((i.insertNth (α := fun _ => Symbols d) s x.1.1, x.1.2),x.2), by simp⟩
  invFun p := ((i.removeNth p.val.1.1,p.val.1.2),p.val.2)
  left_inv x := by simp only [Fin.removeNth_insertNth]
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    exact Fin.insertNth_eq_iff.mpr ⟨p.property.symm,rfl⟩

/-- The strict row contains exactly one packet for each combination of other
coordinate pairs, orientation and block. -/
theorem card_packets_row (i : Fin (n+1)) (s : Symbols d) :
    Fintype.card {p : Packet n d blocks // p.1.1 i = s} = 2*blocks*(d.choose 2)^n := by
  rw [← Fintype.card_congr (fixedPackets i s)]
  simp [card_symbols, Nat.mul_comm, Nat.mul_assoc]

/-- The exact selector prefix in each off-diagonal row; its length is independent
of the selected packet summands and the grouping coordinate. -/
theorem strict_rowSelectorBits (K h : ℕ) (i : Fin (n+1)) (s : Symbols d) :
    rowSelectorBits n d blocks K h i (Sym2.mk s.val.1 s.val.2) =
      2*blocks*(d.choose 2)^n * VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h := by
  unfold rowSelectorBits
  simp_rw [packet_itemRow_eq_iff i s]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, card_packets_row]
  rfl

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
