import OAI.Computability.BorderVNP.CubeSharedRowsPhysical
import OAI.Computability.BorderVNP.CubePhysicalScheduleBudget

/-! # Total group charge for the emitted strict-pair records of Section 8.2 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open Physical VPVNP.MotifBase
variable {n d blocks K h : ℕ}

/-- The strict rows exhaust the selected cut width and all packet selectors.
The omitted diagonal rows have no selector or crossing bit on this cut. -/
theorem sum_reserved (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (hp : passesLengths b s select D) :
    (∑ p : Symbols d, reserved blocks K h D p) = cutWidth b s select (chosen b s select) +
      Fintype.card (Packet n d blocks)*VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h := by
  rw [← reserved_sum b s select D hp]
  let f (p : Symbols d) := Sym2.sortEquiv.symm ⟨p.val,p.property.le⟩
  have inj : Function.Injective f := by
    intro p q eq
    exact Subtype.ext (congrArg (fun x : {q : Fin d × Fin d // q.1 ≤ q.2} => x.val) (Sym2.sortEquiv.symm.injective eq))
  apply Fintype.sum_of_injective f inj
  · intro r hr
    let v := Sym2.sortEquiv r
    have eq : Sym2.mk v.val.1 v.val.2 = r := Sym2.sortEquiv.symm_apply_apply r
    have diag : r.IsDiag := by
      rw [← eq,Sym2.mk_isDiag_iff]
      apply v.property.antisymm
      by_contra! lt
      exact hr ⟨⟨v.val,lt⟩,eq⟩
    have d0 : D.2 r D.1 = 0 := by
      rw [(passesLengths_iff ..).mp hp]
      exact diagonal_row_width b s select _ r diag
    rw [d0,diagonal_row_selectors _ _ _ _ _ _ _ diag,Nat.zero_add]
  · intro p
    exact Nat.add_comm ..

/-- All groups together charge the original padded width at most twice. -/
theorem sum_groupRaw_le (S : ℕ) (i : Fin (n+1)) :
    (∑ s : Fin d, groupRaw S i s) ≤ 2*(S*(d^(n+1))^2) := by
  cases d with
  | zero => simp
  | succ k =>
    apply Nat.le_of_mul_le_mul_right (c := k+1)
    · rw [Finset.sum_mul]
      have bound := Finset.sum_le_sum (s := Finset.univ) (fun j _ => groupRaw_le S i (j : Fin (k+1)))
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm (k+1)] using bound
    · omega

/-- In native units, the total joint weight is bounded by twice the selected
communication, the actual total incoming data, and twice the original raw width.
This is the combinatorial bound on page 30 before applying the numerical scales. -/
theorem total_groupWords_le {A : Type*} [Fintype A] (recv : A → Label (n+1) d) (width : A → ℕ)
    (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (hp : passesLengths b s select D) :
    (∑ j : Fin d, groupWords recv width blocks K h b D j) ≤
      1000000*(2*(cutWidth b s select (chosen b s select) +
        Fintype.card (Packet n d blocks)*VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h) +
        ∑ a, width a) + 2*(blocks*(h*b)*(d^(n+1))^2) := by
  simp only [groupWords,dite_eq_left (Fin.isLt _),TeamNative.scaledWeight,Finset.sum_add_distrib,
    ← Finset.mul_sum]
  change 1000000*((∑ j : Fin d, incident blocks K h D j) + ∑ j : Fin d, dataAt recv width D.1 j) +
    (∑ j : Fin d, groupRaw (blocks*(h*b)) D.1 j) ≤ _
  rw [sum_incident,sum_reserved b s select D hp,sum_dataAt]
  exact Nat.add_le_add_left (sum_groupRaw_le _ _) _

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
