import OAI.Computability.VPVNP.TwoMarkedSplit

/-!
# Acting at a single endpoint of a marked tensor

Appendix A.3 places both exterior operators at the same endpoint of the first
marked leg. One wire supplies the exterior index held by the other endpoint.
The second marked leg and all background indices pass through unchanged.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v

namespace WireTensor

open scoped Classical

variable {k : Type u} {J : Type v} [Field k] [Fintype J]

private def markedPairEquiv (B : J → Type) (I K : Type) (p y : J) :
    ((∀ j, B j) × I × K) ≃ ((j : J) → B j × (j = p → I) × (j = y → K)) where
  toFun v j := (v.1 j, fun _ ↦ v.2.1, fun _ ↦ v.2.2)
  invFun z := (fun j ↦ (z j).1, (z p).2.1 rfl, (z y).2.2 rfl)
  left_inv _ := rfl
  right_inv z := by
    funext j
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    all_goals funext h; subst j; rfl

private def wirePairEquiv (H : Type) (s p : J) :
    (H × H) ≃ ((j : J) → (j = s → H) × (j = p → H)) where
  toFun v _ := (fun _ ↦ v.1, fun _ ↦ v.2)
  invFun z := ((z s).1 rfl, (z p).2 rfl)
  left_inv _ := rfl
  right_inv z := by
    funext j
    apply Prod.ext <;> funext h <;> subst j <;> rfl

namespace TwoMarkedNode

variable {I K H : Type} [Fintype I] [Fintype K] [Fintype H]
  (W : TwoMarkedNode k J I K) (op : H → H → I → I → k)

/-- Apply the matrix to the old marked leg at the row endpoint, using a wire to
supply the column index. Coincident endpoints are allowed. -/
theorem child_same_right_restriction (s p y : J) :
    Restricts (tensorProduct (W.place p y) (WireTensor.wire s p H))
      ((W.child s p op).place p y) := by
  let P := W.place p y
  let U := tensorProduct P (WireTensor.wire s p H)
  let V := (W.child s p op).place p y
  let L (j : J) (o : V.Basis j) (z : U.Basis j) : k :=
    (if o.1.1 = z.1.1 ∧ o.2.2 = z.1.2.2 ∧ o.1.2.1 = z.2.1 then 1 else 0) *
      (if h : j = p then op (o.1.2.2 h) (z.2.2 h) (o.2.1 h) (z.1.2.1 h) else 1)
  refine ⟨L, ?_⟩
  funext o
  let e : (((∀ j, W.Basis j) × I × K) × (H × H)) ≃ ((j : J) → U.Basis j) :=
    ((markedPairEquiv W.Basis I K p y).prodCongr (wirePairEquiv H s p)).trans
      (Equiv.arrowProdEquivProdArrow J P.Basis (WireTensor.wire (k := k) s p H).Basis).symm
  let f (z : (j : J) → U.Basis j) := (∏ j, L j (o j) (z j)) * U.coeff z
  let bg (j : J) := (o j).1.1
  let idx := (o p).2.1 rfl
  let second := (o y).2.2 rfl
  let col := (o s).1.2.1 rfl
  let row := (o p).1.2.2 rfl
  have eval (b : ∀ j, W.Basis j) (old : I) (v : K) (r t : H) :
      f (e ((b,old,v),(r,t))) =
        (if bg = b ∧ second = v ∧ col = r then 1 else 0) *
          op row t idx old * (W.coeff b old v * (if r = t then 1 else 0)) := by
    change (∏ j, (if (o j).1.1 = b j ∧ (o j).2.2 = (fun _ ↦ v) ∧ (o j).1.2.1 = (fun _ ↦ r)
      then (1 : k) else 0) *
        (if h : j = p then op ((o j).1.2.2 h) t ((o j).2.1 h) old else 1)) *
      (W.coeff b old v * (if r = t then 1 else 0)) = _
    rw [Finset.prod_mul_distrib, Fintype.prod_boole]
    have hp : (∀ j, (o j).1.1 = b j ∧ (o j).2.2 = (fun _ ↦ v) ∧ (o j).1.2.1 = (fun _ ↦ r)) ↔
        bg = b ∧ second = v ∧ col = r := by
      constructor
      · intro h
        exact ⟨funext (fun j ↦ (h j).1), congrFun (h y).2.1 rfl, congrFun (h s).2.2 rfl⟩
      · rintro ⟨rfl,rfl,rfl⟩ j
        refine ⟨rfl, ?_, ?_⟩
        all_goals funext h; subst j; rfl
    simp only [hp]
    rw [Fintype.prod_dite_eq']
  change (∑ z, f z) = V.coeff o
  rw [← e.sum_comp f]
  simp_rw [Fintype.sum_prod_type, eval]
  simp [ite_mul, mul_ite, ite_and, V, place, twoMarked, child, bg, col, row, idx, second,
    mul_comm]

/-- At the column endpoint, swap the two exterior legs before applying the matrix. -/
theorem child_same_left_restriction (s p y : J) :
    Restricts (tensorProduct (W.place s y) (WireTensor.wire s p H))
      ((W.child s p op).place s y) := by
  have h := W.child_same_right_restriction (fun α β ↦ op β α) p s y
  refine ((Restricts.refl _).tensorProduct (wire_swap s p H).1).trans (h.trans ?_)
  let P := (W.child p s (fun α β ↦ op β α)).place s y
  let V := (W.child s p op).place s y
  let e (j : J) : V.Basis j ≃ P.Basis j :=
    { toFun z := ((z.1.1, z.1.2.2, z.1.2.1), z.2)
      invFun z := ((z.1.1, z.1.2.2, z.1.2.1), z.2)
      left_inv _ := rfl
      right_inv _ := rfl }
  exact (restricts_of_reindex (T := P) (U := V) e (fun _ ↦ rfl)).1

/-- Both operators can act at either endpoint. The single exterior wire costs
its dimension raised to the distance between the two fixed endpoints. -/
theorem value_child_same_le (F : SpectralPoint k J) (s p x y : J) (hx : x = s ∨ x = p)
    (hH : 0 < Fintype.card H) :
    (F.value ((W.child s p op).place x y) : ℝ) ≤
      (F.value (W.place x y) : ℝ) * (Fintype.card H : ℝ) ^ F.wireDistance s p := by
  have h : Restricts (tensorProduct (W.place x y) (WireTensor.wire s p H))
      ((W.child s p op).place x y) := by
    rcases hx with rfl | rfl
    · exact W.child_same_left_restriction op _ _ _
    · exact W.child_same_right_restriction op _ _ _
  have hb := NNReal.coe_le_coe.mpr (F.monotone h)
  rwa [F.value_tensorProduct, NNReal.coe_mul, F.value_wire_equiv _ _ (Fintype.equivFin H),
    F.value_wire_eq_rpow _ _ hH] at hb

end TwoMarkedNode
end WireTensor

end VPVNP
end Computability
end OAI
