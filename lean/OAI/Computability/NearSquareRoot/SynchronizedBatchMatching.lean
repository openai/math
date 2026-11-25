import OAI.Computability.NearSquareRoot.SynchronizedRoutingEmbedding
import OAI.Computability.NearSquareRoot.SynchronizedPlacementAddress
import OAI.Computability.NearSquareRoot.SynchronizedDilationPairs

/-! # Active half-Walsh pairs on the physical padded borrowing block -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

open SynchronizedBorrowing

variable {a b c r : ℕ}

/-- Serialize the fiber coordinate first and the padded column coordinate second. -/
def rowMajor : Fin b × (Fin a ⊕ Fin c) ≃ Fin (b*(a+c)) :=
  (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv).trans finProdFinEquiv

/-- Map both members of every active half-Walsh pair to their allocated physical cells. -/
def batchEndpoints (hr : 2*r ≤ 8*a) (har : a ≤ r) (j : Fin 15) :
    Fin 2 × Fin (size b j*r) ↪ Fin (b*(a+c)) where
  toFun p :=
    let q : Fin (size b j) × Fin r := finProdFinEquiv.symm p.2
    let cell := batchPlacement b j hr (q.1,auxiliaryLayout har (dilationAddress.symm (p.1,q.2)))
    rowMajor (cell.1, Sum.inl cell.2)
  inj' := by
    rintro ⟨u,s⟩ ⟨v,t⟩ he
    obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective s
    obtain ⟨⟨i',y⟩,rfl⟩ := finProdFinEquiv.surjective t
    simp only [Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq,Sum.inl.injEq] at he
    obtain ⟨hi,hbit⟩ := Prod.mk.inj ((batchPlacement b j hr).injective (Prod.ext he.1 he.2))
    obtain ⟨hb,ht⟩ := Prod.mk.inj (dilationAddress.symm.injective ((auxiliaryLayout har).injective hbit))
    subst_vars
    rfl

/-- One arithmetic query per endpoint. The final row stride includes the padded columns. -/
def endpointValue (start v a c r side row col : ℕ) : ℕ :=
  let raw := physicalRank start v a r row (side*r+col)
  raw%a + (a+c)*(raw/a)

theorem batchEndpoints_val (hr : 2*r ≤ 8*a) (har : a ≤ r) (j : Fin 15)
    (u : Fin 2) (i : Fin (size b j)) (x : Fin r) :
    (batchEndpoints (c := c) hr har j (u,finProdFinEquiv (i,x))).val =
      endpointValue (first b j) (size b j) a c r u.val i.val x.val := by
  let t := dilationAddress.symm (u,x)
  let cell := batchPlacement b j hr (i,auxiliaryLayout har t)
  have h := batchPlacement_rank b j hr har i t
  change cell.2.val+a*cell.1.val = _ at h
  have ht : (finSumFinEquiv t).val = u.val*r+x.val := by
    fin_cases u <;> simp [t,dilationAddress,Nat.add_comm]
  rw [ht] at h
  have hm : (cell.2.val+a*cell.1.val)%a = cell.2.val := by simp [Nat.mod_eq_of_lt cell.2.isLt]
  have hd : (cell.2.val+a*cell.1.val)/a = cell.1.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt cell.2.isLt),Nat.div_eq_of_lt cell.2.isLt,Nat.zero_add]
  let place (p : Fin (size b j) × Fin r) :=
    let t' := batchPlacement b j hr (p.1,auxiliaryLayout har (dilationAddress.symm (u,p.2)))
    rowMajor (c := c) (t'.1, Sum.inl t'.2)
  change (place (finProdFinEquiv.symm (finProdFinEquiv (i,x)))).val = _
  rw [Equiv.symm_apply_apply]
  change cell.2.val+(a+c)*cell.1.val = _
  rw [endpointValue,← h,hm,hd]

/-- The generated full matching agrees with the mathematically placed half-Walsh pairs. -/
theorem match_batch (he : Even (b*(a+c))) (hr : 2*r ≤ 8*a) (har : a ≤ r) (j : Fin 15)
    (u : Fin 2) (i : Fin (size b j*r)) :
    let e := batchEndpoints (c := c) hr har j
    ∃ hi : i.val < b*(a+c)/2,
      matching he (activePairs e) (activePairs_nodup e) (u,⟨i.val,hi⟩) = e (u,i) :=
  pairAt _ he u i

end ShortFourier.RoutingTable

end NearSquareRoot
end Computability
end OAI
