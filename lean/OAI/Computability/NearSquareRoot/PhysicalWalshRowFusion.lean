import OAI.Computability.NearSquareRoot.PrecisionFlatWalshNodeIdeal

/-! # Fusion of adjacent Walsh fields in packed order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open Matrix Finset FlatWalshKernel
noncomputable section

/-- Join high and low packed addresses, the low field varying fastest. -/
private def joinBits (hi lo : ℕ) : Fin (2^hi) × Fin (2^lo) ≃ Fin (2^(lo+hi)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add, Nat.mul_comm]))

private theorem join_val {hi lo : ℕ} (i : Fin (2^hi)) (j : Fin (2^lo)) :
    (joinBits hi lo (i,j)).val = 2^lo*i.val+j.val := by
  change j.val+2^lo*i.val = _
  omega

private theorem splitKernel {hi lo : ℕ} (u i : Fin (2^hi)) (v j : Fin (2^lo)) :
    BoxFin.flatWalsh univ (joinBits hi lo (u,v)) (joinBits hi lo (i,j)) =
      BoxFin.flatWalsh univ v j * BoxFin.flatWalsh univ u i := by
  rw [fullFlat, fullFlat, fullFlat, Fin.prod_univ_add]
  simp only [join_val, Fin.val_castAdd, Fin.val_natAdd,
    Nat.testBit_two_pow_mul_add _ v.isLt, Nat.testBit_two_pow_mul_add _ j.isLt]
  congr 1
  · apply prod_congr rfl
    intro p _
    simp [p.isLt]
  · apply prod_congr rfl
    intro p _
    simp

@[simp] theorem activeRow_zero (suffix : ℕ) (x : ℕ → ℂ) :
    activeRow 0 suffix x = x := by
  funext n
  unfold activeRow
  simp_rw [fullFlat]
  simp [Nat.div_add_mod']

/-- A high field followed by its adjacent low field is exactly the Walsh
transform on their concatenation, for every positive trailing stride. -/
theorem activeRow_fuse (hi lo suffix : ℕ) (hs : 0 < suffix) (x : ℕ → ℂ) :
    activeRow lo suffix (activeRow hi (2^lo*suffix) x) =
      activeRow (lo+hi) suffix x := by
  funext n
  let m := 2^(lo+hi)
  let b : Fin suffix := ⟨n%suffix, Nat.mod_lt _ hs⟩
  let r : Fin m := ⟨n/suffix%m, Nat.mod_lt _ (by dsimp [m]; positivity)⟩
  let g := n/suffix/m
  obtain ⟨⟨u,v⟩,hu⟩ := (joinBits hi lo).surjective r
  have hn : n = (g*2^(lo+hi)+(joinBits hi lo (u,v)).val)*suffix+b.val := by
    rw [hu]
    change n = (n/suffix/m*m + n/suffix%m)*suffix + n%suffix
    rw [Nat.div_add_mod' _ _, Nat.div_add_mod' _ _]
  have joinForm (i : Fin (2^hi)) (j : Fin (2^lo)) :
      (g*2^(lo+hi)+(joinBits hi lo (i,j)).val)*suffix+b.val =
        ((g*2^hi+i.val)*2^lo+j.val)*suffix+b.val := by rw [join_val,pow_add]; ring
  have regroup (i : Fin (2^hi)) (j : Fin (2^lo)) :
      ((g*2^hi+i.val)*2^lo+j.val)*suffix+b.val =
        (g*2^hi+i.val)*(2^lo*suffix)+(j.val*suffix+b.val) := by ring
  have tail (j : Fin (2^lo)) : j.val*suffix+b.val < 2^lo*suffix := by
    have h := Nat.mul_le_mul_right suffix j.isLt
    calc
      _ < j.val*suffix+suffix := Nat.add_lt_add_left b.isLt _
      _ = (j.val+1)*suffix := by rw [Nat.add_mul, one_mul]
      _ ≤ _ := h
  conv_lhs => arg 4; rw [hn, joinForm]
  conv_rhs => arg 4; rw [hn]
  rw [activeRow_at _ _ hs, activeRow_at _ _ hs]
  rw [← (joinBits hi lo).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [regroup]
  change _ * activeRow hi (2^lo*suffix) x
    ((g*2^hi+u.val)*(2^lo*suffix)+(⟨j.val*suffix+b.val,tail j⟩ : Fin (2^lo*suffix)).val) = _
  rw [activeRow_at _ _ (Nat.mul_pos (Nat.two_pow_pos _) hs), Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [splitKernel, joinForm,regroup,mul_assoc]

end
end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
