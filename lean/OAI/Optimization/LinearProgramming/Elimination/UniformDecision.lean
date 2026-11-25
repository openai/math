import OAI.Optimization.LinearProgramming.Elimination.UniformMaskTable
import OAI.Optimization.LinearProgramming.Compression.UniformDetFrame
import OAI.Optimization.LinearProgramming.Compression.DetRamBits
import OAI.Optimization.LinearProgramming.PrimalDual.Bits

/-! A single fixed RAM program for deciding independence from an explicit live mask.
The same code and two work tables serve all inputs and dimensions, including zero. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression Matrix

/-- Compose the dimension-independent mask-table writer with the dimension-independent determinant. -/
def uniformMaskedDecision : Block :=
  .seq uniformMaskTable (uniformDetBlock uniformBirdCell)

def decisionCost (n : ℕ) : ℕ := maskTableCost n + 2000*(n+1)^7

theorem uniformMaskedDecision_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (S : Finset (Fin n)) (hN : m.index 0=n)
    (hzero : m.index 14=0) (hG : 7 ≤ m.index 17) (hf : 7 ≤ m.index 18) (ho : 7 ≤ m.index 1)
    (hgo : m.index 17+n*n ≤ m.index 1) (hfo : m.index 18+n ≤ m.index 1)
    (hw1 : m.index 1+n*n ≤ m.index 11) (hw2 : m.index 11+n*n ≤ m.index 12)
    (hm : ∀ p, P (m.data p)) (h0 : P 0) (h1 : P 1) (hneg : ∀ x,P x → P (-x))
    (hflag : ∀ i : Fin n, m.data (m.index 18+i.val) = flag S i)
    (hreg : let T := maskGram (uniformMatrix n (m.index 17) m) (flag S)
      ∀ k<n, ∀ r : BirdRegister n, P (r.read T (birdLayer T k))) :
    ∃ t k, k ≤ decisionCost n ∧ Block.Eval (fun s => ∀p,P (s.data p)) uniformMaskedDecision m k t ∧
      t.data 6 = (maskGram (uniformMatrix n (m.index 17) m) (flag S)).det ∧
      (∀ a, 7 ≤ a → a < m.index 1 → t.data a = m.data a) ∧
      (∀ p, p ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ) → t.index p = m.index p) := by
  obtain ⟨u,c,hc,e,hmat,hframe,hi⟩ := uniformMaskTable_spec P m n S hN hzero hG hf ho hgo hfo hm h0 h1 hflag
  have f0 := hi 0 (by decide)
  have f1 := hi 1 (by decide)
  have f11 := hi 11 (by decide)
  have f12 := hi 12 (by decide)
  have f14 := hi 14 (by decide)
  obtain ⟨t,c',hc',e',hv,hd⟩ := uniformDetBlock_spec uniformBirdCell uniformBirdCell_spec P u n
    (f0.trans hN) (f1 ▸ ho) (by rw [f1,f11]; exact hw1) (by rw [f11,f12]; exact hw2)
    (f14.trans hzero) e.safe_end h0 h1 hneg (by rw [f1,hmat]; exact hreg)
  refine ⟨t,c+c',Nat.add_le_add hc hc',e.seq e',?_,?_,?_⟩
  · rwa [f1,hmat] at hv
  · intro a ha hlow
    rw [f11,f12] at hd
    exact (hd a ha (Or.inl (by omega)) (Or.inl (by omega))).trans (hframe a ha (Or.inl hlow))
  · intro p hp
    exact (uniformDet_address_frame e' p hp).trans (hi p (by simp_all))

private theorem maskGram_entry {K : Type*} [Field K] {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (S : Finset (Fin n)) (i j : Fin n) :
    maskGram G (flag S) i j = if i ∈ S ∧ j ∈ S then G i j else if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j; by_cases hi : i∈S <;> simp [flag,maskGram,hi]
  · by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [flag,maskGram,h,hi,hj]

/-- The determinant register budget needs only the size of the original Gram coefficients.
It can be reused unchanged on every candidate. -/
theorem masked_bird_bits {n B M : ℕ} (G : Matrix (Fin n) (Fin n) ℚ) (S : Finset (Fin n))
    (hG : ∀ i j, ratBits (G i j) ≤ B) (hb : 3 ≤ B) (hM : detRegisterBits n B ≤ M) :
    let T := maskGram G (flag S)
    ∀ k<n, ∀ r : BirdRegister n, ratBits (r.read T (birdLayer T k)) ≤ M := by
  let T := maskGram G (flag S)
  have hs (i j : Fin n) : ratBits (T i j) ≤ B := by
    rw [show T = maskGram G (flag S) from rfl,maskGram_entry]
    split
    · exact hG i j
    · split <;> exact hb
  change ∀k<n, ∀r : BirdRegister n, ratBits (r.read T (birdLayer T k)) ≤ M
  intro k hk r
  apply (birdRegister_bits T hs k r).trans
  apply LE.le.trans _ hM
  unfold detRegisterBits
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hk.le 2)) 3

end Elimination
end LinearProgramming
end Optimization
end OAI
