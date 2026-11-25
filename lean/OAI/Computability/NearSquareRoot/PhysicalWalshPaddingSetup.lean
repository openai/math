import OAI.Computability.NearSquareRoot.PhysicalWalshPadding
import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingHeader
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth

/-! # The physical padded spectator array from compact width parameters

The machine is given two short unary bit counts and the marked data records.
It computes its extra-record count and produces the entire padded array with
one saved tally for the final truncation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Padding

open IntegerMultiplication Code Space
open PaddingHeader (extra)

/-- Every added cell belongs to a complete spectator row. -/
theorem total (A : ℕ) {W k s : ℕ} (hW : 0 < W) (hs : s ≤ k) :
    2^k + extra A W k s = WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s)*2^s := by
  have original : 2^k = 2^(k-s)*2^s := by rw [← pow_add, Nat.sub_add_cancel hs]
  rw [extra, original, ← Nat.add_mul, Nat.add_sub_of_le (WalshPadding.rows_le_paddedRows hW)]

private theorem compactCost (C d : ℕ) : ∃ L : ℕ, ∀ k s, s ≤ k → C*(k+s+1)^d ≤ L*2^k := by
  obtain ⟨B,hB⟩ := polynomial_le_multiple_array_length d
  refine ⟨C*2^d*B,fun k s hs => ?_⟩
  calc
    C * (k+s+1)^d ≤ C*(2*(k+1))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (C*2^d)*(k+1)^d := by rw [mul_pow,Nat.mul_assoc]
    _ ≤ (C*2^d)*(B*2^k) := Nat.mul_le_mul_left _ (hB k)
    _ = _ := (Nat.mul_assoc ..).symm

variable {I : Type}

/-- Under the occupancy bound, the compact header, all zero copies and the
saved original-length tally are charged to the original array's bit volume. -/
theorem appendFromWidths (A W : ℕ) (k s w : I → ℕ) (xs : (i : I) → List (Dusk.Grain (w i)))
    (len : ∀ i, (xs i).length = 2^k i) (sel : ∀ i, s i ≤ k i)
    (occ : ∀ i, extra A W (k i) (s i) ≤ 2^k i) :
    let V i := 2^k i*(w i+1)
    BoundedTask V V (fun i => send ((tally (k i),tally (s i)),(xs i).map Dusk.mark))
      (fun i => send (tally (2^k i),padded (extra A W (k i) (s i)) (xs i))) := by
  intro V
  obtain ⟨d,C,h⟩ := PaddingHeader.countsTask A W
  obtain ⟨L,compact⟩ := compactCost C d
  let E (i : I) := extra A W (k i) (s i)
  have header := (h.on fun i => (k i,s i)).left (fun i => send ((xs i).map Dusk.mark))
  have work := appendZeros w E xs (fun i hnil => by
    have eq := len i; rw [hnil, List.length_nil] at eq; exact (Nat.two_pow_pos _).ne eq)
  simp only [len] at work
  have chain := header.compose work
  apply chain.bound (L+10) (L+22) <;> intro i
  all_goals
    have hn : 0 < (2:ℕ)^k i := Nat.two_pow_pos _
    have nv : 2^k i ≤ V i := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have he : E i ≤ 2^k i := occ i
    have t := (compact _ _ (sel i)).trans (Nat.mul_le_mul_left L nv)
    have span : (2^k i+E i+1)*(w i+1) ≤ 3*V i := by
      apply (Nat.mul_le_mul_right (w i+1) (show 2^k i+E i+1 ≤ 3*2^k i by omega)).trans_eq
      exact Nat.mul_assoc ..
    have raw : size ((xs i).map Dusk.mark) ≤ 9*V i := by
      rw [marks_size,len]; dsimp only [V]; ring_nf; omega
  · change C*(k i+s i+1)^d+E i+2^k i+((2^k i+E i+1)*(w i+1))+1 ≤ (L+10)*(V i+1)
    conv_rhs => rw [Nat.add_mul, Nat.mul_add L, Nat.mul_one]
    omega
  · change max (C*(k i+s i+1)^d+E i+2^k i+size ((xs i).map Dusk.mark))
      ((2^k i+E i+1)*(w i+1))+1 ≤ (L+22)*(V i+1)
    conv_rhs => rw [Nat.add_mul, Nat.mul_add L, Nat.mul_one]
    omega

/-- The sparsity condition alone implies the occupancy hypotheses for both
physical boundary passes, uniformly over the number and width of records. -/
theorem sparse {A W : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ (k s w : I → ℕ), (∀ i, K ≤ k i) →
      (∀ i, (s i : ℝ) ≤ c*k i / Real.log (2+k i)) →
      ∀ xs : (i : I) → List (Dusk.Grain (w i)), (∀ i, (xs i).length = 2^k i) →
      let V i := 2^k i*(w i+1)
      BoundedTask V V (fun i => send ((tally (k i),tally (s i)),(xs i).map Dusk.mark))
        (fun i => send (tally (2^k i),padded (extra A W (k i) (s i)) (xs i))) ∧
      ∀ ys : (i : I) → List (Dusk.Grain (w i)),
        (∀ i, (ys i).length = 2^k i+extra A W (k i) (s i)) →
        BoundedTask V V (fun i => send (tally (2^k i),(ys i).map Dusk.mark))
          (fun i => send (((ys i).take (2^k i)).map Dusk.mark)) := by
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (WalshPadding.eventually_paddedRows_bound hA hW c hc)
  obtain ⟨K',hK'⟩ := Filter.eventually_atTop.mp (WalshPadding.eventually_twice_selected_le c hc)
  refine ⟨max K K', fun k s w hk compact xs len => ?_⟩
  have sel (i : I) : s i ≤ k i := by
    have := hK' _ ((le_max_right ..).trans (hk i)) (s i) (compact i); omega
  have he (i : I) : extra A W (k i) (s i) ≤ 2^k i := by
    have t := (hK _ ((le_max_left ..).trans (hk i)) (s i) (compact i)).2.2.2.2
    rw [← total A hW (sel i)] at t
    omega
  refine ⟨appendFromWidths A W k s w xs len sel he,fun ys hys => ?_⟩
  have tr := truncate w (fun i => 2^k i) ys (fun i => (hys i) ▸ Nat.le_add_right ..)
  apply tr.bound 3 3 <;> intro i <;> rw [hys i] <;>
    have sz : 2^k i + extra A W (k i) (s i) + 1 ≤ 3*(2^k i) := by
      have := he i; have := Nat.two_pow_pos (k i); omega
  all_goals
    have t := Nat.mul_le_mul_right (w i+1) sz
    rw [Nat.mul_assoc] at t
    omega

end PhysicalWalsh.Padding

end NearSquareRoot
end Computability
end OAI
