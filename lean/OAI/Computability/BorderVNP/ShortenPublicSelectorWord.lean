import OAI.Computability.BorderVNP.ShortenPublicPaddedWords
import OAI.Computability.BorderVNP.CoverDeckPackWidth

/-!
# One public word for geometric counts and the conditional-choice scores

The charge comparisons square populations and multiply by the product-cover
volume. A fixed multiple of the common processor address width accommodates
these scores as well as the stable site and edge pointers. Its sorting pad
only enters the physical circuit size through its logarithm.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open TeamScales Cover.AddressCircuit

/-- The expanded per-tile record bound supplies the selector's maximum
candidate-cell count, including all currently uncharged physical cables. -/
theorem selector_count_bound {D : ℕ} {P Tile : Type*} [Fintype P] [Fintype Tile] {bits : P → ℕ}
    (N : Crossing.Network D P bits) (tile : N.Site → Tile) (prior payload : N.Site → ℕ) (cap n r : ℕ)
    (hc : ∀ t, localRecords N true prior payload (fun v => tile v=t) ≤ cap)
    (hv : Fintype.card Tile ≤ 2*n*r) (hl : cap ≤ 2*n*r) :
    (∑ e, N.width e) ≤ (2*n*r)^2 :=
  (totalWidth_le_records N tile prior payload cap hc).trans (by simpa [sq] using Nat.mul_le_mul hv hl)

/-- Numerical range of the actual candidate comparator, including its sorting
pad and the stable-row names passed through its public front end. -/
theorem selector_word_ranges (n r vol P fan H rows sites : ℕ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hvol : vol ≤ 2*n*r) (hp : P ≤ 2*n*r)
    (hk : fan ≤ 2*n*r) (hc : H ≤ (2*n*r)^2) (he : rows ≤ 2*n*r) (hv : sites ≤ 2*n*r) :
    let W := 60*logWidth r n
    let T := 2^W
    P < T ∧ H < T ∧ packRunWidth vol P fan H ≤ W ∧ rows ≤ T ∧ sites ≤ T ∧
      W ≤ Nat.clog 2 (T+1) ∧ Nat.clog 2 (T+vol+2)+1 ≤ W+3 := by
  intro W T
  let U := 2*n*r
  let L := logWidth r n
  have hU : 2 ≤ U := by dsimp [U]; nlinarith [Nat.mul_le_mul hn hr]
  have hu1 : 1 ≤ U := by omega
  have usq : U ≤ U^2 := by simpa [sq] using Nat.le_mul_of_pos_right U (by omega : 0 < U)
  have sCap : vol+P+fan+H+2 ≤ U^5 := by
    have five : 5 ≤ U^3 := (by decide : 5 ≤ (2:ℕ)^3).trans (Nat.pow_le_pow_left hU _)
    calc
      _ ≤ 5*U^2 := by change H ≤ U^2 at hc; omega
      _ ≤ U^3*U^2 := Nat.mul_le_mul_right _ five
      _ = _ := (pow_add U 3 2).symm
  have base : U ≤ 2^L := by
    rw [show L = Nat.clog 2 U from public_logWidth n r]
    exact Nat.le_pow_clog (by decide) _
  have logarithm : Nat.clog 2 (vol+P+fan+H+2) ≤ 5*L := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.mul_comm,pow_mul]
    exact sCap.trans (Nat.pow_le_pow_left base _)
  have pack : packWidth vol P fan H ≤ W :=
    (packWidth_le _ _ _ _).trans (by change 12*_ ≤ 60*L; omega)
  obtain ⟨pf,hf,run⟩ := packWidth_fits vol P fan H
  have lift : 2^packWidth vol P fan H ≤ T := Nat.pow_le_pow_right (by decide) pack
  have ulim : U ≤ T := base.trans (Nat.pow_le_pow_right (by decide) (by change L ≤ 60*L; omega))
  have pad : W ≤ Nat.clog 2 (T+1) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr (Nat.lt_succ_self T) |>.le
  have depth : Nat.clog 2 (T+vol+2) ≤ W+2 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    change T+vol+2 ≤ T*4
    omega
  exact ⟨pf.trans_le lift,hf.trans_le lift,run.trans pack,he.trans ulim,hv.trans ulim,pad,by omega⟩

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
