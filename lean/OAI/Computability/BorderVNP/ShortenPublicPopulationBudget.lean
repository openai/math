import OAI.Computability.BorderVNP.ShortenPublicPopulationNamed

/-! # Descriptor-linear population work in the paper's size parameters

The stable cover index grows exponentially with depth. Thus reading the
whole canonical quaternion key costs logarithmically many bits in the tile
count, even when the numerical key space contains many unused words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.AddressCircuit
open scoped Classical

/-- The sort, segmented additions and row masking take at most cubic work per padded lane. -/
theorem laneCost_le (b k w : ℕ) : laneCost b k w ≤ 200*(b+k+w+1)^3 := by
  unfold laneCost
  ring_nf
  omega

/-- The standard width for an expanded-size bound accommodates every bin's
actual width, including a bin containing all active bits. -/
theorem count_fits_expanded {D S w : ℕ} {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
    {A : Type} (bin : N.Edge → Option A) (total : (∑ e, N.width e) ≤ S)
    (words : Nat.clog 2 (S+1) ≤ w) (a : A) : SeedIntervals.count N bin a < 2^w := by
  rw [SeedIntervals.count_eq_sum]
  have hc : (∑ e, if bin e = some a then N.width e else 0) ≤ ∑ e, N.width e :=
    Finset.sum_le_sum fun _ _ => by split <;> omega
  exact (Nat.lt_succ_of_le (hc.trans total)).trans_le ((Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) words))

/-- Cover depth is bounded by the binary logarithm of the actual product tile count. -/
theorem depth_le_clog_tiles (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] (l : ℕ) :
    l ≤ Nat.clog 2 (Fintype.card (I → Deck l)) + 2 := by
  cases l with
  | zero => omega
  | succ l =>
    cases l with
    | zero => omega
    | succ l =>
      have hp : 2^l ≤ Fintype.card (Deck (l+2)) := by
        rw [← Nat.card_eq_fintype_card,deck_card,tileCount_eq]
        exact (Nat.pow_le_pow_left (by decide : 2 ≤ 7^3) _).trans
          (Nat.le_mul_of_pos_right _ tileCount_two_bounds.1)
      have hs : Fintype.card (Deck (l+2)) ≤ Fintype.card (I → Deck (l+2)) :=
        Fintype.card_le_of_injective (Function.const I) Function.const_injective
      have h := Nat.clog_mono_right 2 (hp.trans hs)
      rw [Nat.clog_pow _ _ (by decide)] at h
      exact Nat.add_le_add_right h 2

/-- For fixed motion costs, number of factors and relative bins, the exact batch cost is
linear in reserved descriptors plus tiles, times a polynomial in the logarithm of the
expanded bound and tile count. The expanded bound covers all rows and their word values. -/
theorem jointCost_polylog (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] (q bins C e : ℕ) :
    ∃ A p : ℕ, ∀ (d l w rows S : ℕ), d ≤ l → rows ≤ S → w ≤ Nat.clog 2 (S+1) →
      let V := Fintype.card (I → Deck l)
      let v := rows + V*bins
      let r := Nat.clog 2 bins
      1 + rows*(C*(d+1)^e) + (rows*r*(2*bins+1) + 2*(v+1)*laneCost (Nat.clog 2 v) (r+keyWidth q l) w) ≤
        (rows+V+1)*A*(Nat.clog 2 (S+V+2)+1)^p := by
  let r := Nat.clog 2 bins
  let K := Nat.clog 2 (bins+1) + r + 270*q + 4
  let A := 1 + C*3^e + r*(2*bins+1) + 400*(bins+1)*K^3
  refine ⟨A,max 3 e,?_⟩
  intro d l w rows S hd hrows hw V v
  let L := Nat.clog 2 (S+V+2)+1
  let N := rows+V+1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have depth := depth_le_clog_tiles I l
  have hvol := Nat.clog_mono_right 2 (show V ≤ S+V+2 by omega)
  have hdep : l+1 ≤ 3*L := by change l ≤ Nat.clog 2 V + 2 at depth; dsimp [L]; omega
  have hword : w ≤ L := by
    exact hw.trans ((Nat.clog_mono_right 2 (by omega : S+1 ≤ S+V+2)).trans (Nat.le_succ _))
  have count : v ≤ (bins+1)*(S+V+2) := by dsimp [v]; nlinarith only [hrows]
  have sort : Nat.clog 2 v ≤ Nat.clog 2 (bins+1) + Nat.clog 2 (S+V+2) := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    exact count.trans (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
  have hkey : keyWidth q l ≤ 270*q*L := by
    change q*(30*(l+1)*3) ≤ _
    calc
      _ = 90*q*(l+1) := by ring
      _ ≤ 90*q*(3*L) := Nat.mul_le_mul_left _ hdep
      _ = _ := by ring
  have words : Nat.clog 2 v+(r+keyWidth q l)+w+1 ≤ K*L := by
    have hs := Nat.le_mul_of_pos_right (Nat.clog 2 (bins+1)) hL
    have hr := Nat.le_mul_of_pos_right r hL
    have hx : Nat.clog 2 (S+V+2) ≤ L := Nat.le_succ _
    simp only [K,Nat.add_mul]
    omega
  have hc : laneCost (Nat.clog 2 v) (r+keyWidth q l) w ≤ 200*(K*L)^3 :=
    (laneCost_le ..).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left words _))
  have hpad : v+1 ≤ N*(bins+1) := by dsimp [N,v]; nlinarith
  have hrow : rows ≤ N := by dsimp [N]; omega
  have hn : 1 ≤ N := Nat.le_add_left _ _
  have hbase : d+1 ≤ 3*L := (Nat.add_le_add_right hd 1).trans hdep
  have hE : L^e ≤ L^(max 3 e) := Nat.pow_le_pow_right hL (le_max_right ..)
  have h3 : L^3 ≤ L^(max 3 e) := Nat.pow_le_pow_right hL (le_max_left ..)
  have h1 : 1 ≤ L^(max 3 e) := Nat.one_le_pow _ _ hL
  have hrun : rows*(C*(d+1)^e) ≤ N*(C*3^e)*L^(max 3 e) := by
    calc
      _ ≤ N*(C*(3*L)^e) := Nat.mul_le_mul hrow (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _))
      _ = N*(C*3^e)*L^e := by rw [mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hE
  have htag : rows*r*(2*bins+1) ≤ N*(r*(2*bins+1))*L^(max 3 e) := by
    calc
      _ ≤ N*r*(2*bins+1) := by gcongr
      _ = N*(r*(2*bins+1))*1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h1
  have hsort : 2*(v+1)*laneCost (Nat.clog 2 v) (r+keyWidth q l) w ≤
      N*(400*(bins+1)*K^3)*L^(max 3 e) := by
    calc
      _ ≤ 2*(N*(bins+1))*(200*(K*L)^3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hpad) hc
      _ = N*(400*(bins+1)*K^3)*L^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  have hone : 1 ≤ N*L^(max 3 e) := by simpa only [one_mul] using Nat.mul_le_mul hn h1
  change 1 + rows*(C*(d+1)^e) + (rows*r*(2*bins+1) + _) ≤ N*A*L^(max 3 e)
  calc
    _ ≤ N*L^(max 3 e) + N*(C*3^e)*L^(max 3 e) +
        (N*(r*(2*bins+1))*L^(max 3 e) + N*(400*(bins+1)*K^3)*L^(max 3 e)) :=
      Nat.add_le_add (Nat.add_le_add hone hrun) (Nat.add_le_add htag hsort)
    _ = N*A*L^(max 3 e) := by dsimp only [A]; ring

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
