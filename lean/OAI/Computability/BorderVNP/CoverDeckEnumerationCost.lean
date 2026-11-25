import OAI.Computability.BorderVNP.CoverDeckEnumeration

/-!
# Operation count for listing quaternion tile addresses

We count the multiplications used by the digit enumeration of Lemma 5.1.
A seventh power takes four products, using the square and cube as shared
values. Quaternion coordinates are residues with at most three bits per level.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- Compute successive seventh powers, recording the four multiplications in
each iteration. -/
def countedSeventh {M : Type*} [Monoid M] : ℕ → M → ℕ × M
  | 0, x => (0,x)
  | d+1, x =>
    let prior := countedSeventh d x
    let y := prior.2
    let square := y*y
    let cube := square*y
    (prior.1+4, (cube*cube)*y)

private theorem countedSeventh_spec {M : Type*} [Monoid M] (d : ℕ) (x : M) :
    countedSeventh d x = (4*d, seventhIterate d x) := by
  induction d with
  | zero => rfl
  | succ d h =>
    rw [countedSeventh,h,seventhIterate]
    refine Prod.ext (by dsimp; omega) ?_
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

/-- The digit enumeration with an exact multiplication counter. Each prefix
is multiplied by each precomputed digit at the current level. -/
def countedExpansion {M : Type*} [Monoid M] (first digits : List M) : ℕ → ℕ × List M
  | 0 => (0,first)
  | d+1 =>
    let prior := countedExpansion first digits d
    let powers := digits.map (countedSeventh d)
    let layer := powers.map Prod.snd
    let result := prior.2.flatMap (fun x => layer.map (x * ·))
    (prior.1 + (powers.map Prod.fst).sum + result.length, result)

/-- Removing the counters yields precisely the listed products. -/
theorem countedExpansion_values {M : Type*} [Monoid M] (a b : List M) (d : ℕ) :
    (countedExpansion a b d).2 = expandDigits a b d := by
  induction d with
  | zero => rfl
  | succ d h =>
    simp only [countedExpansion, expandDigits, h, List.map_map, Function.comp_def,
      countedSeventh_spec]

private theorem countedExpansion_step {M : Type*} [Monoid M] (a b : List M) (d : ℕ) :
    (countedExpansion a b (d+1)).1 = (countedExpansion a b d).1 +
      b.length*(4*d) + (expandDigits a b (d+1)).length := by
  simp only [countedExpansion, countedExpansion_values, List.map_map, Function.comp_def,
    countedSeventh_spec, expandDigits]
  change _ + (b.map (Function.const M (4*d))).sum + _ = _
  rw [List.map_const,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

/-- An output-sensitive bound on the number of modular products. The digit
table has 343 entries in the quaternion tower. -/
theorem countedExpansion_le {M : Type*} [Monoid M] (a b : List M)
    (ha : 0 < a.length) (hb : 0 < b.length) (d : ℕ) :
    (countedExpansion a b d).1 ≤ (4*b.length+1)*d^2*(expandDigits a b d).length := by
  induction d with
  | zero => simp [countedExpansion]
  | succ d ih =>
    let k := 4*b.length+1
    let n := (expandDigits a b (d+1)).length
    have hn : 0 < n := by dsimp [n]; rw [expand_length]; positivity
    have hlen : (expandDigits a b d).length ≤ n := by
      dsimp [n]
      rw [expand_length,expand_length,pow_succ,← mul_assoc]
      exact Nat.le_mul_of_pos_right _ hb
    have hcost : b.length*(4*d) ≤ k*d*n := calc
      _ = (4*b.length)*d := by ring
      _ ≤ k*d := Nat.mul_le_mul_right _ (by dsimp [k]; omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ hn
    have hk : 0 < k := by dsimp [k]; omega
    rw [countedExpansion_step]
    calc
      _ ≤ k*d^2*n + k*d*n + k*n :=
        Nat.add_le_add (Nat.add_le_add (ih.trans (Nat.mul_le_mul_left _ hlen)) hcost)
          (Nat.le_mul_of_pos_left n hk)
      _ = k*(d^2+d+1)*n := by ring
      _ ≤ k*(d+1)^2*n := by gcongr; nlinarith

/-- The concrete listing of all tiles at depth `d+2` with its modular
quaternion multiplication count. -/
noncomputable def countedAddresses (d : ℕ) : ℕ × List (Address (d+2)) :=
  countedExpansion (firstTable.map (coordinates (d+2))) (digitTable.map (coordinates (d+2))) d

/-- The concrete enumerator outputs the complete tile list using at most
`1373 * d²` modular quaternion multiplications per output tile. -/
theorem countedAddresses_spec (d : ℕ) :
    (countedAddresses d).2 = listAddresses d ∧
      (countedAddresses d).1 ≤ 1373*d^2*tileCount (d+2) := by
  refine ⟨countedExpansion_values .., ?_⟩
  have h := countedExpansion_le (firstTable.map (coordinates (d+2)))
    (digitTable.map (coordinates (d+2)))
    (by simpa only [List.length_map,first_length] using tileCount_two_bounds.1)
    (by simp [digit_length]) d
  change _ ≤ _ * d^2 * (listAddresses d).length at h
  simpa only [countedAddresses,List.length_map,digit_length,listAddresses_length,
    show 4*7^3+1 = 1373 by decide] using h

/-- Every modular quaternion coordinate fits into `3*l` bits at level `l`. -/
theorem residue_lt_bit_bound (l : ℕ) (r : ZMod (7^l)) : r.val < 2^(3*l) := by
  have h : (7:ℕ)^l ≤ (2^3)^l := Nat.pow_le_pow_left (by decide) _
  rw [← pow_mul] at h
  exact (ZMod.val_lt r).trans_le h

/-- Every tile occurs once in the list. The proof uses the faithful four-residue
representation, surjectivity onto the actual tiles, and the exact output length. -/
theorem listAddresses_nodup (d : ℕ) : (listAddresses d).Nodup := by
  classical
  have hcard : 0 < Nat.card (Deck (d+2)) := by
    rw [deck_card,tileCount_eq]
    exact Nat.mul_pos (by positivity) tileCount_two_bounds.1
  let := Nat.finite_of_card_ne_zero hcard.ne'
  let := Fintype.ofFinite (Deck (d+2))
  let L := (listAddresses d).toFinset
  let f : Deck (d+2) → L := fun t => ⟨_, List.mem_toFinset.mpr (listAddresses_complete d t)⟩
  have hi : Function.Injective f := fun _ _ h =>
    deckAddress_injective d.succ.succ (Units.ext (congrArg Subtype.val h))
  have he := Fintype.card_le_of_injective f hi
  rw [← Nat.card_eq_fintype_card,deck_card,← listAddresses_length,Fintype.card_coe] at he
  exact List.nodup_iff_le_length_dedup.mpr (by simpa only [L,List.card_toFinset] using he)

end Cover

end BorderVNP
end Computability
end OAI
