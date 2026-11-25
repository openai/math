import OAI.Computability.MultitapeWeakETH.Valuation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Defs

/-! # Recovering the two shifted copies of the common payload -/

namespace OAI.Computability.MultitapeWeakETH

open scoped BigOperators Fin.NatCast Fin.CommRing

/-- Before the cap is reached the number of trailing zeros gives an exact
power of two times an odd residue. -/
theorem trailing_odd_factor (n x : ℕ) (uncapped : trailing n x < n) :
    ∃ d, Odd d ∧ x = 2^(trailing n x)*d := by
  induction n generalizing x with
  | zero => simp [trailing] at uncapped
  | succ n ih =>
    by_cases even : x%2 = 0
    · simp only [trailing,even,ite_true,Nat.add_lt_add_iff_right] at uncapped
      obtain ⟨d,odd,eq⟩ := ih (x/2) uncapped
      refine ⟨d,odd,?_⟩
      simp only [trailing,even,ite_true,pow_succ]
      calc
        x = 2*(x/2) := by omega
        _ = 2*(2^(trailing n (x/2))*d) := congrArg (2*·) eq
        _ = _ := by ring
    · refine ⟨x,⟨x/2,by omega⟩,?_⟩
      simp [trailing,even]

/-- Odd multiplication on the low L bits permutes the payloads. -/
noncomputable def oddMultiplier (L d : ℕ) (odd : Odd d) : Fin (2^L) ≃ Fin (2^L) :=
  Equiv.ofBijective (fun x => ⟨(d*x.val)%(2^L),Nat.mod_lt _ (by positivity)⟩)
    (Finite.injective_iff_bijective.mp (by
      intro x y h
      apply Fin.ext
      have eq : d*x.val ≡ d*y.val [MOD 2^L] := congrArg Fin.val h
      exact (eq.cancel_left_of_coprime ((Nat.coprime_two_left.mpr odd).pow_left L).gcd_eq_one).eq_of_lt_of_lt
        x.isLt y.isLt))

/-- A bit interval lying entirely below n can be read directly before
truncation to n bits. -/
theorem payload_interval (m s L n : ℕ) (fits : s+L ≤ n) :
    (m % (2^n) / 2^s) % (2^L) = (m/2^s) % (2^L) := by
  have split : 2^n = 2^(n-s)*2^s := by rw [← pow_add]; congr 1; omega
  rw [split,Nat.mod_mul_left_div_self,Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]

/-- The corrected column differences yield the same word in their two
possibly unaligned bit intervals. Multiplying the retained low input bits
by the odd part of the difference is a bijection. -/
theorem shifted_payload {n s u L d : ℕ} (odd : Odd d) (fits : s+u+L ≤ n)
    (x delta delta' : Fin (2^n)) (factor : delta.val = 2^s*d)
    (shifted : delta' = 2^u*delta) :
    let low : Fin (2^L) := ⟨x.val % (2^L),Nat.mod_lt _ (by positivity)⟩
    let w := oddMultiplier L d odd low
    ((x*delta).val / 2^s) % (2^L) = w.val ∧
      ((x*delta').val / 2^(s+u)) % (2^L) = w.val := by
  intro low w
  have output : w.val = (x.val*d)%(2^L) := by
    change (d*(x.val % (2^L))) % (2^L) = _
    rw [Nat.mul_mod_mod,Nat.mul_comm]
  have repr : x*delta = ((2^s*(x.val*d) : ℕ) : Fin (2^n)) := by
    apply Fin.ext
    rw [Fin.val_mul,Fin.val_natCast,factor]
    congr 1; ring
  have shiftedRepr : x*delta' = ((2^(s+u)*(x.val*d) : ℕ) : Fin (2^n)) := by
    rw [shifted,show x*(2^u*delta) = 2^u*(x*delta) by ring,repr]
    push_cast; ring
  constructor
  · rw [repr,Fin.val_natCast,payload_interval _ _ _ _ (by omega),
      Nat.mul_div_cancel_left _ (by positivity),output]
  · rw [shiftedRepr,Fin.val_natCast,payload_interval _ _ _ _ fits,
      Nat.mul_div_cancel_left _ (by positivity),output]

/-- Split an n-bit word into its high and low parts, indexed from the
least significant end. -/
def joinPayload (n L : ℕ) (fits : L ≤ n) :
    Fin (2^(n-L)) × Fin (2^L) ≃ Fin (2^n) :=
  finProdFinEquiv.trans (finCongr (by rw [← pow_add,Nat.sub_add_cancel fits]))

/-- Fixing one high part preserves the density of good rows. Their odd
multiples form a payload set of cardinality at least q times 2^L. -/
theorem fix_high_payload {n L d : ℕ} (fits : L ≤ n) (odd : Odd d)
    (good : Fin (2^n) → Bool) {q : ℝ}
    (density : q ≤ 𝔼 x, if good x then (1:ℝ) else 0) :
    ∃ high : Fin (2^(n-L)),
      let lows := Finset.univ.filter (fun low => good (joinPayload n L fits (high,low)))
      q*(2:ℝ)^L ≤ ((lows.image (oddMultiplier L d odd)).card:ℝ) := by
  classical
  let weight (x : Fin (2^n)) : ℝ := if good x then 1 else 0
  let split := joinPayload n L fits
  have law := Fintype.expect_equiv split (fun p => weight (split p)) weight (fun _ => rfl)
  have nested : (𝔼 p, weight (split p)) = 𝔼 h, 𝔼 l, weight (split (h,l)) := by
    rw [← Finset.expect_product']; simp
  obtain ⟨h,_,best⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (density.trans (law.symm.trans nested).le)
  refine ⟨h,?_⟩
  dsimp only
  rw [Finset.card_image_of_injective _ (oddMultiplier L d odd).injective]
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at best
  have amount := (le_div_iff₀ (show (0:ℝ) < 2^L by positivity)).mp best
  simpa [weight,split,Finset.sum_boole] using amount

end OAI.Computability.MultitapeWeakETH
