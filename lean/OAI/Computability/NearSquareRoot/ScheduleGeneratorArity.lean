import OAI.Computability.NearSquareRoot.ScheduleGeneratorBounds
import OAI.Computability.NearSquareRoot.InterchangeRecurrence

/-! # Effective choice of a contracting interchange arity -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open Filter

/-- Restricting the cofinal search to perfect powers with the common denominator
as exponent makes both real powers in the recurrence exact natural numbers. -/
private theorem perfectPower (b p d : ℕ) (hd : 0 < d) :
    (((b^d : ℕ) : ℝ) ^ ((p:ℝ) / d)) = (b^p : ℕ) := by
  have nz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have prod : (d:ℝ)*((p:ℝ)/d) = (p:ℝ) := by field_simp
  rw [Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _),prod,Real.rpow_natCast,
    Nat.cast_pow]

/-- A computable reserve-width construction and its asymptotic upper bound yield
a single computable choice of stage arity for all rational target exponents.
The constant and growth exponent in the reserve-width estimate need not be computed. -/
theorem choose_arity (accept : ℕ → ℕ → Bool) (haccept : Computable₂ accept)
    (regular : ∀ j, ∀ᶠ m : ℕ in atTop, accept j m = true) (a : ℕ → ℕ → ℕ) (ha : Computable₂ a)
    (d g p : ℕ → ℕ) (hd : Computable d) (hg : Computable g) (hp : Computable p)
    (den : ∀ j, 0 < d j) (ordered : ∀ j, g j < p j)
    (reserve : ∀ j, ∃ β D : ℝ, β ≤ (g j : ℝ) / d j ∧ 0 ≤ D ∧
      ∀ᶠ m : ℕ in atTop, (a j m : ℝ) ≤ D*(m:ℝ)^β) :
    ∃ m : ℕ → ℕ, Computable m ∧ ∀ j, accept j (m j) = true ∧ 2 ≤ m j ∧
      2*(m j : ℝ)^((g j : ℝ)/d j) + 2*a j (m j) < (m j : ℝ)^((p j : ℝ)/d j) := by
  let test (j b : ℕ) := decide (2 ≤ b) &&
    decide (2*b^(g j) + 2*a j (b^(d j)) < b^(p j))
  have htest : Computable₂ test := by
    have natPower := primrecNatPow.to_comp
    exact Primrec.and.to_comp.comp
      (Primrec.nat_le.decide.to_comp.comp (Computable.const 2) Computable.snd)
      (Primrec.nat_lt.decide.to_comp.comp
        (Primrec.nat_add.to_comp.comp
          (Primrec.nat_mul.to_comp.comp (Computable.const 2)
            (natPower.comp Computable.snd (hg.comp Computable.fst)))
          (Primrec.nat_mul.to_comp.comp (Computable.const 2)
            (ha.comp Computable.fst (natPower.comp Computable.snd (hd.comp Computable.fst)))))
        (natPower.comp Computable.snd (hp.comp Computable.fst)))
  have large (j b : ℕ) (hb : 2 ≤ b) : b ≤ b^(d j) := le_self_pow₀ (by omega) (den j).ne'
  have pass (j b : ℕ) : test j b = true ↔ 2 ≤ b ∧
      2*((b^(d j):ℕ):ℝ)^((g j:ℝ)/d j) + 2*a j (b^(d j)) <
      ((b^(d j):ℕ):ℝ)^((p j:ℝ)/d j) := by
    simp only [test,Bool.and_eq_true,decide_eq_true_eq,perfectPower _ _ _ (den j)]
    exact_mod_cast Iff.rfl
  let both (j b : ℕ) := accept j (b^(d j)) && test j b
  have checkBoth : Computable₂ both := Primrec.and.to_comp.comp
    (haccept.comp Computable.fst (primrecNatPow.to_comp.comp Computable.snd (hd.comp Computable.fst))) htest
  have exists_pass (j : ℕ) : ∃ b, both j b = true := by
    obtain ⟨β,D,hβ,hD,hr⟩ := reserve j
    have pos : (0:ℝ) < d j := by exact_mod_cast den j
    have ord : (g j : ℝ) / d j < (p j : ℝ) / d j :=
      (div_lt_div_iff_of_pos_right pos).2 (by exact_mod_cast ordered j)
    obtain ⟨cut,hcut⟩ := eventually_atTop.mp (eventually_interchange_contraction (a j) ord hβ hD hr)
    obtain ⟨extra,hextra⟩ := eventually_atTop.mp (regular j)
    let b := max (max cut extra) 2
    have hb : 2 ≤ b := le_max_right ..
    have big := (le_max_left (max cut extra) 2).trans (large j b hb)
    have yes := hextra _ ((le_max_right ..).trans big)
    have yes₂ := (pass j b).2 ⟨hb,hcut _ ((le_max_left ..).trans big)⟩
    exact ⟨b,by simp [both,yes,yes₂]⟩
  obtain ⟨base,eff,hbase⟩ := first_certificate both checkBoth exists_pass
  refine ⟨fun j => (base j)^(d j),primrecNatPow.to_comp.comp eff hd,fun j => ?_⟩
  have selected := (hbase j).1
  simp only [both,Bool.and_eq_true] at selected
  obtain ⟨extra,hmain⟩ := selected
  obtain ⟨hb,h⟩ := (pass j (base j)).1 hmain
  exact ⟨extra,hb.trans (large j _ hb),h⟩

end Generator

end NearSquareRoot
end Computability
end OAI
