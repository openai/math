import OAI.Computability.BorderVNP.DiagonalCommonBranch
import OAI.Computability.BorderVNP.CubeTableSpecialization

/-! # Joint finite table, chart and advice bounds before the live pin choice -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing MvPolynomial Branch VPVNP
open scoped Classical

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]

/-- Scalar storage for the fixed tables and the advised chart rows, including
the output offset of each weighted row. One extra bit per field word allows a
positive word width. The chart index and its pinned-coordinate mask are counted
in the final summand. -/
noncomputable def chartBitBudget (u h fieldBits primeBits : ℕ) : ℕ :=
  primeBits + (u + h*(h+3)+1)*(fieldBits+1) + 2*(h+1)

private theorem field_clog_of_card {p B f : ℕ} (hf : f ≤ p^B) :
    Nat.clog 2 f ≤ Nat.clog 2 p * B := by
  apply Nat.clog_le_of_le_pow
  rw [pow_mul]
  exact hf.trans (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) B)

/-- For all lengths and every field of a fixed characteristic, a small border
circuit yields one common finite scalar field, one nonsingular arithmetic
branch and a polynomial bound for the scalar data, before any pin is selected. -/
theorem joint_advice_of_borderApprox (q : ℕ) [CharP K q]
    (G : PaidIdentity K D m) (aux : ι → K) :
    ∃ A C : ℕ, ∀ (k s : ℕ) (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
      (F : Type u) [Field F] [CharP F q],
      BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
        ∃ (R : CommonField G aux q k s ord) (chart : AdvisedBranch R),
          chartBitBudget (Fintype.card (G.Entry ⊕ ι)) (pairedTableParameters (k+1) s)
            (Nat.clog 2 (Nat.card chart.E)) (Nat.clog 2 R.p) ≤ A*(2*(k+1)+s+2)^C := by
  obtain ⟨B,A,C,select⟩ := commonField_of_borderApprox.{u,v} q G aux
  obtain ⟨a,c,choice⟩ := uniform_paired_choice_bits
  let u := Fintype.card (G.Entry ⊕ ι)
  let prime (M : ℕ) := A*M^C
  let field (M : ℕ) := prime M * B + a*(M+1)^c
  let h (M : ℕ) := M*M + M^2*M^3
  let bound (M : ℕ) := chartBitBudget u (h M) (field M) (prime M)
  have hi := PolynomiallyBounded.id
  have hp : PolynomiallyBounded prime := (PolynomiallyBounded.const A).mul (hi.pow C)
  have hf : PolynomiallyBounded field :=
    (hp.mul (PolynomiallyBounded.const B)).add ((PolynomiallyBounded.const a).mul ((hi.add (PolynomiallyBounded.const 1)).pow c))
  have hh : PolynomiallyBounded h := (hi.mul hi).add ((hi.pow 2).mul (hi.pow 3))
  have hb : PolynomiallyBounded bound :=
    (hp.add ((((PolynomiallyBounded.const u).add (hh.mul (hh.add (PolynomiallyBounded.const 3)))).add (PolynomiallyBounded.const 1)).mul
      (hf.add (PolynomiallyBounded.const 1)))).add ((PolynomiallyBounded.const 2).mul (hh.add (PolynomiallyBounded.const 1)))
  obtain ⟨a',c',upper⟩ := hb.exists_global_bound
  refine ⟨a',c',?_⟩
  intro k s ord F _ _ hp'
  obtain ⟨R,hbase,hprime⟩ := select k s ord F hp'
  obtain ⟨chart,he⟩ := R.exists_advisedBranch
  let M := 2*(k+1)+s+1
  have h₁ : pairedTableParameters (k+1) s ≤ h M := by
    refine (pairedTableParameters_le ..).trans ?_
    have hn : k+1 ≤ M := by dsimp [M]; omega
    have h2 : 2*(k+1) ≤ M := by dsimp [M]; omega
    change M*(2*(k+1)) + (k+1)^2*M^3 ≤ M*M + M^2*M^3
    gcongr
  have h₂ : Nat.clog 2 (Nat.card chart.E) ≤ field M := by
    refine he.trans (Nat.add_le_add ?_ (choice M (k+1) s (by dsimp [M]; omega) (by dsimp [M]; omega)))
    exact (field_clog_of_card hbase).trans (Nat.mul_le_mul_right _ hprime)
  refine ⟨R,chart,?_⟩
  calc
    _ ≤ bound M := by
      dsimp only [bound, chartBitBudget, u]
      gcongr
    _ ≤ _ := upper M

variable {a b h copies width : ℕ}

/-- The common finite chart field also realizes the fixed cube table identity,
at the exact same scalar addresses used in the diagonal tally. -/
theorem AdvisedBranch.cube_tables {G : PaidIdentity K D m}
    {x : Cube.TableEntry a b h copies width → K} (hx : Cube.ValidTables x)
    {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField G x q k s ord}
    (chart : AdvisedBranch R) :
    Cube.ValidTables (fun j => algebraMap R.E₀ chart.E (R.entry (Sum.inr j))) :=
  hx.specializeWith G (algebraMap R.E₀ chart.E ∘ R.entry) chart.preserves_tables

end Diagonal

end BorderVNP
end Computability
end OAI
