import OAI.Computability.VPVNP.MacaulayExponentISA
import OAI.Computability.VPVNP.MacaulayQueryBounds

/-!
# Bit-stack queries for the exponents in Macaulay entries

After ordinal lookup, the low radix block of each raw key contains the
actual exponents in variable order. The common word width accommodates both
index scans, the shift by one label, and the scaled source digit. Division
by the monomial, powered-row equality, and the requested exponent difference
are recovered in the original label order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ExponentISA

open RAMTape.RegisterTable

/-- Register width for the two index scans and the shifted exponent comparison. -/
def entryWidth (t L D scale mark request : ℕ) :=
  1 + Nat.clog 2 (2 + rawSize t L + rawSize t D + t + t*L + t*D +
    scale + scale*(L+1) + mark + request)

/-- Set the source and column radices to their degree bounds plus one and install the scaling,
marked coordinate and requested coordinate. -/
def params (L D scale mark request : ℕ) : Parameters := ⟨L+1,D+1,scale,mark,request⟩

private theorem width_bound (t L D scale mark request : ℕ) :
    2 + rawSize t L + rawSize t D + t + t*L + t*D + scale + scale*(L+1) + mark + request <
      2 ^ entryWidth t L D scale mark request := by
  let B := 2 + rawSize t L + rawSize t D + t + t*L + t*D + scale + scale*(L+1) + mark + request
  have h := Nat.le_pow_clog (b := 2) (by decide) B
  change B < 2^(1+Nat.clog 2 B)
  rw [pow_add]
  have := Nat.two_pow_pos (Nat.clog 2 B)
  omega

theorem indexFits {t L D scale mark request k₁ k₂ : ℕ}
    (h₁ : k₁ ≤ rawSize t L) (h₂ : k₂ ≤ rawSize t D) :
    let w := entryWidth t L D scale mark request
    ISA.Fits (ISA.graded t L k₁) w ∧ ISA.Fits (ISA.graded t D k₂) w ∧ Fits (params L D scale mark request) w := by
  let w := entryWidth t L D scale mark request
  have hw := width_bound t L D scale mark request
  have hb (d : ℕ) : d+1 ≤ rawSize t d := Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
  have hbox (d : ℕ) : (d+1)^t ≤ rawSize t d := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hL := hb L
  have hD := hb D
  have hboxL := hbox L
  have hboxD := hbox D
  constructor
  · constructor <;> (try dsimp [ISA.graded]) <;> omega
  constructor
  · constructor <;> (try dsimp [ISA.graded]) <;> omega
  · constructor <;> (try dsimp [params]) <;> omega

/-- Remove the degree digit of a raw graded monomial address. -/
def exponentBlock {t D : ℕ} (a : BoundedMonomial t D) : ℕ := (rawCode a).val % (D+1)^t

private theorem read_digit {t D : ℕ} (a : BoundedMonomial t D) (i : Fin t) :
    exponentBlock a / (D+1)^i.rev.val % (D+1) = a.val i := digit_rawCode a i

private theorem position {t : ℕ} (i : Fin t) : t - i.rev.val = i.val + 1 := by
  rw [Fin.val_rev]; have := i.isLt; omega

/-- The exponent at variable i after multiplying by the marked variable and raising the
resulting monomial to the indicated power. -/
def shifted {t : ℕ} (scale mark : ℕ) (source : Fin t → ℕ) (i : Fin t) :=
  scale * (source i + if i.val+1 = mark then 1 else 0)

/-- The fixed control returns the divisibility and equality tests in all
labels, and the difference exponent of any single requested label. -/
theorem row_run {t L D : ℕ} (a : BoundedMonomial t L) (b : BoundedMonomial t D)
    (scale mark request : ℕ) :
    let p := params L D scale mark request
    let w := entryWidth t L D scale mark request
    let input : Work := ⟨t,exponentBlock a,exponentBlock b,0,true,true,0,0⟩
    ∃ ticks ≤ (16*t+1)*(RAMTape.ISA.prepareBound w 0+3), ∃ out,
      UniversalCountStack.SpaceRun (code table) (w+(RAMTape.ISA.prepareBound w 0+3)) ticks
        (RAMTape.ISA.entry table 0) (bank Fin.elim0 0 (registers w p input))
        (RAMTape.ISA.entry table 17) (bank Fin.elim0 0 (registers w p out)) ∧
      (out.divides = true ↔ ∀ i, shifted scale mark a.val i ≤ b.val i) ∧
      (out.same = true ↔ ∀ i, shifted scale mark a.val i = b.val i) ∧
      ∀ i : Fin t, request = i.val+1 → out.residual = b.val i - shifted scale mark a.val i := by
  intro p w input
  have fit : Fits p w := (indexFits (Nat.zero_le (rawSize t L)) (Nat.zero_le (rawSize t D))).2.2
  have hw := width_bound t L D scale mark request
  have ha : exponentBlock a < 2^w := (Nat.mod_le ..).trans_lt <| (rawCode a).isLt.trans_le (by dsimp [w]; omega)
  have hb : exponentBlock b < 2^w := (Nat.mod_le ..).trans_lt <| (rawCode b).isLt.trans_le (by dsimp [w]; omega)
  have hs (i : Fin t) : scaledDigit p (t-i.rev.val) (exponentBlock a / p.sourceBase^i.rev.val) =
      shifted scale mark a.val i := by
    change scale * (exponentBlock a / (L+1)^i.rev.val % (L+1) + if t-i.rev.val = mark then 1 else 0) = _
    rw [position, read_digit]; rfl
  have hc (i : Fin t) : exponentBlock b / p.columnBase^i.rev.val % p.columnBase = b.val i := read_digit b i
  obtain ⟨ticks,ht,out,hphys,hdiv,heq,hread⟩ :=
    run_digits p fit (exponentBlock a) (exponentBlock b) (by dsimp [w]; omega : t < 2^w) ha hb
  have across (P : ℕ → Prop) : (∀ k < t, P k) ↔ ∀ i : Fin t, P i.rev.val := by
    constructor
    · exact fun h i => h _ i.rev.isLt
    · intro h k hk
      simpa using h (⟨k,hk⟩ : Fin t).rev
  refine ⟨ticks,ht,out,hphys,?_,?_,?_⟩
  · rw [hdiv, across]; simp only [hs, hc]
  · rw [heq, across]; simp only [hs, hc]
  · intro i hi
    simpa only [hs, hc] using hread i.rev.val i.rev.isLt (show p.request = _ from (position i).symm ▸ hi)

/-- The width of each register in the scalar entry tests is polynomially
bounded for polynomially many labels and polynomial-bit degree and scale inputs. -/
theorem entryWidth_polynomial {t L D scale mark request : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hL : PolynomiallyBounded (fun n => Nat.clog 2 (L n))) (hD : PolynomiallyBounded (fun n => Nat.clog 2 (D n)))
    (hS : PolynomiallyBounded (fun n => Nat.clog 2 (scale n)))
    (hM : PolynomiallyBounded (fun n => Nat.clog 2 (mark n)))
    (hR : PolynomiallyBounded (fun n => Nat.clog 2 (request n))) :
    PolynomiallyBounded (fun n => entryWidth (t n) (L n) (D n) (scale n) (mark n) (request n)) := by
  open PolynomiallyBounded in
    exact (PolynomiallyBounded.const 1).add <| clog_add (clog_add (clog_add (clog_add (clog_add
      (clog_add (clog_add (clog_add (clog_add (clog (PolynomiallyBounded.const 2)) (bounded_rawSize ht hL))
        (bounded_rawSize ht hD)) (clog ht)) (clog_mul (clog ht) hL)) (clog_mul (clog ht) hD)) hS)
          (clog_mul hS (clog_add hL (clog (PolynomiallyBounded.const 1))))) hM) hR

end RadicalCertificate.MonomialIndex.ExponentISA

end VPVNP
end Computability
end OAI
