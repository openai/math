import OAI.Computability.VPVNP.LiveProgramLayout
import OAI.Computability.VPVNP.CursorBounds
import OAI.Computability.VPVNP.LogBounds
import OAI.Computability.VPVNP.RAMSiteBounds

/-!
# Word capacity for the live processor's public operand expressions

Only two exponentials occur among the static operands: the physical site
count and the virtual site count. For fixed address parameter both counts
grow polynomially in the input length. This suffices for *every intermediate
register* of an operand, including any multiplication before a division.
The later choice of the address parameter does not impose an upper bound
on the exponent of the permitted polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open Filter CursorBounds

/-- Live processor geometry at input length n, with site address width and RAM word width from
the address parameter and bucket size H n. -/
def paperGeometry (B : ℕ) (H : ℕ → ℕ) (n : ℕ) : Geometry :=
  ⟨n, addressBits B n, H n, CursorBounds.wordBits B n⟩

namespace PublicExpr

/-- The syntax used by the complete fixed public bank. -/
def SitePowers : PublicExpr → Prop
  | .add a b | .sub a b | .mul a b => SitePowers a ∧ SitePowers b
  | .divConst a _ | .log2 a | .clog2 a => SitePowers a
  | .pow2 a => SitePowers a ∧ (a = .d ∨ a = Layout.virtualSiteBits)
  | _ => True

@[simp] theorem SitePowers.natPow {a : PublicExpr} (h : a.SitePowers) (k : ℕ) :
    (a.natPow k).SitePowers := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih,h⟩

private theorem siteCount_polynomial (B : ℕ) :
    PolynomiallyBounded (fun n => 2^(B * Nat.clog 2 n)) := by
  apply (((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).pow B).of_eventually_le 1
  intro n hn
  have hlog := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hclog : 2^(Nat.clog 2 n) ≤ 2*n := calc
    _ ≤ 2^(n.log2+1) := Nat.pow_le_pow_right (by decide) (BurstRAM.clog_le_log2_succ n)
    _ = 2*2^(n.log2) := pow_succ' ..
    _ ≤ _ := Nat.mul_le_mul_left _ (by simpa [Nat.log2_eq_log_two] using hlog)
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left hclog B

private theorem virtualCount_polynomial (B : ℕ) (H : ℕ → ℕ) :
    PolynomiallyBounded (fun n => 2^Layout.virtualSiteBits.eval (paperGeometry B H n)) := by
  apply (siteCount_polynomial (B+2)).of_eventually_le 1
  intro n hn
  rw [Layout.virtualSiteBits_eq _ hn]
  exact Nat.pow_le_pow_right (by decide) (virtualBits_le B n)

private theorem d_polynomial (B : ℕ) : PolynomiallyBounded (addressBits B) :=
  (PolynomiallyBounded.const B).mul PolynomiallyBounded.id.clog

private theorem modulus_room (B : ℕ) (hB : 1 ≤ B) {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∀ᶠ n in atTop, f n < 2^CursorBounds.wordBits B n := by
  obtain ⟨A,d,N,h⟩ := hf
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop A,
    BurstRAM.eventually_polynomial_lt_wordModulus (d+1)] with n hn hA hp
  apply lt_of_le_of_lt ((h n hn).trans (Nat.mul_le_mul_right (n^d) hA))
  rw [← pow_succ']
  exact hp _ (BurstRAM.log2_le_addressWidth hB n)

/-- Polynomial bounds and simultaneous intermediate word fit for one
fixed operand. The live bucket size may be any polynomially bounded function. -/
theorem SitePowers.fits {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H)
    {e : PublicExpr} (h : e.SitePowers) :
    PolynomiallyBounded (fun n => e.eval (paperGeometry B H n)) ∧
      ∀ᶠ n in atTop, e.Fits (paperGeometry B H n) (2^CursorBounds.wordBits B n) := by
  induction e with
  | lit c =>
    have hp : PolynomiallyBounded (fun n => (lit c).eval (paperGeometry B H n)) := .const _
    exact ⟨hp, (modulus_room B hB hp).mono fun _ hi => ⟨hi,trivial⟩⟩
  | n => exact ⟨PolynomiallyBounded.id, (modulus_room B hB PolynomiallyBounded.id).mono fun _ hi => ⟨hi,trivial⟩⟩
  | d => exact ⟨d_polynomial B, (modulus_room B hB (d_polynomial B)).mono fun _ hi => ⟨hi,trivial⟩⟩
  | H => exact ⟨hH, (modulus_room B hB hH).mono fun _ hi => ⟨hi,trivial⟩⟩
  | w =>
    have hp := ((d_polynomial B).add (.const 10)).pow 4
    exact ⟨hp, (modulus_room B hB hp).mono fun _ hi => ⟨hi,trivial⟩⟩
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    obtain ⟨ha,fa⟩ := ia h.1
    obtain ⟨hb,fb⟩ := ib h.2
    first | have hp := ha.add hb; refine ⟨hp,?_⟩
          | have hp := ha.mul hb; refine ⟨hp,?_⟩
          | have hp := ha.of_le (fun n => Nat.sub_le (a.eval (paperGeometry B H n)) (b.eval (paperGeometry B H n))); refine ⟨hp,?_⟩
    filter_upwards [modulus_room B hB hp, fa, fb] with n hl hal hbl
    exact ⟨hl,hal,hbl⟩
  | divConst a b ih =>
    obtain ⟨ha,fa⟩ := ih h
    have hp := ha.of_le (fun n => Nat.div_le_self (a.eval (paperGeometry B H n)) b)
    refine ⟨hp,?_⟩
    filter_upwards [modulus_room B hB hp, fa, modulus_room B hB (PolynomiallyBounded.const b)] with n hl hal hb
    exact ⟨hl,hal,hb⟩
  | log2 a ih | clog2 a ih =>
    obtain ⟨ha,fa⟩ := ih h
    first | have hp := ha.clog; refine ⟨hp,?_⟩
          | have hp := ha.of_le (fun n => Nat.log_le_self 2 (a.eval (paperGeometry B H n))); refine ⟨hp,?_⟩
    filter_upwards [modulus_room B hB hp, fa] with n hl hal
    exact ⟨hl,hal⟩
  | pow2 a ih =>
    obtain ⟨_,fa⟩ := ih h.1
    have hp : PolynomiallyBounded (fun n => (pow2 a).eval (paperGeometry B H n)) := by
      rcases h.2 with rfl | rfl
      · exact siteCount_polynomial B
      · exact virtualCount_polynomial B H
    exact ⟨hp, (modulus_room B hB hp).and fa⟩

/-- Uniform threshold for every operand in any finite table. -/
theorem fits_bank {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H)
    {ι : Type*} [Finite ι] (bank : ι → PublicExpr) (hs : ∀ i, (bank i).SitePowers) :
    ∀ᶠ n in atTop, ∀ i, (bank i).Fits (paperGeometry B H n) (2^CursorBounds.wordBits B n) :=
  (Filter.eventually_all).mpr fun i => ((hs i).fits hB hH).2

end PublicExpr
end LiveProgram

end VPVNP
end Computability
end OAI
