import OAI.Computability.VPVNP.ExponentTrace
import OAI.Computability.VPVNP.GrammarDiagonal
import OAI.Computability.VPVNP.PrimedInputRAMRows

/-!
# The two contractions of the primed chain

Equation (9.2) uses consecutive pairs of groups of length `2^h` pairs.
Each pair has two complete processor groups. Even cuts are shared with
neighboring pairs; its odd cut and all communication sends in its two groups
are private to that pair. The four header bits on a site contain its group's
actual one-based number, the advice, and the incident cut bits. This numbering
is independent of the live group which later simulates the pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairedChain

open CutSchedule ExponentTrace PrimedInputRAM MvPolynomial
open scoped Classical

private theorem width_le (H Δ i : ℕ) : CutSchedule.width H Δ i ≤ H * Δ := by
  unfold CutSchedule.width
  split_ifs
  · exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  · exact Nat.zero_le _

/-- The pair's exterior cuts are `2i` and `2i+2` and its interior cut is
`2i+1`, using a zero-based pair index `i`. -/
def lengths (h Δ adviceLength : ℕ) (i : Fin (2 ^ h)) : Lengths where
  index := h + 2
  advice := adviceLength
  leftCut := CutSchedule.width (h + 1) Δ (2 * i.val)
  middleCut := CutSchedule.width (h + 1) Δ (2 * i.val + 1)
  rightCut := CutSchedule.width (h + 1) Δ (2 * (i.val + 1))
  cutCapacity := (h + 1) * Δ
  leftFit := width_le ..
  rightFit := width_le ..

/-- The `H+1`-bit literal encoding of the primed group's own one-based number. -/
def groupIndex {h : ℕ} (i : Fin (2 ^ h)) (g : Fin 2) : BurstRAM.Word (h + 2) :=
  ⟨2 * i.val + g.val + 1, by
    have hi := i.isLt
    have hg := g.isLt
    rw [pow_add]
    norm_num
    omega⟩

/-- The fixed literal and exterior fields supplied to both groups of a pair.
The full bit string at a site is built by `PrimedInputRAM.input`. -/
def headers {h Δ a : ℕ} (advice : Bits a) (exterior : Exterior h Δ)
    (i : Fin (2 ^ h)) : Header (lengths h Δ a i) → Bool
  | .group g k => RAMSerialization.wordBits _ (groupIndex i g) k
  | .advice k => advice k
  | .leftCut k => exterior i.castSucc k
  | .rightCut k => exterior i.succ k

/-- A Boolean assignment to the internal wires of the paired-chain instance at the specified
chain index and RAM parameters. -/
abbrev PairBits (h Δ a r bucket w : ℕ) (i : Fin (2 ^ h)) :=
  Internal (lengths h Δ a i) r bucket w → Bool

/-- Full literal-and-wire input of a primed site. Communication bits are
summed even when they do not form a valid RAM transcript. -/
def siteInput {n h Δ a r bucket w : ℕ} (program : UniversalMachine.Program)
    (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w) (advice : Bits a)
    (exterior : Exterior h Δ) (i : Fin (2 ^ h)) (s : PairBits h Δ a r bucket w i)
    (v : Site r) : Fin n → Bool :=
  input program hfit (headers advice exterior i) s v

/-- The integer contraction (9.2), with the shared bit assignments indexed
by the even cuts and the independent internal bits of every pair. -/
noncomputable def original {n h Δ a r bucket w : ℕ} (program : UniversalMachine.Program)
    (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w) (advice : Bits a) : ℕ :=
  Diagonal.originalContraction (fun (ξ : Exterior h Δ) i s v =>
    acceptingCount (siteInput program hfit advice ξ i s v))

/-- The formal joint polynomial of equations (9.3) and (9.5), leaving the
integer production labels as variables until the contraction is evaluated. -/
noncomputable def primed {n h Δ a r bucket w : ℕ} {H : Type*} [Fintype H]
    (program : UniversalMachine.Program) (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w)
    (advice : Bits a) (d : Fin n) (head : H) : MvPolynomial (GrammarLabel (Fin n × Bool) H n) ℤ :=
  ∑ ξ : Exterior h Δ, ∏ i : Fin (2 ^ h),
    PairCoefficient.jointPolynomial d head (siteInput program hfit advice ξ i)

/-- Equation (9.3) for the paper's actual bit sharing, `Uₙ`, and `Bₓ`.
Equation (8.1) at each site replaces a grammar query by the path count of
the very same input string. -/
theorem primed_eq_original {n h Δ a r bucket w : ℕ} {H A : Type*} [Fintype H] [CommRing A]
    (program : UniversalMachine.Program) (hfit : BurstRAM.ProcessorInput.Fits program n r bucket w)
    (advice : Bits a) (d : Fin n) (head : H) (value : GrammarLabel (Fin n × Bool) H n → A)
    (hlabels : ∀ x, eval₂Hom (Int.castRingHom A) value (labelQuery d head x) = (acceptingCount x : A)) :
    eval₂Hom (Int.castRingHom A) value (primed (h := h) (Δ := Δ) program hfit advice d head) =
      (original (h := h) (Δ := Δ) program hfit advice : A) := by
  unfold primed original Diagonal.originalContraction PairCoefficient.jointPolynomial
  simp only [map_sum, map_prod, hlabels]
  simp_rw [Fintype.prod_sum]
  push_cast
  rfl

end PairedChain

end VPVNP
end Computability
end OAI
