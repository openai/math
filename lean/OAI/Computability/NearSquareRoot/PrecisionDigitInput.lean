import OAI.Computability.NearSquareRoot.PrecisionDigitBounds
import OAI.Computability.IntegerMultiplication.Brief.Launch
import OAI.Computability.IntegerMultiplication.Lea.Crops
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Partial

/-!
# Parsing the binary operands

One fixed stack program measures a most-significant-first operand, computes the
radix and slot count from its length, reverses it, pads its top digit with
zeros, and cuts it into the `h` little-endian digits. The shape header is
manufactured inside the time bound. The ordered digit stream is the input of
the subsequent placement into valid box addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open IntegerMultiplication.Carry IntegerMultiplication.Brief

/-- The chunk records in increasing digit order. -/
noncomputable def records (x : Word) : Fin (count x.length) → Word :=
  Lea.crop (width x.length) (count x.length) x.reverse

theorem record_width (x : Word) (i : Fin (count x.length)) :
    (records x i).length = width x.length :=
  (Lea.crop_ ..).1 i

theorem record_value_lt_radix (x : Word) (i : Fin (count x.length)) :
    value (records x i) < 2 ^ width x.length := by
  simpa only [record_width] using value_lt (records x i)

theorem records_score (x : Word) (hx : 2 ≤ x.length) :
    Cap.score (2 ^ width x.length) (value ∘ records x) = bitValue x := by
  rw [endianness]
  apply Lea.scoreV
  rw [List.length_reverse, mul_comm]
  exact (count_mul_width hx).1

/-- Convert a polynomial-time binary integer derived from the measured
header into tally form, in the linear budget whenever its value fits it. -/
private theorem unary_of_figure {I : Type} {n f : I → ℕ} (hf : Figure (city n) f)
    (B : ℕ) (hf' : ∀ i, f i ≤ B*(n i+1)) :
    Carries (measure n) ((journals n).header) (fun i => send (tally (f i))) := by
  obtain ⟨words,hwords,hval⟩ := hf
  have wordTask := IntegerMultiplication.Strip.Regime.Small.cooked (wealthy n) hwords
  have binary := wordTask.times (here n) 8 (fun i => by
    have u := Param.load_below (n i)
    have v := Param.amount_l (n i)
    change ((Param.load (n i) : ℕ) : ℝ) ≤ (8 : ℝ)*((n i : ℝ)+1)
    exact_mod_cast (by omega : Param.load (n i) ≤ 8*(n i+1)))
  obtain ⟨K,hK⟩ := binary.out
  have convert := rice.on words
  simp only [hval] at convert
  apply binary.sequence
  refine ⟨here n,_,convert,K+B+1,fun i => ?_⟩
  have hw := hK i
  change (size (words i) : ℝ) ≤ (K : ℝ) * measure n i at hw
  have hv : (f i : ℝ) ≤ (B : ℝ) * measure n i := by exact_mod_cast hf' i
  push_cast
  nlinarith only [hw,hv,here n i]

/-- The address width is calculated from the input length by the same
polynomial-time header arithmetic used to calculate the number of digits. -/
theorem header_addressBits {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Carries (measure n) ((journals n).header) (fun i => send (tally (addressBits (n i)))) := by
  have hb : Figure (city n) (width ∘ n) := Figure.of_spoken (guide_city n).amount_.short_log
  have hh : Figure (city n) (count ∘ n) :=
    ((((guide_city n).amount_.added hb).subtracted (.natural 1)).quotients hb)
  have hk : Figure (city n) (addressBits ∘ n) :=
    Figure.of_spoken (((Figure.natural 4).multiplied hh).short_log)
  apply unary_of_figure hk 2
  intro i
  have := addressBits_le (hn i)
  have := width_le (n i)
  change addressBits (n i) ≤ _
  omega

/-- Fixed command on an encoded MSF operand, for any computable rank count
up to the full box size. The uniform
`Carries` bound includes building the shape, measuring and reversing the
input, unary header generation, padding, and segmentation. -/
theorem parse_msf_given_slots {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length)
    (m : I → ℕ)
    (tallM : Carries (measure (fun i => (x i).length)) ((journals (fun i => (x i).length)).header)
      (fun i => send (tally (m i))))
    (hcap : ∀ i, m i ≤ capacity (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x)
      (fun i => send (List.ofFn (Lea.crop (width (x i).length) (m i) (x i).reverse))) := by
  let n (i : I) := (x i).length
  let b := width ∘ n
  have hb : Figure (city n) b := Figure.of_spoken (guide_city n).amount_.short_log
  have hm' (i : I) : m i ≤ 8*n i := by
    have hh := (hcap i).trans_lt (capacity_bounds (hx i)).2
    have he := count_le (hx i)
    change m i < 8*count (n i) at hh
    change count (n i) ≤ n i at he
    omega
  have hm'' (i : I) : m i * b i ≤ 16*n i := by
    have h₁ := (hcap i).trans_lt (capacity_bounds (hx i)).2
    have h₂ := (count_mul_width (hx i)).2
    change width (n i) * count (n i) ≤ 2*n i at h₂
    have h₃ := Nat.mul_le_mul_right (b i) h₁.le
    change m i * b i ≤ 8*count (n i)*b i at h₃
    dsimp only [b,Function.comp_apply] at *
    nlinarith only [h₂,h₃]
  have tallB := unary_of_figure hb 1 (fun i => by have := width_le (n i); change width (n i) ≤ _; omega)
  let mb (i : I) := (tally (m i),tally (b i))
  have gen := (generate (X := Tally)).on mb
  simp only [mb, tally_length] at gen
  have plan : Carries (measure n) ((journals n).header) (fun i => send (List.replicate (m i) (tally (b i)))) := by
    apply (tallM.twice tallB).sequence
    refine ⟨here n,_,gen,64,fun i => ?_⟩
    rw [size_tally,tally_length]
    unfold Brief.measure
    norm_cast
    have hm₁ := hm' i
    have hm₂ := hm'' i
    have hb₁ : b i ≤ n i := width_le _
    nlinarith only [hm₁,hm₂,hb₁]
  let tallyList (i : I) := List.replicate (m i) (tally (b i))
  have flat := Carries.func (y := tallyList) (here n) plan.out _ Easy.flatten
  have header := plan.twice (plan.chain flat)
  have key : Carries (measure n) (send ∘ x) ((journals n).header) := Brief.lit x (fun _=>rfl)
  have rev := Carries.func (y := x) (here n) key.small _ Easy.reverse
  have argument := (key.chain header).twice rev
  let input (i : I) := ((tallyList i,(tallyList i).flatten),(x i).reverse)
  have cut := argument.chain (Carries.func (y := input) (here n) argument.out Lea.saw Lea.sawE)
  have tallyLen i : (tallyList i).flatten = tally (m i * b i) := by
    simp [tallyList, tally]
  have cut_eq i : Lea.saw (input i) = List.ofFn (Lea.crop (b i) (m i) (x i).reverse) := by
    unfold input
    rw [tallyLen]
    exact Lea.sawn ..
  simpa only [cut_eq, b, n, Function.comp_apply] using cut

/-- Count the occupied slots with a fixed linear-time command. -/
theorem maskCount_easy : Easy (fun mask : List Bool => tally (mask.count true)) := by
  let emit (b : Bool) : Tally := if b then [()] else []
  have prog : Easy (fun mask : List Bool => (mask.map emit).flatten) :=
    (easy_map Easy.identity (Easy.finite emit)).compose Easy.flatten
  have heq (mask : List Bool) : (mask.map emit).flatten = tally (mask.count true) := by
    induction mask with
    | nil => rfl
    | cons x xs ih =>
      cases x <;> simp [emit,ih,tally,List.replicate_succ]
  exact (funext heq) ▸ prog

/-- The validity-mask construction can supply the compact rank count directly
by a sequential count of the occupied slots. -/
theorem parse_msf_mask {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length)
    (mask : I → List Bool)
    (hm : Carries (measure (fun i => (x i).length)) ((journals (fun i => (x i).length)).header)
      (send ∘ mask))
    (hcap : ∀ i, (mask i).length ≤ capacity (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x)
      (fun i => send (List.ofFn (Lea.crop (width (x i).length) ((mask i).count true) (x i).reverse))) := by
  apply parse_msf_given_slots x hx _ (hm.chain (Carries.func (y := mask) hm.budget hm.out _ maskCount_easy))
  intro i
  exact (List.count_le_length ..).trans (hcap i)

/-- A size computed in binary in polynomial header time also supplies the
unary rank count required by the scan. -/
theorem parse_msf_slots {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length)
    (m : I → ℕ) (hm : Figure (city (fun i => (x i).length)) m)
    (hcap : ∀ i, m i ≤ capacity (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x)
      (fun i => send (List.ofFn (Lea.crop (width (x i).length) (m i) (x i).reverse))) := by
  apply parse_msf_given_slots x hx m _ hcap
  apply unary_of_figure hm 8
  intro i
  exact le_trans ((hcap i).trans (capacity_bounds (hx i)).2.le)
    (Nat.mul_le_mul_left _ ((count_le (hx i)).trans (Nat.le_succ _)))

/-- Parse without appending extra zero digits. -/
theorem parse_msf {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x)
      (fun i => send (List.ofFn (records (x i)))) := by
  let n (i : I) := (x i).length
  have hb : Figure (city n) (width ∘ n) := Figure.of_spoken (guide_city n).amount_.short_log
  have hh : Figure (city n) (count ∘ n) :=
    ((((guide_city n).amount_.added hb).subtracted (.natural 1)).quotients hb)
  apply parse_msf_slots x hx _ hh
  intro i
  have h := (capacity_bounds (hx i)).1
  change count (x i).length ≤ capacity (x i).length
  omega

end DigitPacking

end NearSquareRoot
end Computability
end OAI
