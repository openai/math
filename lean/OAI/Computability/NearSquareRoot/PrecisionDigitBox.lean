import OAI.Computability.NearSquareRoot.PrecisionDigitInput
import OAI.Computability.NearSquareRoot.PrecisionDigitRelease
import OAI.Computability.NearSquareRoot.BoxMaskProgram
import OAI.Computability.NearSquareRoot.BoxMaskedRecords

/-! # Placement of two MSF operands into the padded coprime box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open IntegerMultiplication.Brief

/-- Filled positions are in increasing mixed-radix rank. Empty bit strings
represent digit zero at invalid positions. -/
noncomputable def boxed (x : Word) : List Word :=
  let mask := BoxMaskProgram.mask (addressBits x.length)
  BoxMaskedRecords.expand [] (mask, List.ofFn (Lea.crop (width x.length) (mask.count true) x.reverse))

abbrev ValidShape (n : ℕ) :=
  BoxShape.Valid (addressBits n) (BoxScale.width (addressBits n)) (CoprimeBox.box (addressBits n))

theorem eventually_validShape : ∀ᶠ n in Filter.atTop, ValidShape n := by
  obtain ⟨K,hK⟩ := CoprimeBox.eventually_valid
  exact (addressBits_tendsto_atTop.eventually_ge_atTop K).mono fun _ h => hK _ h

/-- Count the raw bits, compute the box and its mask, and expand the radix
digits into precisely its occupied positions, charging every intermediate
list in the linear stack budget. -/
theorem boxed_scan {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length)
    (hv : ∀ i, ValidShape (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x) (send ∘ boxed ∘ x) := by
  let n (i : I) := (x i).length
  let k (i : I) := addressBits (n i)
  let mask (i : I) := BoxMaskProgram.mask (k i)
  have hm (i : I) : (mask i).length = capacity (n i) := BoxOrder.length_shape (hv i)
  have header := header_addressBits n hx
  have maskProg := (BoxMaskProgram.carries k hv).times (here n) 8 (fun i=>by
    have h := (capacity_bounds (hx i)).2.le
    have g := count_le (hx i)
    change (capacity (n i) : ℝ) ≤ 8*((n i:ℝ)+1)
    exact_mod_cast (show capacity (n i) ≤ 8*(n i+1) from h.trans (Nat.mul_le_mul_left _ (g.trans (Nat.le_succ _)))))
  have loadMask : Carries (measure n) ((journals n).header) (send ∘ mask) := header.chain maskProg
  have maskFromInput := (lit x (fun _=>rfl)).chain loadMask
  have digits := parse_msf_mask x hx mask loadMask (fun i => (hm i).le)
  have argument := maskFromInput.twice digits
  let arg (i : I) := (mask i,List.ofFn (Lea.crop (width (n i)) ((mask i).count true) (x i).reverse))
  exact argument.chain (Carries.func (y := arg) (here n) argument.out _ (BoxMaskedRecords.expand_easy ([] : Word)))

/-- One finite-tape machine reads the raw delimiter-separated operands and
emits both padded coefficient arrays on all sufficiently large lengths. -/
theorem boxed_pair_machine : ∃ N : ℕ,
    let Input := {p : Interface.Pair // p.1.length = p.2.length ∧ N ≤ p.1.length}
    PairToTree (fun p : Input => p.val) (fun p => send (boxed p.val.1,boxed p.val.2))
      (fun p => p.val.1.length) := by
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp eventually_validShape
  let N := max 2 M
  let Input := {p : Interface.Pair // p.1.length = p.2.length ∧ N ≤ p.1.length}
  have big (p : Input) : 2 ≤ p.val.1.length := (le_max_left 2 M).trans p.property.2
  have val (p : Input) : ValidShape p.val.1.length := hM _ ((le_max_right 2 M).trans p.property.2)
  have u := boxed_scan (fun p : Input => p.val.1) big val
  have v := boxed_scan (fun p : Input => p.val.2) (fun p => p.property.1 ▸ big p)
    (fun p => p.property.1 ▸ val p)
  have hw (p : Input) : p.val.2.length = p.val.1.length := p.property.1.symm
  simp only [hw] at v
  refine ⟨N,release_pair_scan (fun p : Input => p.val) _ _ (fun _=>rfl) hw ?_⟩
  exact (u.first v.small).chain (v.second u.out)

end DigitPacking

end NearSquareRoot
end Computability
end OAI
