import OAI.Computability.VPVNP.MacaulayPairCall

/-!
# Uniform register widths and bounds for the physical Macaulay entry arms

The actual physical clocks in the two returning routines are singly
exponential. Their stack bounds are polynomial in the arity, register width
and caller's live stack bound, independently of the size of the index scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open PolynomiallyBounded

/-- Common register width accommodating both graded-key scans, the optional coordinate shift
and the scaled exponent comparisons. -/
def requiredWidth (d : Inputs) := ExponentISA.entryWidth d.arity (d.degree false) (d.degree true) d.scale d.mark 0

private theorem size_le_raw (t D : ℕ) : size t D ≤ rawSize t D := by
  rw [size_eq_card]
  exact (card_boundedMonomial_le t D).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

/-- One advised register width works for every pair of legal ordinals at
these degrees, including the shifted power comparison. -/
theorem fits_of_width (d : Inputs) (k : Ordinals d) {w : ℕ} (hw : requiredWidth d ≤ w) :
    (∀ c, ISA.Fits (ISA.graded d.arity (d.degree c) (k c)) w) ∧ ExponentISA.Fits (powerParams d) w := by
  have h₀ := ExponentISA.indexFits (scale := d.scale) (mark := d.mark) (request := 0)
    ((k false).isLt.le.trans (size_le_raw ..)) ((k true).isLt.le.trans (size_le_raw ..))
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have larger {p : ISA.Parameters} (h : ISA.Fits p (requiredWidth d)) : ISA.Fits p w :=
    ⟨h.one_lt.trans_le hpow,h.base_pos,h.base_lt.trans_le hpow,h.arity_lt.trans_le hpow,h.box_lt.trans_le hpow,
      h.limit_lt.trans_le hpow,h.ordinal_lt.trans_le hpow,h.sum_lt.trans_le hpow⟩
  have h := h₀.2.2
  exact ⟨fun c => by cases c; exact larger h₀.1; exact larger h₀.2.1,
    ⟨h.one_lt.trans_le hpow,h.source_pos,h.column_pos,h.source_lt.trans_le hpow,h.column_lt.trans_le hpow,
      h.scale_lt.trans_le hpow,h.product_lt.trans_le hpow,h.mark_lt.trans_le hpow,h.request_lt.trans_le hpow⟩⟩

theorem requiredWidth_polynomial (d : ℕ → Inputs) (ht : PolynomiallyBounded (fun n => (d n).arity))
    (hdeg : ∀ c, PolynomiallyBounded (fun n => Nat.clog 2 ((d n).degree c)))
    (hscale : PolynomiallyBounded (fun n => Nat.clog 2 (d n).scale))
    (hmark : PolynomiallyBounded (fun n => Nat.clog 2 (d n).mark)) :
    PolynomiallyBounded (fun n => requiredWidth (d n)) :=
  ExponentISA.entryWidth_polynomial ht (hdeg false) (hdeg true) hscale hmark (clog (const 0))

private theorem boundMax {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le fun _ => max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

private theorem boundPrepare {w : ℕ → ℕ} (hw : PolynomiallyBounded w) :
    PolynomiallyBounded (fun n => RAMTape.ISA.prepareBound (w n) 0+3) :=
  (((const 100).mul ((hw.add (const 1)).pow 2)).mul (const (0+1))).add (const 3)

private theorem boundOverhead (i o r : ℕ) {B C : ℕ → ℕ} (hB : PolynomiallyBounded B) (hC : PolynomiallyBounded C) :
    PolynomiallyBounded (fun n => CallBank.overhead i o r (B n) (C n)) :=
  ((((const i).mul (((const 5).mul hB).add (const 2))).add (const 1)).add
    (((const o).mul (((const 5).mul hC).add (const 2))).add (const 1))).add
      (((const r).mul (hC.add (const 1))).add (const 1))

/-- The bounds of the actual two binary controls under the bit-size
hypotheses of Lemma 8.2. Both include advice staging and final cleanup. -/
theorem resources (d : ℕ → Inputs) {w B : ℕ → ℕ} (hw : PolynomiallyBounded w) (hB : PolynomiallyBounded B)
    (ht : PolynomiallyBounded (fun n => (d n).arity))
    (hdeg : ∀ c, PolynomiallyBounded (fun n => Nat.clog 2 ((d n).degree c))) :
    PolynomiallyBounded (fun n => equationSpace (w n) (B n) (d n)) ∧
    PolynomiallyBounded (fun n => poweredSpace (w n) (B n)) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (scanClock (w n) (B n) (d n) +
      packClock (d n).arity (w n) (B n) + clearCost (w n))) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (scanClock (w n) (B n) (d n) +
      powerClock (d n).arity (w n) (B n) + clearCost (w n))) := by
  have hPrep := boundPrepare hw
  have hScan := boundOverhead 14 1 14 hB (hw.add hPrep)
  have hPwr := boundOverhead 16 1 16 hB (hw.add hPrep)
  have hScanSpace : PolynomiallyBounded (fun n => ordinalSpace (w n) (B n)) := (hB.add (hw.add hPrep)).add hScan
  have hPowSpace : PolynomiallyBounded (fun n => powerSpace (w n) (B n)) := (hB.add (hw.add hPrep)).add hPwr
  have hBody : PolynomiallyBounded (fun n => ExponentPack.bodyCost (w n)) :=
    ((const ExponentPack.arithmetic.length).mul ((const 100).mul ((hw.add (const 1)).pow 2))).add
      (((const 5).mul hw).add (const 2))
  have hTicks : PolynomiallyBounded (fun n => packTicks (d n).arity (w n)) :=
    (ht.mul (hBody.add (const 1))).add (const 1)
  have hInner := (boundMax hw ht).add hTicks
  have hPack := boundOverhead 12 2 13 hB hInner
  have hPackSpace : PolynomiallyBounded (fun n => packSpace (d n).arity (w n) (B n)) := (hB.add hInner).add hPack
  have hClear : PolynomiallyBounded (fun n => clearCost (w n)) := ((const 2).mul (hw.add (const 1))).add (const 1)
  have hOrd (c : Bool) : PolynomiallyBounded (fun n => Nat.clog 2
      (ordinalClock (w n) (B n) (d n).arity ((d n).degree c))) :=
    clog_add (clog_mul (clog_add (clog_mul (bounded_rawSize ht (hdeg c))
      (clog (((const 5).mul ht).add (const 10)))) (clog (const 2))) (clog hPrep)) (clog hScan)
  have hAll := clog_add (hOrd false) (hOrd true)
  have hPackClock := hTicks.add hPack
  have hPowClock := ((((const 16).mul ht).add (const 2)).mul hPrep).add hPwr
  exact ⟨boundMax (boundMax hScanSpace hPackSpace) (((hB.add (ht.mul hw)).add hw).add hClear),
    boundMax (boundMax hScanSpace hPowSpace) ((hB.add hw).add hClear),
    clog_add (clog_add hAll (clog hPackClock)) (clog hClear),
    clog_add (clog_add hAll (clog hPowClock)) (clog hClear)⟩

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
