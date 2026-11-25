import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRDecode
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCode

/-!
# A primitive recursive checker for the complete repair matrix tape

All dimensions, the modulus, the mask, the power and the matrix tape are
inputs to the same natural-number algorithm. Matrix equality is checked
entry by entry modulo the supplied positive modulus.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Raw

open KernelComputableAddress Matrix

def signDigit (p z j : ℕ) : ℕ := if digit 2 z j = 0 then 1 else p

def signTotal (p z m : ℕ) : ℕ := ∏ j ∈ Finset.range m, signDigit p z j

def pencilMat (p w m : ℕ) (t : Tape) (z : ℕ) : Mat :=
  add (atSlot t 0 w) (fun i j => ∑ k ∈ Finset.range m,
    signDigit p z k * atSlot t (1+k) w i j)

def correctionSlot (m z : ℕ) (u v : Bool) := 3+m+4*z+2*u.toNat+v.toNat

/-- The ground-ring response evaluated using natural representatives. -/
def responseMat (p w s m o half : ℕ) (t : Tape) (z : ℕ) : Mat :=
  let P := power w (pencilMat p w m t z) o
  let H := atSlot t (1+m) w
  let G := atSlot t (2+m) s
  let K u v := atSlot t (correctionSlot m z u v) s
  let T u := add (mult s (K u false) (mult w H P)) (mult s (K u true) H)
  add (sub p (sub p P (scale half (sub p (mult w P (mult w P P)) P))) (mult w P (mult s G (T false))))
    (mult s G (T true))

def Valid (p w s m o half : ℕ) (t : Tape) : Prop :=
  ∀ z < 2^m, equalMod p w w (responseMat p w s m o half t z) (scale (signTotal p z m) ident)

instance (p w s m o half : ℕ) (t : Tape) : Decidable (Valid p w s m o half t) :=
  inferInstanceAs (Decidable (∀ z < 2^m, equalMod p w w _ _))

variable {X : Type*} [Primcodable X]

private theorem primrec_signDigit {p z j : X → ℕ} (hp : Primrec p) (hz : Primrec z) (hj : Primrec j) :
    Primrec fun x => signDigit (p x) (z x) (j x) :=
  Primrec.ite (Primrec.eq.comp (primrec_digit (.const 2) hz hj) (.const 0)) (.const 1) hp

private theorem primrec_signTotal {p z m : X → ℕ} (hp : Primrec p) (hz : Primrec z) (hm : Primrec m) :
    Primrec fun x => signTotal (p x) (z x) (m x) := by
  let step (x : X) (v : ℕ × ℕ) := v.2 * signDigit (p x) (z x) v.1
  have hs : Primrec₂ step := (Primrec.nat_mul.comp (Primrec.snd.comp .snd)
    (primrec_signDigit (hp.comp .fst) (hz.comp .fst) (Primrec.fst.comp .snd))).to₂
  refine (Primrec.nat_rec' hm (.const 1) hs).of_eq fun x => ?_
  unfold signTotal
  generalize m x = n
  induction n with
  | zero => simp
  | succ n ih => simp [step, ih, Finset.prod_range_succ]

private theorem primrec_pencilMat {p w m z : X → ℕ} {t : X → Tape}
    (hp : Primrec p) (hw : Primrec w) (hm : Primrec m) (hz : Primrec z) (ht : Primrec t) :
    EntryPR fun x => pencilMat (p x) (w x) (m x) (t x) (z x) := by
  apply EntryPR.add (primrec_atSlot ht (.const 0) hw)
  apply primrec_rangeSum (hm.comp .fst)
  unfold Primrec₂
  apply Primrec.nat_mul.comp
  · exact primrec_signDigit (hp.comp (Primrec.fst.comp .fst)) (hz.comp (Primrec.fst.comp .fst)) .snd
  · exact (primrec_atSlot (ht.comp (Primrec.fst.comp .fst))
      (Primrec.nat_add.comp (.const 1) .snd) (hw.comp (Primrec.fst.comp .fst))).eval
      .id (Primrec.fst.comp (Primrec.snd.comp .fst)) (Primrec.snd.comp (Primrec.snd.comp .fst))

/-- Uniform numerical matrix response, including the input order of the pencil power. -/
theorem primrec_responseMat {p w s m o half z : X → ℕ} {t : X → Tape}
    (hp : Primrec p) (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (ho : Primrec o)
    (hh : Primrec half) (ht : Primrec t) (hz : Primrec z) :
    EntryPR fun x => responseMat (p x) (w x) (s x) (m x) (o x) (half x) (t x) (z x) := by
  let P := EntryPR.power hw (primrec_pencilMat hp hw hm hz ht) ho
  let H := primrec_atSlot ht (Primrec.nat_add.comp (.const 1) hm) hw
  let G := primrec_atSlot ht (Primrec.nat_add.comp (.const 2) hm) hs
  have K (u v : Bool) : EntryPR fun x => atSlot (t x) (correctionSlot (m x) (z x) u v) (s x) :=
    primrec_atSlot ht (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp (.const 3) hm) (Primrec.nat_mul.comp (.const 4) hz))
      (.const (2*u.toNat))) (.const v.toNat)) hs
  let T (u : Bool) := (EntryPR.mult hs (K u false) (EntryPR.mult hw H P)).add (EntryPR.mult hs (K u true) H)
  exact (EntryPR.sub hp (EntryPR.sub hp P (EntryPR.scale hh (EntryPR.sub hp (EntryPR.mult hw P (EntryPR.mult hw P P)) P)))
    (EntryPR.mult hw P (EntryPR.mult hs G (T false)))).add (EntryPR.mult hs G (T true))

theorem primrec_valid {p w s m o half : X → ℕ} {t : X → Tape}
    (hp : Primrec p) (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (ho : Primrec o)
    (hh : Primrec half) (ht : Primrec t) :
    PrimrecPred fun x => Valid (p x) (w x) (s x) (m x) (o x) (half x) (t x) := by
  apply bounded (primrec_pow (.const 2) hm)
  apply primrec_matches (hp.comp .fst) (hw.comp .fst) (hw.comp .fst)
  · exact primrec_responseMat (hp.comp .fst) (hw.comp .fst) (hs.comp .fst) (hm.comp .fst)
      (ho.comp .fst) (hh.comp .fst) (ht.comp .fst) .snd
  · exact EntryPR.scale (primrec_signTotal (hp.comp .fst) .snd (hm.comp .fst)) primrec_ident

private theorem cast_signDigit (p : ℕ) {m : ℕ} (η : Fin m → Bool) (j : Fin m) :
    (signDigit p (mask η).val j.val : ZMod (p+1)) = charSign (η j) := by
  have h : (p : ZMod (p+1)) + 1 = 0 := by
    simpa only [Nat.cast_succ] using ZMod.natCast_self (p+1)
  rw [signDigit, mask_bit]
  cases hj : η j <;> simp [charSign, eq_neg_of_add_eq_zero_left h]

private theorem cast_signTotal (p : ℕ) {m : ℕ} (η : Fin m → Bool) :
    (signTotal p (mask η).val m : ZMod (p+1)) = signProduct η := by
  rw [signTotal, Nat.cast_prod, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun j _ => cast_signDigit p η j

theorem interpret_pencilMat (p w s m : ℕ) (t : Tape) (η : Fin m → Bool) :
    interpret p w w (pencilMat p w m t (mask η).val) = onSign (decode p w s m t) η := by
  ext i j
  simp only [pencilMat, interpret, add, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, onSign,
    Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [cast_signDigit]
  rfl

theorem interpret_responseMat (p w s m o half : ℕ) (t : Tape) (η : Fin m → Bool) :
    interpret p w w (responseMat p w s m o half t (mask η).val) =
      response (decode p w s m t) η o (half : ZMod (p+1)) := by
  simp only [responseMat, interpret_add, interpret_sub, interpret_scale,
    interpret_mult, interpret_power, interpret_pencilMat p w s m, response, correctionSlot, decode]

/-- The primitive recursive entry tests decide exactly the full abstract acceptance predicate. -/
theorem valid_iff (p w s m o half : ℕ) (t : Tape) :
    Valid p w s m o half t ↔ accepts (decode p w s m t) o (half : ZMod (p+1)) = true := by
  rw [accepts_iff]
  constructor
  · intro h η
    have H := (matches_iff ..).mp (h (mask η).val (mask η).isLt)
    simpa only [interpret_responseMat, interpret_scale, cast_signTotal, interpret_ident] using H
  · intro h z hz
    obtain ⟨η, hη⟩ := mask_surjective m (⟨z, hz⟩ : Fin (2^m))
    obtain rfl : z = (mask η).val := (congrArg Fin.val hη).symm
    apply (matches_iff ..).mpr
    simpa only [interpret_responseMat, interpret_scale, cast_signTotal, interpret_ident] using h η

private abbrev Arguments := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Tape

private def test (a : Arguments) : Bool :=
  decide (Valid a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2)

private theorem primrec_test : Primrec test :=
  (primrec_valid .fst (Primrec.fst.comp .snd) (Primrec.fst.comp (Primrec.snd.comp .snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))).decide

def tapeOfCode (k : ℕ) : Tape := (Encodable.decode k).getD []

theorem primrec_tapeOfCode : Primrec tapeOfCode :=
  Primrec.option_getD.comp Primrec.decode (.const [])

@[simp] theorem tapeOfCode_encode (t : Tape) : tapeOfCode (Encodable.encode t) = t := by
  simp [tapeOfCode]

/-- One computable selector for every member of a family of inhabited
table searches, with all six dimensions and scalars allowed to vary. -/
theorem exists_computable_tape (p w s m o half : ℕ → ℕ) (hp : Computable p)
    (hw : Computable w) (hs : Computable s) (hm : Computable m) (ho : Computable o)
    (hh : Computable half) (hex : ∀ j, ∃ t : Tape, Valid (p j) (w j) (s j) (m j) (o j) (half j) t) :
    ∃ tape : ℕ → Tape, Computable tape ∧
      ∀ j, Valid (p j) (w j) (s j) (m j) (o j) (half j) (tape j) := by
  let good (j k : ℕ) := test (p j, w j, s j, m j, o j, half j, tapeOfCode k)
  have hg : Computable₂ good := (primrec_test.to_comp.comp
    ((hp.comp .fst).pair ((hw.comp .fst).pair ((hs.comp .fst).pair ((hm.comp .fst).pair
      ((ho.comp .fst).pair ((hh.comp .fst).pair (primrec_tapeOfCode.to_comp.comp .snd)))))))).to₂
  have he (j : ℕ) : ∃ k, good j k = true := by
    obtain ⟨t, ht⟩ := hex j
    exact ⟨Encodable.encode t, by simpa [good, test] using ht⟩
  obtain ⟨f, hf, h⟩ := Generator.first_certificate good hg he
  refine ⟨fun j => tapeOfCode (f j), primrec_tapeOfCode.to_comp.comp hf, ?_⟩
  intro j
  exact of_decide_eq_true ((h j).1)

end InterchangeROMRepair.Raw

end NearSquareRoot
end Computability
end OAI
