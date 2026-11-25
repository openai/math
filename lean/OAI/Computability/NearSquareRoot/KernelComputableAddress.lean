import OAI.Computability.NearSquareRoot.KernelPass
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Algebra.BigOperators.Fin

/-! # Arithmetic addresses for a uniform binary template checker

Letters are base-four vectors, one digit for each axis and two binary
coordinates per digit. Address words are written in base four to the arity,
least significant column first.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableAddress
open KernelPass Finset

def packSig (q : ℕ) : (Fin q → ZMod 2) ≃ Fin (2^q) := finFunctionFinEquiv

def packColumn (A : ℕ) : Column A ≃ Fin (4^A) :=
  (Equiv.piCongrRight fun _ : Fin A => packSig 2).trans finFunctionFinEquiv

def pack (A h : ℕ) : Addr A h ≃ Fin ((4^A)^h) :=
  (Equiv.piCongrRight fun _ : Fin h => packColumn A).trans finFunctionFinEquiv

def digit (base z i : ℕ) : ℕ := z / base ^ i % base

def letter (A z c : ℕ) : ℕ := digit (4^A) z c

def pairAt (t a : ℕ) : ℕ := digit 4 t a

def bitAt (t a j : ℕ) : ℕ := digit 2 (pairAt t a) j

private theorem digit_equiv {m n : ℕ} (v : Fin n → Fin m) (k : Fin n) :
    digit m (finFunctionFinEquiv v).val k.val = (v k).val :=
  congrArg (fun f : Fin n → Fin m => (f k).val) (finFunctionFinEquiv.symm_apply_apply v)

theorem letter_pack {A h : ℕ} (x : Addr A h) (c : Fin h) :
    letter A (pack A h x).val c.val = (packColumn A (x c)).val := digit_equiv _ _

theorem pairAt_packColumn {A : ℕ} (x : Column A) (a : Fin A) :
    pairAt (packColumn A x).val a.val = (packSig 2 (x a)).val := digit_equiv _ _

theorem digit_packSig {q : ℕ} (x : Fin q → ZMod 2) (j : Fin q) :
    digit 2 (packSig q x).val j.val = (x j).val := digit_equiv _ _

theorem bitAt_packColumn {A : ℕ} (x : Column A) (a : Fin A) (j : Fin 2) :
    bitAt (packColumn A x).val a.val j.val = (x a j).val := by
  rw [bitAt, pairAt_packColumn, digit_packSig]

variable {X : Type*} [Primcodable X]

theorem primrec_pow {b n : X → ℕ} (hb : Primrec b) (hn : Primrec n) :
    Primrec (fun x => b x ^ n x) := by
  let step (x : X) (s : ℕ × ℕ) := s.2 * b x
  have hs : Primrec₂ step := (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (hb.comp Primrec.fst)).to₂
  refine (Primrec.nat_rec' hn (Primrec.const 1) hs).of_eq fun x => ?_
  generalize n x = k
  induction k with
  | zero => simp
  | succ k ih => simp [step, ih, pow_succ]

theorem primrec_digit {b z i : X → ℕ} (hb : Primrec b) (hz : Primrec z) (hi : Primrec i) :
    Primrec (fun x => digit (b x) (z x) (i x)) :=
  Primrec.nat_mod.comp (Primrec.nat_div.comp hz (primrec_pow hb hi)) hb

theorem primrec_letter {a z c : X → ℕ} (ha : Primrec a) (hz : Primrec z) (hc : Primrec c) :
    Primrec (fun x => letter (a x) (z x) (c x)) :=
  primrec_digit (primrec_pow (Primrec.const 4) ha) hz hc

theorem primrec_pairAt {t a : X → ℕ} (ht : Primrec t) (ha : Primrec a) :
    Primrec (fun x => pairAt (t x) (a x)) := primrec_digit (Primrec.const 4) ht ha

theorem primrec_bitAt {t a j : X → ℕ} (ht : Primrec t) (ha : Primrec a) (hj : Primrec j) :
    Primrec (fun x => bitAt (t x) (a x) (j x)) := primrec_digit (Primrec.const 2) (primrec_pairAt ht ha) hj

theorem primrec_rangeSum {n : X → ℕ} {f : X → ℕ → ℕ} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec (fun x => ∑ i ∈ range (n x), f x i) := by
  let step (x : X) (s : ℕ × ℕ) := s.2 + f x s.1
  have hs : Primrec₂ step :=
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (hf.comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  refine (Primrec.nat_rec' hn (Primrec.const 0) hs).of_eq fun x => ?_
  generalize n x = k
  induction k with
  | zero => simp
  | succ k ih => simp [step, ih, sum_range_succ]

end KernelComputableAddress

end NearSquareRoot
end Computability
end OAI
