import OAI.Computability.NearSquareRoot.CommonAlphabetNumbering
import OAI.Computability.NearSquareRoot.KernelComputableAddress
import Mathlib.Data.Nat.Digits.Defs

/-! # Arithmetic for numbering finite function tables

The first argument in the domain enumeration supplies the least significant digit.
Decoding takes the domain size as a parameter so that trailing zero digits are retained.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Numbering

/-- Read a little-endian list of numerical output labels. -/
def encodeBase (b : ℕ) (digits : List ℕ) : ℕ := Nat.ofDigits b digits

/-- Read the output label at argument number `k`. -/
abbrev digit (b code k : ℕ) : ℕ := KernelComputableAddress.digit b code k

/-- Recover the complete list of output labels for a fixed domain size. -/
def decodeBase (b code n : ℕ) : List ℕ := (List.range n).map (digit b code)

theorem primrec_encodeBase : Primrec₂ encodeBase := by
  let step (p : ℕ × List ℕ) (s : ℕ × ℕ) := s.1 + p.1 * s.2
  have hs : Primrec₂ step := (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hs).to₂.of_eq fun b l =>
    (Nat.ofDigits_eq_foldr b l).symm

variable {X : Type*} [Primcodable X]

theorem primrec_digit {b c k : X → ℕ} (hb : Primrec b) (hc : Primrec c) (hk : Primrec k) :
    Primrec (fun x => digit (b x) (c x) (k x)) :=
  KernelComputableAddress.primrec_digit hb hc hk

theorem primrec_decodeBase {b c n : X → ℕ} (hb : Primrec b) (hc : Primrec c) (hn : Primrec n) :
    Primrec (fun x => decodeBase (b x) (c x) (n x)) :=
  Primrec.list_map (Primrec.list_range.comp hn)
    (primrec_digit (hb.comp Primrec.fst) (hc.comp Primrec.fst) Primrec.snd).to₂

theorem encodeBase_ofFn {b n : ℕ} (v : Fin n → Fin b) :
    encodeBase b (List.ofFn fun i => (v i).val) = (finFunctionFinEquiv v).val := by
  rw [finFunctionFinEquiv_apply]
  induction n with
  | zero => simp [encodeBase]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    simp only [encodeBase, Nat.ofDigits, Nat.cast_id, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    rw [show Nat.ofDigits b (List.ofFn fun i : Fin n => (v i.succ).val) = _ from ih (v ∘ Fin.succ)]
    simp [pow_succ', Finset.mul_sum, Nat.mul_left_comm]

variable {G H : Type} (g : Numbering G) (h : Numbering H)

theorem encodeBase_arrow (f : G → H) :
    encodeBase h.size (g.all.map fun x => (h.equiv (f x)).val) = ((g.arrow h).equiv f).val := by
  change _ = (finFunctionFinEquiv (fun i : Fin g.size => h.equiv (f (g.equiv.symm i)))).val
  rw [← encodeBase_ofFn, all, List.map_map, List.ofFn_eq_map]
  rfl

theorem digit_arrow_symm (c : Fin (g.arrow h).size) (x : G) :
    digit h.size c.val (g.equiv x).val = (h.equiv ((g.arrow h).equiv.symm c x)).val := by
  change _ = (h.equiv (h.equiv.symm (finFunctionFinEquiv.symm c (g.equiv x)))).val
  rw [Equiv.apply_symm_apply]
  rfl

theorem digit_arrow (f : G → H) (x : G) :
    digit h.size ((g.arrow h).equiv f).val (g.equiv x).val = (h.equiv (f x)).val := by
  rw [digit_arrow_symm, Equiv.symm_apply_apply]

theorem decodeBase_arrow_symm (c : Fin (g.arrow h).size) :
    decodeBase h.size c.val g.size = g.all.map fun x => (h.equiv ((g.arrow h).equiv.symm c x)).val := by
  apply List.ext_getElem
  · simp [decodeBase, all]
  · intro j hj hk
    have hlt : j < g.size := by simpa [decodeBase] using hj
    simpa [decodeBase, all] using digit_arrow_symm g h c (g.equiv.symm ⟨j,hlt⟩)

end CommonAlphabet.Numbering

end NearSquareRoot
end Computability
end OAI
