import OAI.Computability.NearSquareRoot.ScheduleGeneratorPresentation

/-! # Uniform arithmetic for a one-hot alphabet block -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.OneHot

open CommonAlphabet

/-- Output digit of the block for the symbol of rank `rank`. -/
def encode (rank blank j : ℕ) : ℕ := if rank ≠ blank ∧ j = rank then 2 else 0

/-- The index of the first mark, with the blank rank as the default. -/
def decode (blank : ℕ) (digits : List ℕ) : ℕ :=
  let i := digits.idxOf 2
  if i < digits.length then i else blank

variable {X : Type*} [Primcodable X]

theorem primrec_encode {r b k : X → ℕ} (hr : Primrec r) (hb : Primrec b) (hk : Primrec k) :
    Primrec fun x => encode (r x) (b x) (k x) :=
  Primrec.ite ((Primrec.eq.comp hr hb).not.and (Primrec.eq.comp hk hr))
    (Primrec.const 2) (Primrec.const 0)

theorem computable_encode {r b k : X → ℕ} (hr : Computable r) (hb : Computable b) (hk : Computable k) :
    Computable fun x => encode (r x) (b x) (k x) :=
  (primrec_encode Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp.comp
    (hr.pair (hb.pair hk))

theorem primrec_decode : Primrec₂ decode := by
  have idx := Primrec.list_idxOf.comp (Primrec.const (α := ℕ × List ℕ) 2) Primrec.snd
  exact Primrec.ite (Primrec.nat_lt.comp idx (Primrec.list_length.comp Primrec.snd)) idx Primrec.fst

variable {A : Type} {n : ℕ} (e : A ≃ Fin n) (blank : A)

theorem encode_oneHot (x : A) (i : Fin n) :
    encode (e x).val (e blank).val i.val =
      (Numbering.ternary.equiv ((oneHot e blank).enc x i)).val := by
  change encode _ _ _ =
    (Numbering.ternary.equiv (if e x ≠ e blank ∧ i = e x then some true else none)).val
  simp only [encode, ne_eq, Fin.val_inj]
  split <;> rfl

theorem decode_oneHot (bits : Fin n → Option Bool) :
    decode (e blank).val (List.ofFn fun i => (Numbering.ternary.equiv (bits i)).val) =
      (e ((oneHot e blank).dec bits)).val := by
  let mark := fun i => bits i == some true
  have ord (s : Option Bool) :
      ((Numbering.ternary.equiv s).val == 2) = (s == some true) := by
    rcases s with _ | (_ | _) <;> rfl
  have idx : (List.ofFn fun i => (Numbering.ternary.equiv (bits i)).val).idxOf 2 =
      (List.finRange n).findIdx mark := by
    rw [List.ofFn_eq_map, List.idxOf, List.findIdx_map]
    congr 1
    exact funext fun i => ord (bits i)
  unfold decode
  rw [idx, List.length_ofFn]
  change _ = (e ((((List.finRange n).find? mark).map e.symm).getD blank)).val
  rw [List.find?_eq_getElem?_findIdx]
  by_cases h : (List.finRange n).findIdx mark < n <;> simp [h]

theorem decode_oneHot_all (bits : Fin n → Option Bool) :
    decode (e blank).val ((Numbering.fin n).all.map fun i => (Numbering.ternary.equiv (bits i)).val) =
      (e ((oneHot e blank).dec bits)).val := by
  rw [← decode_oneHot e blank bits, Numbering.all, List.map_map, List.ofFn_eq_map]
  rfl

end Generator.OneHot

end NearSquareRoot
end Computability
end OAI
