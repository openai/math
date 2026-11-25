import OAI.Computability.BorderVNP.ResidueBoxIndex
import OAI.Computability.BorderVNP.ResiduePinsBasis
import OAI.Computability.VPVNP.RAMSerialization

/-!
# Binary pin fields and padded residue indices

A pin stores one finite-field basis coordinate followed by the Laurent
exponents, all in fixed-width binary fields. Adding the box radius encodes
signed exponents. Extra binary words are rejected by coordinate range tests,
so a program never indexes an array by the entire matrix index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open ResiduePins ResidueBox VPVNP.RAMSerialization VPVNP.BurstRAM
open scoped Classical

/-- One binary field encoding each allowed index exactly once. -/
structure PinCodec (I : Type*) (d : ℕ) where
  /-- Canonical pin bits for the index. -/
  encode : I → Fin d → Bool
  /-- Range-check all fields and recover the index, or reject the word. -/
  decode : (Fin d → Bool) → Option I
  /-- Successful words have exactly one canonical representation. -/
  decode_eq_some : ∀ b i, decode b = some i ↔ b = encode i

variable {h β H w : ℕ}

/-- The basis address, shifted time exponent and shifted parameter exponents, in field order. -/
def pinWords (hβ : β ≤ 2^w) (hH : 2*H < 2^w) (i : Index (Fin β) (Fin h) H) :
    Fin (h+2) → Word w :=
  let x (k : Option (Fin h)) : Word w :=
    ⟨(i.2.val k + H).toNat, by
      have bound : i.2.val k ≤ H := by cases k with
        | none => exact i.2.property.1.2
        | some j => exact (i.2.property.2 j).2
      omega⟩
  Fin.cons (i.1.castLE hβ) (Fin.cons (x none) fun j => x (some j))

/-- Admissible binary fields for a pin, with nonnegative parameter exponents. -/
def within (β H : ℕ) (a : Fin (h+2) → Word w) : Prop :=
  (a 0).val < β ∧ (a 1).val ≤ 2*H ∧
    ∀ j : Fin h, H ≤ (a j.succ.succ).val ∧ (a j.succ.succ).val ≤ 2*H

private def wordsIndex (a : Fin (h+2) → Word w) (ha : within β H a) : Index (Fin β) (Fin h) H :=
  (⟨(a 0).val, ha.1⟩, ⟨fun k => match k with
    | none => ((a 1).val : ℤ) - H
    | some j => ((a j.succ.succ).val : ℤ) - H, by
      refine ⟨⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
      · change - (H : ℤ) ≤ ((a 1).val : ℤ) - H
        omega
      · change ((a 1).val : ℤ) - H ≤ H
        have := ha.2.1; omega
      · change 0 ≤ ((a j.succ.succ).val : ℤ) - H
        have := (ha.2.2 j).1; omega
      · change ((a j.succ.succ).val : ℤ) - H ≤ H
        have := (ha.2.2 j).2; omega⟩)

private theorem pinWords_valid (hβ : β ≤ 2^w) (hH : 2*H < 2^w) (i : Index (Fin β) (Fin h) H) :
    within β H (pinWords hβ hH i) := by
  refine ⟨by simp [pinWords], ?_, fun j => ?_⟩
  · change (i.2.val none + H).toNat ≤ 2*H
    have := i.2.property.1.2; omega
  · change H ≤ (i.2.val (some j) + H).toNat ∧ (i.2.val (some j) + H).toNat ≤ 2*H
    have := i.2.property.2 j; omega

private theorem wordsIndex_pinWords (hβ : β ≤ 2^w) (hH : 2*H < 2^w)
    (i : Index (Fin β) (Fin h) H) : wordsIndex (pinWords hβ hH i) (pinWords_valid ..) = i := by
  apply Prod.ext
  · apply Fin.ext; rfl
  · apply Subtype.ext; funext k
    cases k with
    | none =>
      change (((i.2.val none + H).toNat : ℕ) : ℤ) - H = i.2.val none
      have := i.2.property.1.1; omega
    | some j =>
      change (((i.2.val (some j) + H).toNat : ℕ) : ℤ) - H = i.2.val (some j)
      have := (i.2.property.2 j).1; omega

private theorem pinWords_wordsIndex (hβ : β ≤ 2^w) (hH : 2*H < 2^w)
    (a : Fin (h+2) → Word w) (ha : within β H a) : pinWords hβ hH (wordsIndex a ha) = a := by
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) j
  · apply Fin.ext; rfl
  · apply Fin.ext; change (((a 1).val : ℤ) - H + H).toNat = (a 1).val; simp
  · apply Fin.ext
    change (((a i.succ.succ).val : ℤ) - H + H).toNat = (a i.succ.succ).val
    simp

/-- Explicit coding used by the live and substituted pins of a numbered
residue chart. Only individual `w`-bit words are decoded. -/
noncomputable def boxPinCodec (h : ℕ) (hβ : β ≤ 2^w) (hH : 2*H < 2^w) :
    PinCodec (Index (Fin β) (Fin h) H) ((h+2)*w) where
  encode i := arrayBits _ _ (pinWords hβ hH i)
  decode b :=
    let a := (arrayBits _ _).symm b
    if ha : within β H a then some (wordsIndex a ha) else none
  decode_eq_some b i := by
    let a := (arrayBits _ _).symm b
    change (if ha : within β H a then some (wordsIndex a ha) else none) = some i ↔ _
    constructor
    · split_ifs with ha
      · intro he
        obtain rfl := Option.some.inj he
        rw [pinWords_wordsIndex]
        exact ((arrayBits _ _).apply_symm_apply _).symm
      · simp
    · rintro rfl
      have he : a = pinWords hβ hH i := (arrayBits _ _).symm_apply_apply _
      have ha : within β H a := he ▸ pinWords_valid hβ hH i
      rw [dite_eq_left ha]
      congr 1
      simpa only [he] using wordsIndex_pinWords hβ hH i

/-- The box codec accepts exactly when its decoded words pass the component range checks. -/
theorem boxPinCodec_decode_isSome_iff (hβ : β ≤ 2^w) (hH : 2*H < 2^w)
    (b : Fin ((h+2)*w) → Bool) :
    ((boxPinCodec h hβ hH).decode b).isSome = true ↔ within β H ((arrayBits (h+2) w).symm b) := by
  simp only [boxPinCodec]
  split_ifs <;> simp_all

/-- A chosen bit of a chosen pin field is an actual little-endian array bit. -/
theorem boxPinCodec_encode_word_get (hβ : β ≤ 2^w) (hH : 2*H < 2^w)
    (i : Index (Fin β) (Fin h) H) (f : Fin (h+2)) (j : Fin w) :
    (boxPinCodec h hβ hH).encode i (finProdFinEquiv (f,j)) =
      VPVNP.RAMSerialization.wordBits w (pinWords hβ hH i f) j := arrayBits_at ..

/-- Extending a contribution by zero on all rejected binary indices preserves
its finite sum. This includes all extra rows of the padded matrix. -/
theorem PinCodec.sum_decode {I A : Type*} [Fintype I] [AddCommMonoid A] {d : ℕ}
    (codec : PinCodec I d) (f : I → A) :
    ∑ b, (codec.decode b).elim 0 f = ∑ i, f i := by
  have henc (i) := (codec.decode_eq_some (codec.encode i) i).mpr rfl
  let inc : I ↪ (Fin d → Bool) := ⟨codec.encode, fun i j he =>
    Option.some.inj ((henc i).symm.trans (he ▸ henc j))⟩
  calc
    _ = ∑ b ∈ Finset.univ.map inc, (codec.decode b).elim 0 f := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro b _ hb
      cases h : codec.decode b with
      | none => rfl
      | some i =>
        exact (hb (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, ((codec.decode_eq_some _ _).mp h).symm⟩)).elim
    _ = _ := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (codec.decode (codec.encode i)).elim 0 f = _
      rw [henc]
      rfl

end Diagonal

end BorderVNP
end Computability
end OAI
