import OAI.Computability.NearSquareRoot.InterchangeROMAffineMask
import OAI.Computability.NearSquareRoot.InterchangeROMLagEquation
import Mathlib.Data.List.Nodup

/-! # Monotone classes of a rational affine address permutation

A fixed high carry on either side converts residue order into ordinary
integer order. This proves stability through an entire addressed field.
The literal mask test computes the carry of the unknown partner without
enumerating the field.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAffineMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits
  IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Strip

variable {p f : ℕ}

def sourceKey (M : ℕ) (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f) (x : Block p f) :
    Class ℕ := (stamp A c (number x)/M,stamp B c (number (op x))/M)

def destKey (M : ℕ) (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f) :=
  sourceKey M A B c op ∘ op.symm

/-- The classwise monotonicity only uses positive source slope and
nonnegative destination slope. -/
def ranger [NeZero p] (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f) (pos : 0<A.1)
    (link : ∀ x, stamp A c (number x) % p^f = stamp B c (number (op x)) % p^f) :
    Ranger (line p f) (line p f) (sourceKey (p^f) A B c op) (destKey (p^f) A B c op) where
  run := op
  same x := by simp [destKey]
  spot := number
  next := number
  ps := clean p f
  pt := clean p f
  mono x y h hxy := by
    let M := p^f
    have a : stamp A c (number x)/M = stamp A c (number y)/M := congrArg Prod.fst h
    have b : stamp B c (number (op x))/M = stamp B c (number (op y))/M := congrArg Prod.snd h
    have ax := Nat.mod_add_div (stamp A c (number x)) M
    have ay := Nat.mod_add_div (stamp A c (number y)) M
    have bx := Nat.mod_add_div (stamp B c (number (op x))) M
    have by' := Nat.mod_add_div (stamp B c (number (op y))) M
    rw [a] at ax
    rw [b] at bx
    have lx : _ % M = _ % M := link x
    have ly : _ % M = _ % M := link y
    have gain : stamp A c (number x) < stamp A c (number y) :=
      Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hxy pos) _
    by_contra! back
    have loss : stamp B c (number (op y)) ≤ stamp B c (number (op x)) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ back) _
    omega

def encoded (a : Row ℕ) : Row Word := (born a.1,born a.2.1,born a.2.2)

def literal (M : ℕ) (A B : Row ℕ) (k : Class ℕ) : Header Word :=
  ((born M,encoded A,encoded B),(born k.1,born k.2))

@[simp] theorem values_encoded (a : Row ℕ) : values (encoded a) = a := by
  simp [encoded,values,birthValue]

theorem inspect_source [NeZero p] (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f)
    (pos : 0<B.1) (unit : Nat.Coprime (p^f) B.1)
    (link : ∀ x, stamp A c (number x) % p^f = stamp B c (number (op x)) % p^f)
    (x : Block p f) (k : Class ℕ) (wc wx : Word) (hc : value wc=c) (hx : value wx=number x) :
    inspect (literal (p^f) A B k,wc,wx) = decide (sourceKey (p^f) A B c op x = k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [literal,inspect_true,birthValue,values_encoded,hx,hc,decide_eq_true_eq]
  rw [selects_of_pair (Nat.pow_pos (NeZero.pos p)) pos unit (number_lt (op x)) (link x)]
  simp only [sourceKey,Prod.ext_iff]

theorem inspect_dest [NeZero p] (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f)
    (pos : 0<A.1) (unit : Nat.Coprime (p^f) A.1)
    (link : ∀ x, stamp A c (number x) % p^f = stamp B c (number (op x)) % p^f)
    (y : Block p f) (k : Class ℕ) (wc wy : Word) (hc : value wc=c) (hy : value wy=number y) :
    inspect (literal (p^f) B A k.swap,wc,wy) = decide (destKey (p^f) A B c op y = k) := by
  have eq := (link (op.symm y)).symm
  rw [Equiv.apply_symm_apply] at eq
  apply Bool.eq_iff_iff.mpr
  simp only [literal,inspect_true,birthValue,values_encoded,hy,hc,decide_eq_true_eq,Prod.swap]
  rw [selects_of_pair (Nat.pow_pos (NeZero.pos p)) pos unit (number_lt (op.symm y)) eq]
  simp only [destKey,sourceKey,Function.comp_apply,Equiv.apply_symm_apply,Prod.ext_iff]
  tauto

/-- All possible carries lie in a rectangle independent of the address width. -/
def colors (A B : Row ℕ) : List (Class ℕ) :=
  (List.range (A.1+A.2.1+A.2.2+1)).product (List.range (B.1+B.2.1+B.2.2+1))

theorem colors_nodup (A B : Row ℕ) : (colors A B).Nodup :=
  List.Nodup.product List.nodup_range List.nodup_range

private theorem carry_bound {M c x : ℕ} (hm : 0<M) (hc : c≤M) (hx : x≤M) (A : Row ℕ) :
    stamp A c x/M ≤ A.1+A.2.1+A.2.2 := by
  have ht : stamp A c x ≤ (A.1+A.2.1+A.2.2)*M := by
    have h1 := Nat.mul_le_mul_left A.1 hx
    have h2 := Nat.mul_le_mul_left A.2.1 hc
    have h3 := Nat.mul_le_mul_left A.2.2 hm
    simp only [Nat.mul_one] at h3
    simp only [stamp,offset,Nat.add_mul]
    omega
  simpa only [Nat.mul_div_cancel _ hm] using Nat.div_le_div_right (c:=M) ht

theorem covers [NeZero p] (A B : Row ℕ) {c : ℕ} (hc : c≤p^f) (op : Block p f ≃ Block p f)
    (x : Block p f) : sourceKey (p^f) A B c op x ∈ colors A B := by
  apply List.mem_product.2
  simp only [List.mem_range]
  exact ⟨Nat.lt_succ_of_le (carry_bound (Nat.pow_pos (NeZero.pos p)) hc (number_lt x).le A),
    Nat.lt_succ_of_le (carry_bound (Nat.pow_pos (NeZero.pos p)) hc (number_lt (op x)).le B)⟩

end InterchangeAffineMask

end NearSquareRoot
end Computability
end OAI
