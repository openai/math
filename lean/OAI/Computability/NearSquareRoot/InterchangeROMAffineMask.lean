import OAI.Computability.IntegerMultiplication.Carry.Remainder
import OAI.Computability.IntegerMultiplication.Carry.Shrink
import Mathlib.Data.Nat.ModEq

/-! # Binary arithmetic for affine routing masks

A class specifies the two high carries of a congruence. Its low residue and
the other side's high carry determine a candidate address by ordinary exact
division, both forward and backward. The control program is fixed for all
radices, coefficients, field widths, directions, and carry pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAffineMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
  IntegerMultiplication.Carry

/-- The coefficients of a row are the slope, the coefficient of the control
field, and the constant offset. -/
abbrev Row (α : Type) := α × α × α
abbrev Geometry (α : Type) := α × Row α × Row α
abbrev Class (α : Type) := α × α
abbrev Header (α : Type) := Geometry α × Class α
abbrev Query := Header Word × Word × Word

def offset (r : Row ℕ) (c : ℕ) := r.2.1*c+r.2.2
def stamp (r : Row ℕ) (c x : ℕ) := r.1*x+offset r c

def values (r : Row Word) : Row ℕ := (value r.1,value r.2.1,value r.2.2)

def offsetWord (p : Row Word × Word) : Word :=
  Bits.add (school (p.1.2.1,p.2),p.1.2.2)

def stampWord (p : Row Word × Word × Word) : Word :=
  Bits.add (school (p.1.1,p.2.2),offsetWord (p.1,p.2.1))

@[fun_prop] private theorem offset_poly : Poly offsetWord := by unfold offsetWord; fun_prop
@[fun_prop] private theorem stamp_poly : Poly stampWord := by
  unfold stampWord offsetWord
  fun_prop

@[simp] private theorem offset_value (r : Row Word) (c : Word) :
    value (offsetWord (r,c)) = offset (values r) (value c) := by
  simp [offsetWord,add_val,offset,values]
@[simp] private theorem stamp_value (r : Row Word) (c x : Word) :
    value (stampWord (r,c,x)) = stamp (values r) (value c) (value x) := by
  simp [stampWord,add_val,stamp,values]

/-- Numerical equality allows non-canonical words. -/
def eqWord (p : Word × Word) := !(lt_ p || lt_ p.swap)

@[fun_prop] private theorem negPoly {X : Type} [Codec X] {f : X → Bool} (h : Poly f) :
    Poly (fun x => !(f x)) := h.compose (Easy.finite Bool.not).poly

@[fun_prop] private theorem andPoly {X : Type} [Codec X] {f g : X → Bool} (h : Poly f) (j : Poly g) :
    Poly (fun x => f x && g x) := (h.pair j).compose (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

@[fun_prop] private theorem orPoly {X : Type} [Codec X] {f g : X → Bool} (h : Poly f) (j : Poly g) :
    Poly (fun x => f x || g x) := (h.pair j).compose (Easy.finite (fun p : Bool × Bool => p.1 || p.2)).poly

@[fun_prop] private theorem eq_poly : Poly eqWord := by
  unfold eqWord Prod.swap
  fun_prop

@[simp] theorem eqWord_true (x y : Word) : eqWord (x,y) = true ↔ value x = value y := by
  simp [eqWord,lt_r]
  omega

/-- Input consists of the modulus and the two rows, the two requested
carries, and the earlier and current address words. Reverse routing swaps
the two rows and the two carries. -/
def inspect (i : Query) : Bool :=
  let shape := i.1.1
  let M := shape.1
  let A := shape.2.1
  let B := shape.2.2
  let c := i.2.1
  let z := nat_div (stampWord (A,c,i.2.2),M)
  let t := Bits.add (z.2,school (M,i.1.2.2))
  let q := offsetWord (B,c)
  let d := nat_div (sub0 (t,q),B.1)
  eqWord (z.1,i.1.2.1) && !(lt_ (t,q)) && eqWord (d.2,[]) && lt_ (d.1,M)

theorem inspect_poly : Poly inspect := by
  unfold inspect
  fun_prop

/-- Arithmetic specification of the mask. -/
def selects (M : ℕ) (A B : Row ℕ) (k l c x : ℕ) : Prop :=
  let z := stamp A c x
  let t := z%M+M*l
  let q := offset B c
  z/M=k ∧ q≤t ∧ (t-q)%B.1=0 ∧ (t-q)/B.1<M

theorem inspect_true (M : Word) (A B : Row Word) (k l c x : Word) :
    inspect (((M,A,B),(k,l)),c,x) = true ↔
      selects (value M) (values A) (values B) (value k) (value l) (value c) (value x) := by
  let z := nat_div (stampWord (A,c,x),M)
  let t := Bits.add (z.2,school (M,l))
  let q := offsetWord (B,c)
  let d := nat_div (sub0 (t,q),B.1)
  have u := division_rules (stampWord (A,c,x)) M
  have v := division_rules (sub0 (t,q)) B.1
  change value z.1 = _ ∧ value z.2 = _ at u
  change value d.1 = _ ∧ value d.2 = _ at v
  have te : value t = stamp (values A) (value c) (value x) % value M + value M*value l := by
    simp only [t,add_val,u.2,stamp_value,school_exact]
  change (eqWord (z.1,k) && !(lt_ (t,q)) && eqWord (d.2,[]) && lt_ (d.1,M)) = true ↔ _
  simp only [Bool.and_eq_true,Bool.not_eq_true',eqWord_true,lt_r,decide_eq_true_eq,decide_eq_false_iff_not,
    not_lt,value_nil,u.1,v.1,v.2,stamp_value,sub0_v,te,q,offset_value,selects,values]
  tauto

theorem selects_iff {M : ℕ} (hM : 0<M) {A B : Row ℕ} (hB : 0<B.1) (k l c x : ℕ) :
    selects M A B k l c x ↔ stamp A c x/M=k ∧
      ∃ y<M, stamp B c y/M=l ∧ stamp A c x % M = stamp B c y % M := by
  let z := stamp A c x
  let t := z%M+M*l
  let q := offset B c
  change (z/M=k ∧ q≤t ∧ (t-q)%B.1=0 ∧ (t-q)/B.1<M) ↔
    z/M=k ∧ ∃ y<M, (B.1*y+q)/M=l ∧ z%M=(B.1*y+q)%M
  constructor
  · rintro ⟨hk,hle,h0,hl⟩
    let y := (t-q)/B.1
    have e : B.1*y+q=t := by
      have a := Nat.mod_add_div (t-q) B.1
      rw [h0,Nat.zero_add] at a
      change B.1*((t-q)/B.1)+q=t
      omega
    refine ⟨hk,y,hl,?_,?_⟩
    · rw [e]
      simp [t,Nat.add_mul_div_left _ _ hM,Nat.div_eq_of_lt (Nat.mod_lt z hM)]
    · rw [e]
      simp [t]
  · rintro ⟨hk,y,hy,hl,hr⟩
    have e : B.1*y+q=t := by
      have a := Nat.mod_add_div (B.1*y+q) M
      rw [hl,←hr] at a
      exact a.symm
    have le : q ≤ t := by omega
    have diff : t-q = B.1*y := by omega
    refine ⟨hk,le,?_,?_⟩
    · simp [diff]
    · simpa [diff,Nat.mul_div_cancel_left _ hB] using hy

/-- For a unit slope the shared low residue determines the other address
uniquely, hence the predicate recognizes exactly the two true carries. -/
theorem selects_of_pair {M : ℕ} (hM : 0<M) {A B : Row ℕ} (hB : 0<B.1)
    (unit : Nat.Coprime M B.1) {c x y : ℕ} (hy : y<M)
    (link : stamp A c x % M = stamp B c y % M) (k l : ℕ) :
    selects M A B k l c x ↔ stamp A c x/M=k ∧ stamp B c y/M=l := by
  rw [selects_iff hM hB]
  constructor
  · rintro ⟨hk,v,hv,hl,hr⟩
    have agree : Nat.ModEq M (B.1*v) (B.1*y) :=
      Nat.ModEq.add_right_cancel' (offset B c) (hr.symm.trans link)
    have e := Nat.ModEq.cancel_left_of_coprime unit agree
    have same : v=y := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt hy] using e
    exact ⟨hk,same ▸ hl⟩
  · rintro ⟨hk,hl⟩
    exact ⟨hk,y,hy,hl,link⟩

end InterchangeAffineMask

end NearSquareRoot
end Computability
end OAI
