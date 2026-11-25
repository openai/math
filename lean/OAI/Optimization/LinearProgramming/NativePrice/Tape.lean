import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Scalar 0/1 tapes for the interleaved little-endian bit protocol. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

/-- At the supplied base, each protocol bit is its scalar value zero or one. -/
def WordAt {K : Type*} [NatCast K] (s : Memory K) (base : ℕ) (w : Word) : Prop :=
  ∀ j (hj : j<w.length), s.data (base+j) = (w[j].toNat : K)

variable {K : Type*} [NatCast K] {s t : Memory K} {c : ℕ} {b : Bool} {u v : Word}

theorem wordAt_cons : WordAt s c (b::u) ↔
    s.data c = (b.toNat : K) ∧ WordAt s (c+1) u := by
  constructor
  · intro h
    constructor
    · have e := h 0 (by simp)
      change s.data (c+0)=(b.toNat:K) at e
      exact e
    · intro j hj
      have e := h (j+1) (by simpa using hj)
      change s.data (c+(j+1))=(u[j].toNat:K) at e
      simpa only [show c+1+j=c+(j+1) by omega] using e
  · rintro ⟨hb,ht⟩ (_|j) hj
    · simpa using hb
    · simpa [Nat.add_assoc,Nat.add_comm 1 j] using ht j (by simpa using hj)

theorem wordAt_append : WordAt s c (u++v) ↔ WordAt s c u ∧ WordAt s (c+u.length) v := by
  induction u generalizing c with
  | nil => simp [WordAt]
  | cons b u ih =>
    rw [List.cons_append,wordAt_cons,ih,wordAt_cons]
    simp only [List.length_cons]
    rw [show c+(u.length+1) = c+1+u.length by omega]
    tauto

theorem WordAt.of_data (h : WordAt s c u)
    (he : ∀ j, c ≤ j → j < c+u.length → t.data j=s.data j) : WordAt t c u := by
  intro j hj
  exact (he _ (by omega) (by omega)).trans (h j hj)

theorem frameLen (bs : Word) : (frame bs).length = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (true::b::frame bs).length=_
    simp only [List.length_cons,ih]
    omega

/-- Every marker and payload is in its explicit paired position. -/
theorem frame_cells {K : Type*} [AddMonoidWithOne K] (s : Memory K) (base : ℕ) (bs : Word)
    (h : WordAt s base (frame bs)) :
    (∀ j, j ≤ bs.length → s.data (base+2*j) = if j<bs.length then 1 else 0) ∧
    ∀ j (hj : j<bs.length), s.data (base+2*j+1) = (bs[j].toNat : K) := by
  induction bs generalizing base with
  | nil =>
    have endBit : s.data base = 0 := by simpa [frame] using h 0 (by decide)
    constructor
    · rintro j hj
      have j0 : j=0 := by simpa using hj
      simp [j0,endBit]
    · simp
  | cons b bs ih =>
    change WordAt s base (true::b::frame bs) at h
    obtain ⟨marker,rest⟩ := wordAt_cons.mp h
    obtain ⟨payload,tail⟩ := wordAt_cons.mp rest
    obtain ⟨hm,hp⟩ := ih (base+1+1) tail
    constructor
    · rintro (_|j) hj
      · simpa using marker
      · have eq := hm j (by simpa using hj)
        simpa only [List.length_cons,Nat.add_lt_add_iff_right,
          show base+1+1+2*j=base+2*(j+1) by omega] using eq
    · rintro (_|j) hj
      · simpa using payload
      · have eq := hp j (by simpa using hj)
        simpa only [List.getElem_cons_succ,
          show base+1+1+2*j+1=base+2*(j+1)+1 by omega] using eq

def value (bs : Word) : ℕ := bs.foldr Nat.bit 0

theorem value_bits (n : ℕ) : value n.bits=n := by
  unfold value
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h,List.foldr_cons,ih]

theorem value_cons (b : Bool) (bs : Word) : value (b::bs) = 2*value bs+b.toNat := by
  cases b <;> simp [value,Nat.bit]

theorem value_lt (bs : Word) : value bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    rw [value_cons,List.length_cons,pow_succ]
    cases b <;> simp_all <;> omega

/-- One more most-significant-first Horner update when traversing little-endian data backwards. -/
theorem value_drop_step (bs : Word) (j : ℕ) (hj : j<bs.length) :
    value (bs.drop j) = 2*value (bs.drop (j+1))+bs[j].toNat := by
  rw [List.drop_eq_getElem_cons hj,value_cons]

end NativePrice
end LinearProgramming
end Optimization
end OAI
