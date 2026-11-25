import OAI.ThreeFlat.Diagonal.ShrinkGraph
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # The tag-XOR row emitted for an unused shrinking slot -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open scoped Fin.NatCast
variable {t w n : ℕ} {V L : Type*} [AddCommGroup L]

def tagOne (pos : 0<t) : BitWord t := (tagOrdinal t).symm ⟨1,Nat.one_lt_two_pow pos.ne'⟩

theorem tagOne_ne (pos : 0<t) : tagOne pos ≠ 0 := by
  intro h
  have hz : (tagOrdinal t (0 : BitWord t)).val = 0 := by
    have := tagOrdinal_add (0 : BitWord t) 0
    simpa only [zero_add,Nat.xor_self] using this
  have he := congrArg (fun x => (tagOrdinal t x).val) h
  simp [tagOne,hz] at he

theorem packed_tag_xor (b : ℕ) (z u : BitWord t) :
    (b*2^t+(tagOrdinal t z).val) ^^^ (tagOrdinal t u).val =
      b*2^t+(tagOrdinal t (z+u)).val := by
  let x := b*2^t+(tagOrdinal t z).val
  let y := (tagOrdinal t u).val
  have low : x%2^t=(tagOrdinal t z).val := by simp [x,Nat.mod_eq_of_lt (tagOrdinal t z).isLt]
  have high : x/2^t=b := by simp [x,Nat.mul_comm b (2^t),Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (tagOrdinal t z).isLt]
  have raw := (Nat.mod_add_div (x^^^y) (2^t)).symm
  rw [Nat.xor_mod_two_pow,Nat.xor_div_two_pow,low,high,Nat.mod_eq_of_lt (tagOrdinal t u).isLt,
    Nat.div_eq_of_lt (tagOrdinal t u).isLt,Nat.xor_zero] at raw
  rw [tagOrdinal_add]
  exact raw.trans (by rw [Nat.mul_comm (2^t) b,Nat.add_comm])

theorem padding_neighbor (base : V → ℕ) (pos : 0<t) (rev : Bool) (v : V) (tag : BitWord t)
    (i : Fin n) :
    let G := tagPadding (V:=V) (L:=L) (tagOne pos) (tagOne_ne pos) n
    let a := (if rev then G.base.target.symm else G.base.target) ((v,tag),i)
    (base v*2^t+(tagOrdinal t tag).val) ^^^ 1 =
      base a.1.1*2^t + (tagOrdinal t a.1.2).val := by
  have key := packed_tag_xor (base v) tag (tagOne pos)
  have neg : -(tagOne pos) = tagOne pos := by
    funext j
    exact (by decide : ∀ z : Fin 2, -z=z) _
  cases rev
  · simpa [tagPadding,tagOne] using key
  · have castNeg : -((tagOrdinal t).symm ⟨1,Nat.one_lt_two_pow pos.ne'⟩) =
        (tagOrdinal t).symm ⟨1,Nat.one_lt_two_pow pos.ne'⟩ := neg
    simpa [tagPadding,sub_eq_add_neg,tagOne,castNeg] using key

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
