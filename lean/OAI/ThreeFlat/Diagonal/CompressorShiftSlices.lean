import OAI.ThreeFlat.Diagonal.CompressorLaneSplit
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Reading coordinate slices of a single physical XOR-shift word -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open scoped Fin.NatCast BigOperators
variable {w k n a b : ℕ}

theorem ordinal_sum (v : BitWord a) :
    (tagOrdinal a v).val = ∑ i, (v i).val * 2^i.val := rfl

theorem ordinal_split (v : BitWord (a+b)) :
    (tagOrdinal (a+b) v).val =
      (tagOrdinal a (splitWord a b v).1).val + 2^a * (tagOrdinal b (splitWord a b v).2).val := by
  rw [ordinal_sum,Fin.sum_univ_add,ordinal_sum,ordinal_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [splitWord,Fin.val_natAdd,Nat.pow_add]
  ring

theorem split_low (v : BitWord (a+b)) :
    (tagOrdinal (a+b) v).val % 2^a = (tagOrdinal a (splitWord a b v).1).val := by
  rw [ordinal_split]
  simp [Nat.add_mod,Nat.mod_eq_of_lt (tagOrdinal a (splitWord a b v).1).isLt]

theorem split_high (v : BitWord (a+b)) :
    (tagOrdinal (a+b) v).val / 2^a = (tagOrdinal b (splitWord a b v).2).val := by
  rw [ordinal_split,Nat.mul_comm (2^a),Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (tagOrdinal a (splitWord a b v).1).isLt,Nat.zero_add]

/-- The low field of known power-of-two radix. -/
def lowTerm (value radix : Term w k n) : Term w k n := .binary .mod value radix

/-- The unconsumed high field is the quotient. -/
def highTerm (value radix : Term w k n) : Term w k n := .binary .div value radix

theorem lowWord (fit : a+b ≤ w) (v : BitWord (a+b)) (radix : Word w) (hr : radix.val=2^a) :
    BinaryOp.mod.eval (tagWord fit v) radix =
      tagWord (show a ≤ w by omega) (splitWord a b v).1 := by
  apply Fin.ext
  have bound := (tagWord (show a ≤ w by omega) (splitWord a b v).1).isLt
  simpa [BinaryOp.eval,tagWord,hr,split_low,Nat.mod_eq_of_lt] using
    Nat.mod_eq_of_lt bound

theorem highWord (fit : a+b ≤ w) (v : BitWord (a+b)) (radix : Word w) (hr : radix.val=2^a) :
    BinaryOp.div.eval (tagWord fit v) radix =
      tagWord (show b ≤ w by omega) (splitWord a b v).2 := by
  apply Fin.ext
  have bound := (tagWord (show b ≤ w by omega) (splitWord a b v).2).isLt
  simpa [BinaryOp.eval,tagWord,hr,split_high,Nat.mod_eq_of_lt] using
    Nat.mod_eq_of_lt bound

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
