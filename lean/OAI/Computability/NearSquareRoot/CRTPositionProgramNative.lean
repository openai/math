import OAI.Computability.NearSquareRoot.CRTPositionNativeOp

/-! # Position programs on native binary blocks

The bits of the destination address are the original bits read through the
position permutation. A payload found at a given destination therefore comes
from the address obtained by reading its bits through the inverse permutation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic Reflections

/-- Reindex the bits of a native block by a permutation of positions. -/
noncomputable def permuteNative {k : ℕ} (p : Equiv.Perm (Fin k)) : Equiv.Perm (Block 2 k) :=
  let e : Equiv.Perm (Fin k → Bool) := {
    toFun w := w ∘ p
    invFun w := w ∘ p.symm
    left_inv w := funext fun j => by simp
    right_inv w := funext fun j => by simp }
  ((nativeWord k).trans e).trans (nativeWord k).symm

@[simp] theorem permuteNative_bits {k : ℕ} (p : Equiv.Perm (Fin k)) (b : Block 2 k) :
    prefixBit (permuteNative p b) = prefixBit b ∘ p :=
  (nativeWord k).apply_symm_apply _

@[simp] theorem permuteNative_symm_bits {k : ℕ} (p : Equiv.Perm (Fin k)) (b : Block 2 k) :
    prefixBit ((permuteNative p).symm b) = prefixBit b ∘ p.symm :=
  (nativeWord k).apply_symm_apply _

variable {k G : ℕ} (op : Op → Block 2 k → Block 2 k)

/-- One native implementation of a correctly interpreted opcode is involutive. -/
theorem native_involutive_of_bits (q : Op)
    (bits : ∀ b, prefixBit (op q b) = act G (prefixBit b) q) : Function.Involutive (op q) := by
  intro b
  apply prefixBit_injective k
  rw [bits, bits, act_twice]

theorem native_fold_bits (qs : List Op) (b : Block 2 k)
    (bits : ∀ q ∈ qs, ∀ a, prefixBit (op q a) = act G (prefixBit a) q) :
    prefixBit (qs.foldl (fun a q => op q a) b) = qs.foldl (act G) (prefixBit b) := by
  induction qs generalizing b with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (op q b) (fun j hj => bits j (List.mem_cons_of_mem _ hj)),
      bits q List.mem_cons_self]

private theorem row_at_image {Y : Type*} (qs : List Op) (f : Block 2 k → Y) (b : Block 2 k)
    (inv : ∀ q ∈ qs, Function.Involutive (op q)) :
    qs.foldl (fun z q => z ∘ op q) f (qs.foldl (fun a q => op q a) b) = f b := by
  induction qs generalizing f b with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.foldl_cons, ih _ _ (fun j hj => inv j (List.mem_cons_of_mem _ hj)),
      Function.comp_apply, inv q List.mem_cons_self b]

/-- The assembled stream sends each native block to the prescribed address.
The semantic hypothesis is needed only for opcodes that the assembler emits. -/
theorem assemble_native_forward_of_mem (hG : 0 < G) (p : Equiv.Perm (Fin k))
    (bits : ∀ q ∈ assemble (tally G,table p), ∀ a, prefixBit (op q a) = act G (prefixBit a) q)
    (b : Block 2 k) :
    (assemble (tally G,table p)).foldl (fun a q => op q a) b = permuteNative p b := by
  apply prefixBit_injective k
  rw [native_fold_bits op _ b bits, assemble_action hG p, permuteNative_bits]

/-- The sequential physical updates give the inverse pullback on native rows
for arbitrary payloads. -/
theorem assemble_native_rows_of_mem {Y : Type*} (hG : 0 < G) (p : Equiv.Perm (Fin k))
    (bits : ∀ q ∈ assemble (tally G,table p), ∀ a, prefixBit (op q a) = act G (prefixBit a) q)
    (f : Block 2 k → Y) :
    (assemble (tally G,table p)).foldl (fun z q => z ∘ op q) f = f ∘ (permuteNative p).symm := by
  funext b
  have h := row_at_image op _ f ((permuteNative p).symm b)
    (fun q h => native_involutive_of_bits op q (bits q h))
  simpa only [assemble_native_forward_of_mem op hG p bits, Equiv.apply_symm_apply, Function.comp_apply] using h

theorem assemble_native_forward_of_bits (bits : ∀ q a, prefixBit (op q a) = act G (prefixBit a) q)
    (hG : 0 < G) (p : Equiv.Perm (Fin k)) (b : Block 2 k) :
    (assemble (tally G,table p)).foldl (fun a q => op q a) b = permuteNative p b :=
  assemble_native_forward_of_mem op hG p (fun q _ => bits q) b

theorem assemble_native_rows_of_bits {Y : Type*}
    (bits : ∀ q a, prefixBit (op q a) = act G (prefixBit a) q)
    (hG : 0 < G) (p : Equiv.Perm (Fin k)) (f : Block 2 k → Y) :
    (assemble (tally G,table p)).foldl (fun z q => z ∘ op q) f = f ∘ (permuteNative p).symm :=
  assemble_native_rows_of_mem op hG p (fun q _ => bits q) f

theorem assemble_native_forward (hG : 0 < G) (p : Equiv.Perm (Fin k)) (b : Block 2 k) :
    (assemble (tally G,table p)).foldl (fun a q => nativeOp k G q a) b = permuteNative p b :=
  assemble_native_forward_of_bits _ (nativeOp_bits k G) hG p b

theorem assemble_native_rows {Y : Type*} (hG : 0 < G) (p : Equiv.Perm (Fin k)) (f : Block 2 k → Y) :
    (assemble (tally G,table p)).foldl (fun z q => z ∘ nativeOp k G q) f =
      f ∘ (permuteNative p).symm :=
  assemble_native_rows_of_bits _ (nativeOp_bits k G) hG p f

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
