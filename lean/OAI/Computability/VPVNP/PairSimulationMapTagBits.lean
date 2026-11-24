import OAI.Computability.VPVNP.PairSimulationMapConsistency
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Comparing selector suffixes in their original private bit fields

The payload lengths at two incident ports can differ. Starting each cursor
above its own payload, a private scan compares every bit in their selectors.
This checks the same condition as comparing the decoded selector words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapConsistency

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifEntry PrimedInputRAM
open scoped Fin.CommRing

private theorem readField_eq_iff {len len' : ℕ} (x : Fin len → Bool) (y : Fin len' → Bool)
    (a b n : ℕ) :
    readField x a n = readField y b n ↔
      ∀ j : Fin n, paddedBit x (a + j.val) = paddedBit y (b + j.val) := by
  have digit (l r : Bool) (p q : ℕ) :
      l.toNat + 2*p = r.toNat + 2*q ↔ l = r ∧ p = q := by
    cases l <;> cases r <;> simp <;> omega
  induction n generalizing a b with
  | zero => simp [readField]
  | succ n ih =>
    simp only [readField, digit, ih (a+1) (b+1), Fin.forall_fin_succ]
    simp [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-- Flattening the copy and bit indices enumerates exactly the suffix above
the payload. This equivalence also covers zero-bit tags and zero copies. -/
theorem readTag_eq_iff_suffix {u bits v v' : ℕ}
    (x : Fin (v + u * bits) → Bool) (y : Fin (v' + u * bits) → Bool) :
    (∀ i : Fin u, readTag x i = readTag y i) ↔
      ∀ j : Fin (u * bits), x (Fin.natAdd v j) = y (Fin.natAdd v' j) := by
  have pos {a : ℕ} (z : Fin (a + u * bits) → Bool) (i : Fin u) (j : Fin bits) :
      paddedBit z (a + bits*i.val + j.val) = z (Fin.natAdd a (finProdFinEquiv (i,j))) := by
    have he : a + bits*i.val + j.val = (Fin.natAdd a (finProdFinEquiv (i,j))).val := by
      change a + bits*i.val + j.val = a + (j.val + bits*i.val)
      omega
    rw [he]
    simp only [paddedBit, dite_eq_left (Fin.natAdd a (finProdFinEquiv (i,j))).isLt]
  have chunk (i : Fin u) : readTag x i = readTag y i ↔ ∀ j : Fin bits,
      x (Fin.natAdd v (finProdFinEquiv (i,j))) = y (Fin.natAdd v' (finProdFinEquiv (i,j))) := by
    rw [Fin.ext_iff]
    change readField x _ _ = readField y _ _ ↔ _
    rw [readField_eq_iff]
    simp_rw [pos]
  constructor
  · intro h j
    obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective j
    exact (chunk i).mp (h i) k
  · intro h i
    exact (chunk i).mpr fun j ↦ h (finProdFinEquiv (i,j))

/-- The native loop starts at the two payload boundaries and compares the
resident bits directly. It takes seven ticks per selector bit and one final
test. Its mask can feed the next port's comparison. -/
theorem compareResidentTags {w p r k u bits v v' : ℕ} {M : Machine w p r k}
    {pc : Fin 7 → Fin p} {reg : Fin 7 ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (x : Fin (v + u * bits) → Bool) (y : Fin (v' + u * bits) → Bool)
    (base base' : Word w) (c : Config w p r) (hc : c.pc = pc 0)
    (hleft : c.reg (reg 0) = base + (v : Word w))
    (hend : c.reg (reg 1) = base + ((v + u * bits : ℕ) : Word w))
    (hright : c.reg (reg 2) = base' + (v' : Word w)) (h1 : c.reg (reg 3) = 1)
    (hn : u * bits < 2 ^ w)
    (hx : ∀ i : Fin (v + u * bits), c.privateMem (base + (i.val : Word w)) = encodeBit w (x i))
    (hy : ∀ i : Fin (v' + u * bits), c.privateMem (base' + (i.val : Word w)) = encodeBit w (y i)) :
    ∃ out, Prefix M c (List.replicate (7 * (u * bits) + 1) .tick) out ∧ out.pc = done ∧
      (out.reg (reg 4) = 0 ↔ c.reg (reg 4) = 0 ∧ ∀ i : Fin u, readTag x i = readTag y i) ∧
      Frame reg c out ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let left (j : Fin (u * bits)) := encodeBit w (x (Fin.natAdd v j))
  let right (j : Fin (u * bits)) := encodeBit w (y (Fin.natAdd v' j))
  obtain ⟨out, pre, hp, _, _, mask, frame, hm, hs⟩ :=
    compareArrays hl left right _ _ c hc hleft (by simpa [add_assoc] using hend) hright h1 hn
      (fun i ↦ by simpa [left, add_assoc] using hx (Fin.natAdd v i))
      (fun i ↦ by simpa [right, add_assoc] using hy (Fin.natAdd v' i))
  refine ⟨out, pre, hp, ?_, frame, hm, hs⟩
  rw [mask, readTag_eq_iff_suffix]
  refine and_congr_right fun _ ↦ ⟨?_, fun h i ↦ congrArg (encodeBit w) (h i)⟩
  intro h i
  have hw : 0 < w := by
    by_contra! hzero
    have hz : w = 0 := Nat.eq_zero_of_le_zero hzero
    have hi := i.isLt
    have hh : u * bits < 1 := by simpa only [hz, pow_zero] using hn
    omega
  apply Bool.eq_iff_iff.mpr
  rw [← encodeBit_eq_one hw, ← encodeBit_eq_one hw, show
    encodeBit w (x (Fin.natAdd v i)) = encodeBit w (y (Fin.natAdd v' i)) from h i]

end PairSimulation.MapConsistency

end VPVNP
end Computability
end OAI
