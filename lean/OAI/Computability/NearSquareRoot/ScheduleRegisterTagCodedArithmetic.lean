import OAI.Computability.NearSquareRoot.KernelComputableAddressXor
import OAI.Computability.NearSquareRoot.KernelComputableSelector
import OAI.Computability.NearSquareRoot.KernelScaleStream

/-! # Arithmetic on the column and parity registers of a scale pass

A physical column holds one bit per slot. Two consecutive columns select a
base-four address in the mask table. Each bit in the selected mask toggles
the corresponding parity register. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTagCoded

open KernelSelectorAlign (Column get ofFn)
open KernelComputableAddress

private def columnEquiv (a : ℕ) : Column a ≃ Fin (2^(a+1)) :=
  let slots : Column a ≃ (Fin (a+1) → Bool) :=
    ⟨get a, ofFn a, KernelSelectorAlign.ofFn_get a, KernelSelectorAlign.get_ofFn a⟩
  slots.trans ((Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv)

/-- The little-endian binary numeral of the physical column. -/
def columnRank (a : ℕ) (c : Column a) : ℕ := (columnEquiv a c).val

theorem columnRank_lt (a : ℕ) (c : Column a) : columnRank a c < 2^(a+1) :=
  (columnEquiv a c).isLt

def columnUnrank (a : ℕ) (k : Fin (2^(a+1))) : Column a := (columnEquiv a).symm k

@[simp] theorem columnRank_unrank (a : ℕ) (k : Fin (2^(a+1))) :
    columnRank a (columnUnrank a k) = k.val :=
  congrArg Fin.val ((columnEquiv a).apply_symm_apply k)

@[simp] theorem columnUnrank_rank (a : ℕ) (c : Column a) :
    columnUnrank a ⟨columnRank a c, columnRank_lt a c⟩ = c :=
  (columnEquiv a).symm_apply_apply c

theorem digit_columnRank (a : ℕ) (c : Column a) (i : Fin (a+1)) :
    digit 2 (columnRank a c) i.val = (get a c i).toNat := by
  let bits (j : Fin (a+1)) : ZMod 2 := finTwoEquiv.symm (get a c j)
  change digit 2 (packSig (a+1) bits).val i.val = _
  rw [digit_packSig]
  change (finTwoEquiv.symm (get a c i)).val = _
  cases get a c i <;> rfl

/-- Interleave the low and high bits of each slot to form one base-four digit. -/
def pairedRank (a u x : ℕ) : ℕ :=
  assemble 4 (a+1) fun i => digit 2 u i + 2 * digit 2 x i

theorem pairedRank_rank {a : ℕ} (u x : Column a) :
    pairedRank a (columnRank a u) (columnRank a x) =
      (packColumn (a+1) (KernelScaleStream.paired u x)).val := by
  apply assemble_eq (fun i => packSig 2 (KernelScaleStream.paired u x i))
  intro i
  rw [digit_columnRank, digit_columnRank]
  let lo := get a u i
  let hi := get a x i
  change lo.toNat + 2 * hi.toNat = (packSig 2
    (fun j => if j = 0 then (lo.toNat : ZMod 2) else (hi.toNat : ZMod 2))).val
  cases lo <;> cases hi <;> decide

/-- Add a selected mask to the current binary signature coordinatewise modulo two. -/
def updateParity (q maskVal acc : ℕ) : ℕ :=
  assemble 2 q fun j => (digit 2 acc j + digit 2 maskVal j) % 2

theorem updateParity_pack {a q : ℕ} (masks : List ℕ) (u x : Column a)
    (s : Fin q → ZMod 2) :
    updateParity q (masks.getD (pairedRank a (columnRank a u) (columnRank a x)) 0)
        (packSig q s).val =
      (packSig q (s + KernelComputableSelector.test (a+1) q masks (KernelScaleStream.paired u x))).val := by
  rw [pairedRank_rank]
  apply assemble_eq (s + KernelComputableSelector.test (a+1) q masks (KernelScaleStream.paired u x))
  intro j
  rw [digit_packSig, Pi.add_apply]
  change _ = ZMod.val (s j + KernelComputableSelector.test (a+1) q masks (KernelScaleStream.paired u x) j)
  rw [ZMod.val_add]
  simp only [KernelComputableSelector.test, ZMod.val_natCast, digit, Nat.mod_mod]

variable {X : Type*} [Primcodable X]

theorem primrec_pairedRank {a u x : X → ℕ} (ha : Primrec a) (hu : Primrec u) (hx : Primrec x) :
    Primrec fun t => pairedRank (a t) (u t) (x t) :=
  primrec_assemble (Primrec.const 4) (Primrec.succ.comp ha)
    (Primrec.nat_add.comp (primrec_digit (Primrec.const 2) (hu.comp Primrec.fst) Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (primrec_digit (Primrec.const 2) (hx.comp Primrec.fst) Primrec.snd))).to₂

theorem primrec_updateParity {q m acc : X → ℕ} (hq : Primrec q) (hm : Primrec m)
    (ha : Primrec acc) : Primrec fun t => updateParity (q t) (m t) (acc t) :=
  primrec_assemble (Primrec.const 2) hq
    (Primrec.nat_mod.comp (Primrec.nat_add.comp
      (primrec_digit (Primrec.const 2) (ha.comp Primrec.fst) Primrec.snd)
      (primrec_digit (Primrec.const 2) (hm.comp Primrec.fst) Primrec.snd)) (Primrec.const 2)).to₂

end RegisterTagCoded

end NearSquareRoot
end Computability
end OAI
