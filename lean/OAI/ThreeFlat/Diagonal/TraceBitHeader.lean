import OAI.ThreeFlat.BitNetwork.PinMap
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # One open bit per initialized RAM word -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM RAMSerialization

variable {F : Type*} {S w n P Q : ℕ}

/-- Resolve a word pin to its associated public bit or to a fixed zero source. -/
def relabel (wire : Fin P → Option (Fin Q)) : BitSource n P → BitSource n Q
  | .pin j => match wire j with
    | some i => .pin i
    | none => .constant false
  | .hidden h => .hidden h
  | .constant b => .constant b

/-- The low bit of each input word is an open pin. The other word bits are
the fixed zero ports, so initialized advice bits use exactly one pin each. -/
def bitPin (i : Fin (S*w)) : Option (Fin S) :=
  let a : Fin S × Fin w := finProdFinEquiv.symm i
  if a.2.val = 0 then some a.1 else none

def binaryWord (w : ℕ) (b : Bool) : Word w := if b then 1 else 0

theorem bitPin_at (hw : 0 < w) (x : Fin S → Bool) :
    (fun i => ((bitPin i).map x).getD false) =
      arrayBits S w (fun j => binaryWord w (x j)) := by
  funext i
  obtain ⟨⟨a,b⟩,rfl⟩ := finProdFinEquiv.surjective i
  rw [arrayBits_at,← LiveHeader.testBit_wordBits]
  cases e : x a <;> by_cases hb : b.val = 0 <;> apply Bool.eq_iff_iff.mpr <;>
    simp [bitPin,binaryWord,e,hb,hw,Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem eval [CommSemiring F] (hw : 0 < w) (N : BitNetwork F (S*w)) (x : Fin S → Bool) :
    (N.restrictPins bitPin).eval x = N.eval (arrayBits S w (fun j => binaryWord w (x j))) := by
  rw [BitNetwork.restrictPins_eval,bitPin_at hw]

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
