import OAI.ThreeFlat.Diagonal.HistogramTileNetwork
import OAI.ThreeFlat.Diagonal.MotifSelectorChecks
import OAI.ThreeFlat.Routing.StableCompactNative
import OAI.ThreeFlat.Routing.StableCompactionPadRows

namespace OAI
/-! # Dyadic physical compactor templates for tile and histogram checks -/

namespace ThreeFlat.Diagonal.MotifNativeCompactors

noncomputable section

open Routing Routing.StableCompaction MotifOrderedCells

variable {F : Type*} [CommRing F]

def partialInput (F : Type*) [Zero F] [One F] (n m : ℕ) : BitNetwork F (n+(n+n)) :=
  restrictRows (StableCompactNative.network F m) n

theorem partialInput_eval (n m : ℕ) (room : n ≤ 2^m) (M X Y : Fin n → Bool) :
    (partialInput F n m).eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0 :=
  restrictRows_eval room _ (StableCompactNative.network_eval m) M X Y

theorem partialInput_bits (n m : ℕ) : (partialInput F n m).internal ≤ 2^m*(32000*(m+1)^3) :=
  StableCompactNative.network_internal F m

theorem partialInput_rows (n m : ℕ) : (partialInput F n m).cells ≤ 2^m*(32000*(m+1)^3) :=
  StableCompactNative.network_cells F m

/-- Complete private/record charge for the payload part of one local atom.
The arity-dependent LUT cost is constant across widths and stage choices. -/
theorem tile_size {H : Type*} {e d b : ℕ} (K : Tile F H e d b) (r m : ℕ) :
    let C := partialInput F (r*d) m
    (K.network C).cells + (K.network C).internal ≤
      r*(2^(b+(e*d+e*d))*((b+(e*d+e*d))+2)) + 2*(e*(r*d)) +
      2*(e*(2^m*(32000*(m+1)^3))) := by
  intro C
  rw [Tile.network,network_rows,network_bits]
  have hr := Nat.mul_le_mul_left e (partialInput_rows (F:=F) (r*d) m)
  have hb := Nat.mul_le_mul_left e (partialInput_bits (F:=F) (r*d) m)
  change e*C.cells ≤ _ at hr
  change e*C.internal ≤ _ at hb
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two]
  omega

end

end ThreeFlat.Diagonal.MotifNativeCompactors

end OAI
