import OAI.ThreeFlat.Diagonal.CompressorPacking
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Allocating the fixed binary lane coordinates of a shrinking step -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression

/-- Restrict a lane to its two consecutive coordinate ranges. Addition of
the old wire displacement decomposes on those same ranges. -/
def splitWord (a b : ℕ) : BitWord (a+b) ≃+ BitWord a × BitWord b where
  toFun w := (fun i => w (Fin.castAdd b i), fun j => w (Fin.natAdd a j))
  invFun z := Fin.append z.1 z.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv z := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left ..
    · exact Fin.append_right ..
  map_add' _ _ := rfl

def laneSplit (colors slots tags remain : ℕ) :
    BitWord (colors + (slots + (tags + remain))) ≃+
      BitWord colors × BitWord slots × BitWord tags × BitWord remain :=
  (splitWord _ _).trans ((AddEquiv.refl _).prodCongr
    ((splitWord _ _).trans ((AddEquiv.refl _).prodCongr (splitWord _ _))))

variable {V L M : Type*} {d : ℕ} [AddCommGroup L] [AddCommGroup M]

/-- Change the additive lane coordinates of a lifted graph. -/
def changeLanes (G : LiftedSlots V d L) (u : L ≃+ M) : LiftedSlots V d M :=
  ⟨G.base, fun e => u (G.displacement e)⟩

theorem changeLanes_target (G : LiftedSlots V d L) (u : L ≃+ M) (e : V × Fin d) (g : L) :
    (changeLanes G u).actualTarget (e,u g) = (G.base.target e,u (G.actualTarget (e,g)).2) := by
  simp [changeLanes]

/-- Number of greedy tag bits, determined entirely by the old degree. -/
def tagBits (d : ℕ) := Nat.clog 2 (2*d*((d+1)+(d+1)^2) + 1)

theorem tagBits_fit (d : ℕ) : 2*d*((d+1)+(d+1)^2) < Fintype.card (BitWord (tagBits d)) := by
  rw [Fintype.card_fun,Fintype.card_fin,ZMod.card]
  exact Nat.le_pow_clog (by decide : 1 < 2) _

/-- Binary tags are their own additive inverses, as required when the
thin C endpoint lies at the destination of an old wire. -/
theorem binary_neg {n : ℕ} (w : BitWord n) : -w = w := by
  funext i
  exact (by decide : ∀ x : Fin 2, -x = x) (w i)

/-- Construct the paper's actual packing data from an unpartitioned old
binary lane and an arbitrary power-of-two degree. -/
noncomputable def binaryPacking [Fintype V] (s remain : ℕ)
    (G : LiftedSlots V (2^s) (BitWord ((2*(2^s)+1) + (s + (tagBits (2^s) + remain))))) :
    PackingData V (BitWord s) (BitWord (tagBits (2^s))) (BitWord remain) (2^s) (2*(2^s)+1) :=
  packingData (changeLanes G (laneSplit _ _ _ _)) (bitWordFinEquiv s) (tagBits_fit _)

end ThreeFlat.Diagonal.CompressorPacking

end OAI
