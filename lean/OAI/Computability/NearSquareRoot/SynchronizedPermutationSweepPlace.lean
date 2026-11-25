import OAI.Computability.NearSquareRoot.CRTPositionLargePerm
import OAI.Computability.NearSquareRoot.PermutationLayoutConjugate

/-! # Execute a bit-position placement or its inverse from the shared physical header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Loom
open IntegerMultiplication.Strip PositionProgram NearSquareRoot.Space

noncomputable section

theorem nativePullback {k : ℕ} (π : Equiv.Perm (Fin k)) :
    permuteNative π = flatBitPullback π :=
  eq_flatBitPullback _ _ (fun a j => congrFun (permuteNative_bits π a) j)

theorem nativeUnplace {k : ℕ} (π : Equiv.Perm (Fin k)) :
    (permuteNative π).symm = flatBitPullback π.symm :=
  eq_flatBitPullback _ _ (fun a j => congrFun (permuteNative_symm_bits π a) j)

/-- Polynomial-size header work fits the complete physical array even when
the header's own scale is a polynomial of the address width. -/
theorem ripeOfPolyScale {X : Type} (r : Regime X) (k V : X → ℕ)
    (small : Dom k r.scale) (area : ∀ x, 2^k x ≤ V x) :
    r.ripe (fun x => (V x : ℝ)) := by
  refine ⟨fun x => ?_,fun n => ?_⟩
  · change (1 : ℝ) ≤ (V x : ℝ)
    exact_mod_cast (show 1 ≤ V x from (Nat.one_le_pow _ _ (by decide)).trans (area x))
  · obtain ⟨d,c,h⟩ := (small.add (Dom.const k 1)).pow n
    obtain ⟨C,hC⟩ := polynomial_le_multiple_array_length d
    refine ⟨c*C,fun x => ?_⟩
    change (((r.scale x+1)^n : ℕ) : ℝ) ≤ ((c*C : ℕ) : ℝ)*(V x : ℝ)
    exact_mod_cast (show (r.scale x+1)^n ≤ (c*C)*V x from (h x).trans
      ((Nat.mul_le_mul_left c ((hC (k x)).trans (Nat.mul_le_mul_left C (area x)))).trans
        (Nat.mul_assoc ..).ge))

/-- The short table is projected while the complete array is parked.
The small-width dispatcher covers all widths below the compiled routing cutoff. -/
theorem positionFromHeader {X : Type} {U : X → Type} {r : Regime X}
    (k : X → ℕ) (u : (x : X) → Series (U x))
    (π : (x : X) → Equiv.Perm (Fin (k x))) (f : (x : X) → Block 2 (k x) → U x → Bead)
    (pos : ∀ x, 0 < (u x).count) (ρ : ℝ) (hρ : 1/2 < ρ)
    (tab : r.Has fun x => Reflections.table (π x))
    (ripe : r.ripe (fun x => ((2^k x*(u x).count : ℕ) : ℝ))) :
    let V x := 2^k x*(u x).count
    let T x := V x*(positionFactor ρ (k x)+1)
    BoundedTask T V (together r.header (cloth (fun x => line 2 (k x)) u f))
      (cloth (fun x => line 2 (k x)) u (fun x z => f x (flatBitPullback (π x) z))) := by
  let V x := 2^k x*(u x).count
  let T x := V x*(positionFactor ρ (k x)+1)
  let data := cloth (fun x => line 2 (k x)) u f
  obtain ⟨K,above⟩ := PositionRows.largeTableCloth hρ
  have move := ReserveSmall.dispatchPositionCloth K ρ k (fun x => (u x).count) u π f pos
    (fun _ => le_rfl) (above (fun x : {x // K < k x} => k x) (fun x => u x.val)
      (fun x => pos x.val) (fun x => π x.val) (fun x => f x.val) (fun x => x.property.le))
  have setup : BoundedTask V V r.header (fun x => send (Reflections.table (π x))) :=
    boundedOfCarries (tab.cooked ripe)
  have seq := (setup.left data).compose move
  apply seq.bound 2 6 <;> intro x
  · have h : V x ≤ T x := Nat.le_mul_of_pos_right _ (by omega)
    change V x+T x+1 ≤ 2*(T x+1)
    omega
  · have h := ReserveSmall.beadClothCap k (fun x => (u x).count) u f pos (fun _ => le_rfl) x
    change (data x).count ≤ 5*V x at h
    change max (V x+(data x).count) (V x)+1 ≤ 6*(V x+1)
    omega

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
