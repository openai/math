import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepMask
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepPlace
import OAI.Computability.NearSquareRoot.InterchangeRectangular

/-! # A complete bounded prepared batch on the natural, ungrouped array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Packed IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Staff NearSquareRoot.Space PositionProgram

noncomputable section
set_option maxHeartbeats 400000

/-- Place the natural array, apply the computed sparse batch, and undo the
placement. The same original header provides both position tables and all
prefix controls. The runtime includes each full-array position permutation. -/
theorem naturalBatch {X : Type} {r : Regime X} (A G i B : X → ℕ) (ρ : ℝ) (hρ : 1/2 < ρ)
    (hA : Realizes r A) (hB : Realizes r B)
    (hc : Realizes r (extent (fun x => G x-1) (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (G x-1) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (G x-1) 0+1)*(32*i x) ≤ 2^width (G x-1) 0)
    (π : (x : X) → Equiv.Perm (Fin (maskWidth (A x) (i x) (G x) (B x))))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (mask : (fixedRowRegime r A hA).Has fun z => List.ofFn (ctrl z.1 z.2))
    (forward : r.Has fun x => Reflections.table (π x))
    (backward : r.Has fun x => Reflections.table (π x).symm)
    {U : X → Type} (u : (x : X) → Series (U x)) (positive : ∀ x, 0 < (u x).count)
    (f : (x : X) → Block 2 (maskWidth (A x) (i x) (G x) (B x)) → U x → Bead)
    (ripe : r.ripe (fun x => ((2^maskWidth (A x) (i x) (G x) (B x)*(u x).count : ℕ) : ℝ))) :
    let h := extent (fun x => G x-1) (fun _ => 0) i
    let k x := maskWidth (A x) (i x) (G x) (B x)
    let V x := 2^(k x)*(u x).count
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, payloadBits D (Q y) ≤ B (pick y)) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) →
      (∀ y, factor y ≤ 2^(A (pick y))) →
      BoundedTask (fun y => V (pick y)*(positionFactor ρ (k (pick y))+factor y+1)) (V ∘ pick)
        (together r.header (cloth (fun x => line 2 (k x)) u f) ∘ pick)
        (cloth (fun x => line 2 (k x)) u (fun x a => f x (naturalStage (π x) (ctrl x) a)) ∘ pick) := by
  let h := extent (fun x => G x-1) (fun _ => 0) i
  let k x := maskWidth (A x) (i x) (G x) (B x)
  let V x := 2^(k x)*(u x).count
  let T x := V x*(positionFactor ρ (k x)+1)
  let s x := line 2 (k x)
  let first x (a : Block 2 (k x)) := f x ((permuteNative (π x)).symm a)
  let second x (a : Block 2 (k x)) := first x (flatMask (H := G x-1) (A x) 0 (B x) (ctrl x) a)
  let result x (a : Block 2 (k x)) := f x (naturalStage (π x) (ctrl x) a)
  have live (v : (x : X) → Block 2 (k x) → U x → Bead) : Volume (fun x => (V x : ℝ)) (cloth s u v) := by
    refine ⟨5, fun x => ?_⟩
    change ((cloth s u v x).count : ℝ) ≤ 5*(V x : ℝ)
    exact_mod_cast (show (cloth s u v x).count ≤ 5*V x from ReserveSmall.beadClothCap k (fun x => (u x).count) u v positive (fun _ => le_rfl) x)
  have fits (x : X) : V x ≤ T x := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have pre : BoundedTask T V (together r.header (cloth s u f)) (cloth s u first) := by
    apply (positionFromHeader k u (fun x => (π x).symm) f positive ρ hρ backward ripe).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro x
    apply congrArg (stripe _)
    funext a
    change strip _ (f x (flatBitPullback (π x).symm a)) = strip _ (f x ((permuteNative (π x)).symm a))
    rw [nativeUnplace]
  have post : BoundedTask T V (together r.header (cloth s u second)) (cloth s u result) := by
    apply (positionFromHeader k u π second positive ρ hρ forward ripe).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro x
    apply congrArg (stripe _)
    funext a
    change strip _ (second x (flatBitPullback (π x) a)) = strip _ (second x (permuteNative (π x) a))
    rw [nativePullback]
  have header := Regime.self.cooked ripe
  have p₁ := ReserveStage.retainBoundedHeader pre header (live f) fits
  obtain ⟨D,core⟩ := nativePreparedMask A (fun x => G x-1) i B (fun x => (u x).count) hA hB ρ u ctrl hc
    shape sparse (nearRoot_rectInterchange hρ _ _) mask positive (fun _ => le_rfl) (by linarith) first
  refine ⟨D,fun pick Q factor scale low rate high => ?_⟩
  have middle := core pick Q factor scale low rate high
  obtain ⟨c,hc⟩ := live first
  have headroom : Volume (fun y => (V (pick y) : ℝ)) (cloth s u first ∘ pick) :=
    ⟨c,fun y => hc (pick y)⟩
  have p₂ := ReserveStage.retainBoundedHeader middle (header.slide pick) headroom
    (fun y => Nat.le_mul_of_pos_right _ (Nat.succ_pos (factor y)))
  have execute := ((p₁.on pick).compose p₂).compose (post.on pick)
  apply execute.bound 3 1 <;> intro y
  · let pos := positionFactor ρ (k (pick y))
    change V (pick y)*(pos+1)+V (pick y)*(factor y+1)+V (pick y)*(pos+1)+1 ≤
      3*(V (pick y)*(pos+factor y+1)+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  · change max (max (V (pick y)) (V (pick y))) (V (pick y))+1 ≤ 1*(V (pick y)+1)
    simp

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
