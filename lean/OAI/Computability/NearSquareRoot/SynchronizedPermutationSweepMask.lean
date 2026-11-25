import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepNative
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Bounded prepared switches on the original ungrouped physical array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Packed IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Staff NearSquareRoot.Space

noncomputable section
set_option maxHeartbeats 400000

/-- The low reserve consists of actual address bits in the input and output.
The full physical pass packs them into each row's payload, applies the switches
determined by its high prefix, and restores all original record boundaries. -/
theorem nativePreparedMask {X : Type} {r : Regime X} (A H i B m : X → ℕ)
    (hA : Realizes r A) (hB : Realizes r B) (ρ : ℝ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : Realizes r (extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (sw : RectInterchange (fixedRowRegime r A hA) ((extent H (fun _ => 0) i) ∘ Sigma.fst) ρ)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0 + B x) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let n x := A x + h x + h x
    let k x := n x + B x
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, payloadBits D (Q y) ≤ B (pick y)) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) →
      (∀ y, factor y ≤ 2^(A (pick y))) →
      let V y := 2^(k (pick y))*m (pick y)
      BoundedTask (fun y => V y*(factor y+1)) V
        (together r.header (cloth (fun x => line 2 (k x)) u f) ∘ pick)
        (cloth (fun x => line 2 (k x)) u (fun x a => f x (flatMask (A x) 0 (B x) (ctrl x) a)) ∘ pick) := by
  let h := extent H (fun _ => 0) i
  let n x := A x + h x + h x
  let k x := n x+B x
  let mid x := (line 2 (B x)).cart (u x)
  let leaf x (a : Block 2 (n x)) (v : Block 2 (B x) × U x) :=
    f x ((tile 2 (n x) (B x)).cast (a,v.1)) v.2
  let g x (a : Block 2 (k x)) := f x (flatMask (A x) 0 (B x) (ctrl x) a)
  have ready : Realizes r n := (hA.plus hc).plus hc
  have len (x : X) : (mid x).count ≤ 2^(B x)*m x := by
    simp only [mid,Series.count_cart,lineSize]
    exact Nat.mul_le_mul_left _ (hu x)
  obtain ⟨s,pack⟩ := ReservePack.aroundBoundedOn u n B m f g hm hu ready hB
    (head := r.header) Regime.self 1 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  obtain ⟨d,core⟩ := boundedReservedMaskRowsOn A H i hA ρ mid ctrl hc shape sparse sw mask len hρ leaf
  refine ⟨max d s,fun pick Q factor scale low rate high => ?_⟩
  let V y := 2^k (pick y)*m (pick y)
  let T y := V y*(factor y+1)
  have room (a) (ha : a ≤ max d s) (y) : payloadBits a (Q y) ≤ B (pick y) :=
    (Nat.mul_le_mul_right _ ha).trans (low y)
  have volume (y) : ReservePack.volume n B m (pick y) = V y := by
    simp only [V,k,ReservePack.volume,ReservePack.records,ReservePack.packed,pow_add,Nat.mul_assoc]
  have run := core pick (B ∘ pick) (m ∘ pick) Q factor scale (fun y => hm (pick y)) (fun _ => rfl)
    (room d (le_max_left ..)) rate high
  have out (y) : cloth (fun x => line 2 (n x)) mid
      (fun x a => leaf x (flatMask (A x) 0 0 (ctrl x) a)) (pick y) = ReservePack.grouped u n B g (pick y) := by
    apply congrArg (stripe _)
    funext a
    apply congrArg (strip _)
    funext z
    let x := pick y
    let low := z.1
    change f x ((tile 2 (n x) (B x)).cast (flatMask (H := H x) (A x) 0 0 (ctrl x) a,low)) z.2 =
      f x (flatMask (H := H x) (A x) 0 (B x) (ctrl x) ((tile 2 (n x) (B x)).cast (a,low))) z.2
    have eq := flatMask_suffix (p := A x) (i := i x) (H := H x) (g := 0) (B := B x) (ctrl x) a low
    exact congrArg (fun v => f x v z.2) eq.symm
  have packed := pack pick Q T scale (room s (le_max_right ..)) (run.conform (fun _ => rfl)
    (fun y => (volume y).symm) (fun _ => rfl) out)
  apply (packed.conform (fun y => congrArg (·+T y) (volume y)) volume (fun _ => rfl)
    (fun _ => rfl)).bound 2 1
  · intro y
    have h : V y ≤ T y := Nat.le_mul_of_pos_right _ (by omega)
    change V y+T y+1 ≤ 2*(T y+1)
    omega
  · intro y
    change V y+1 ≤ 1*(V y+1)
    omega

end
end Controlled

end NearSquareRoot
end Computability
end OAI
