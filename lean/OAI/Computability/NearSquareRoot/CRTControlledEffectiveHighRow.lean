import OAI.Computability.NearSquareRoot.CRTControlledEffectiveSelection
import OAI.Computability.NearSquareRoot.CRTControlledRowControls

/-! # The named prepared switch mask below a fixed high prefix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective
open IntegerMultiplication Code Strip Strip.Dims Loom Adic Packed
noncomputable section

private theorem tileEmpty {A : ℕ} (a : Block 2 A) (v : Block 2 0) :
    (tile 2 A 0).cast (a,v) = a := by
  apply Adic.distinct
  rw [tile_most]
  have hv : (most v).length = 0 := by simp
  simp [List.length_eq_zero_iff.mp hv]

/-- Execute the entire header-supplied vector before rejoining the original high prefix. -/
theorem fixedHighMaskTemplate {X : Type} {r : Regime X} {l : X → ℕ}
    (A H i : X → ℕ) (hA : r.Has (tally ∘ A))
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let n x := 0 + h x + 0 + h x + 0
    let K x := A x + h x + h x
    let join x := prefixRowJoin (A x) 0 (h x) 0 0
    let rr := fixedRowRegime r A hA
    let leaf (x : X) (a : Block 2 (K x)) := strip (u x) (f x a)
    let perm x := flatMask (H := H x) (A x) 0 0 (ctrl x)
    Program rectContract (h ∘ Sigma.fst) rr (fun w => (line 2 (n w.1)).count) (l ∘ Sigma.fst)
      (fun w => Tree.fork (rr.header w) (stripe (line 2 (n w.1)) fun b => leaf w.1 ((join w.1).cast (w.2,b))))
      (fun w => stripe (line 2 (n w.1)) fun b => leaf w.1 (perm w.1 ((join w.1).cast (w.2,b)))) := by
  let h := extent H (fun _ => 0) i
  let n x := 0 + h x + 0 + h x + 0
  let K x := A x + h x + h x
  let join x := prefixRowJoin (A x) 0 (h x) 0 0
  let rr := fixedRowRegime r A hA
  let W := Sigma (fun x => Block 2 (A x))
  let v (w : W) (lo : Block 2 (n w.1)) := (join w.1).cast (w.2,lo)
  have hzero : rr.Has (tally ∘ fun _ => 0) := Regime.fixed (tally 0)
  have trace := fixedPrefixTrace (r := rr) (fun _ => 0) hzero
  have ready : Strip.Trace rr (fun _ => line 2 0) (fun w _ => send (List.ofFn (ctrl w.1 w.2))) :=
    trace.tune (onboard_small _ trace.meter _ mask)
  have row := flatTemplate (r := rr) (l := l ∘ Sigma.fst) (H ∘ Sigma.fst) (i ∘ Sigma.fst)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun w => u w.1) (fun w _ => ctrl w.1 w.2)
    (fixedRowGlobal A hA hc) (fixedRowGlobal A hA shape) (fun w => sparse w.1)
    hzero hzero hzero ready (fun w => z w.1) (fun w b => f w.1 (v w b))
  have act (w : W) (b : Block 2 (n w.1)) :
      v w (flatMask 0 0 0 (fun _ => ctrl w.1 w.2) b) =
        flatMask (A w.1) 0 0 (ctrl w.1) (v w b) := by
    simpa only [v,join,h,extent,tileEmpty,Nat.add_zero] using prefixRowJoin_mask (A := A w.1) (p := 0)
      (g := 0) (s := 0) (H := H w.1) (ctrl w.1) w.2 b
  dsimp only
  convert row using 1 <;> try rfl
  funext w
  apply congrArg (stripe _)
  funext b
  exact congrArg (fun a => strip (u w.1) (f w.1 a)) (act w b).symm

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
