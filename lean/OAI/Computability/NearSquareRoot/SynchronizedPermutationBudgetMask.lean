import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetRate
import OAI.Computability.NearSquareRoot.PermutationLayoutMask

/-! # The complete control word in one fixed physical row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open IntegerMultiplication IntegerMultiplication.Packed Controlled

/-- All unused positions form part of the high prefix. A single fixed-row
header can therefore compute its full table mask before entering the guarded fields. -/
theorem BoxPasses.mask_layout {k D : ℕ} (budget : BoxPasses k D 2) (hk : 1 ≤ k)
    (a : ℕ) (selected : Finset (Fin ((CoprimeBox.box k).length / 4)))
    (sub : selected ⊆ members k a) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (record : ℕ) :
    let c := ∑ i ∈ selected, (BoxFin.physicalWidth (box := CoprimeBox.box k) i - 1)
    let b := selected.card
    let chunk := (b+1)*guardWidth k
    let low := payloadBits D k
    let high := k-(2*chunk+low)
    payloadBits 2 k + c ≤ high ∧ PermutationLayout.maskWidth high b (guardWidth k) low = k ∧
      PhysicalWalsh.XorReserve.volume high (chunk+chunk) low record = 2^k*record ∧
      2*((chunk:ℝ)+1)^ρ ≤ rowFactor k ρ ∧ rowFactor k ρ ≤ 2^high ∧
      (3*cap b (guardWidth k-1) 0+1)*(32*b) ≤ 2^(Packed.width (guardWidth k-1) 0) := by
  have fit := selected_fits _ budget.width_bound budget.fits budget.reserves a selected sub
  dsimp only at fit ⊢
  have pos : 0 < guardWidth k := by unfold guardWidth; omega
  rw [PermutationLayout.maskWidth_eq _ _ _ _ pos, PhysicalWalsh.XorReserve.volume]
  let h := (selected.card+1)*guardWidth k
  change payloadBits 2 k + _ ≤ k-(2*h+payloadBits D k) ∧ k-(2*h+payloadBits D k)+2*h+payloadBits D k=k ∧
    2^(k-(2*h+payloadBits D k)+(h+h)+payloadBits D k)*record=2^k*record ∧ _
  have hfit : payloadBits 2 k + _ + h+h+payloadBits D k ≤ k := fit
  have hh : h ≤ k := by omega
  refine ⟨by omega, by omega, by congr 2; omega, row_rate hh h₀, ?_, sparse_of_fits hh⟩
  exact (row_factor_high hk h₁).trans (Nat.pow_le_pow_right (by decide) (by omega))

end SynchronizedPermutationBudget

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Packed IntegerMultiplication.Strip IntegerMultiplication.Loom
open NearSquareRoot.Space

private theorem tile_empty {A : ℕ} (a : Block 2 A) (v : Block 2 0) :
    (tile 2 A 0).cast (a,v) = a := by
  apply Adic.distinct
  rw [tile_most]
  have hv : (most v).length = 0 := by simp
  simp [List.length_eq_zero_iff.mp hv]

/-- Execute a whole table-computed control vector in each fixed high row. Only
the table evaluation needs to be polynomial in the regime scale. The two
guarded blocks use the physical rectangular interchange and its radix repair. -/
theorem boundedReservedMaskRowsOn {X : Type} {r : Regime X} {l : X → ℕ}
    (A H i : X → ℕ) (hA : r.Has (tally ∘ A)) (ρ : ℝ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (sw : RectInterchange (fixedRowRegime r A hA) ((extent H (fun _ => 0) i) ∘ Sigma.fst) ρ)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let K x := A x + h x + h x
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, 0 < m y) →
      (∀ y, l (pick y) = 2^(B y)*m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) →
      (∀ y, factor y ≤ 2^(A (pick y))) →
      let V y := 2^(K (pick y) + B y)*m y
      BoundedTask (fun y => V y*(factor y+1)) V
        (together r.header (cloth (fun x => line 2 (K x)) u f) ∘ pick)
        (cloth (fun x => line 2 (K x)) u (fun x a => f x (flatMask (A x) 0 0 (ctrl x) a)) ∘ pick) := by
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
  have row := flatControlledStage (r := rr) (l := l ∘ Sigma.fst) (H ∘ Sigma.fst) (i ∘ Sigma.fst)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) ρ (fun w => u w.1) (fun w _ => ctrl w.1 w.2)
    (fixedRowGlobal A hA hc) (fixedRowGlobal A hA shape) (fun w => sparse w.1)
    hzero hzero hzero sw ready (fun w => z w.1) hρ (fun w b => f w.1 (v w b))
  have act (w : W) (b : Block 2 (n w.1)) :
      v w (flatMask 0 0 0 (fun _ => ctrl w.1 w.2) b) =
        flatMask (A w.1) 0 0 (ctrl w.1) (v w b) := by
    simpa only [v,join,h,extent,tile_empty,Nat.add_zero] using prefixRowJoin_mask (A := A w.1) (p := 0)
      (g := 0) (s := 0) (H := H w.1) (ctrl w.1) w.2 b
  let leaf (x : X) (a : Block 2 (K x)) := strip (u x) (f x a)
  let perm x := flatMask (H := H x) (A x) 0 0 (ctrl x)
  have hn : r.Has (tally ∘ n) := by
    have add := (hc.pair hc).ez (Easy.append (X := Unit))
    convert add using 1
    funext x
    simp only [Function.comp_apply,n,h,tally,Nat.zero_add,Nat.add_zero,List.replicate_add]
  have row' : Breeze (Spindle.modes (h ∘ Sigma.fst) (τ := ρ)) rr
      (fun w => (line 2 (n w.1)).count) (l ∘ Sigma.fst)
      (fun w => Tree.fork (rr.header w) (stripe (line 2 (n w.1)) fun b => leaf w.1 (v w b)))
      (fun w => stripe (line 2 (n w.1)) fun b => leaf w.1 (perm w.1 (v w b))) := by
    convert row using 1 <;> try rfl
    funext w
    apply congrArg (stripe _)
    funext b
    exact congrArg (leaf w.1) (act w b).symm
  obtain ⟨D,go⟩ := PhysicalWalsh.XorReserve.packedWindowRowsOn A n K hA hn join leaf
    (fun x a => leaf x (perm x a)) row'
  refine ⟨D,fun pick B m Q factor scale pos packed low rate high => ?_⟩
  have bound y (a : Block 2 (K (pick y))) : (leaf (pick y) a).count ≤ 2*(2^(B y)*m y)+1 := by
    have := bulk (u (pick y)) (f (pick y) a)
    have fit := z (pick y)
    rw [packed y] at fit
    change (strip _ _).count ≤ _
    omega
  have out := go pick B m Q factor (fun _ _ => by simp only [lineSize]; exact le_rfl)
    (fun y _ => packed y) bound (fun y a => bound y (perm _ a)) scale pos low
    (fun y _ => rate y) high
  simpa only [PhysicalWalsh.XorReserve.volume, n, K,Nat.zero_add,Nat.add_zero,Nat.add_assoc] using out

end Controlled

end NearSquareRoot
end Computability
end OAI
