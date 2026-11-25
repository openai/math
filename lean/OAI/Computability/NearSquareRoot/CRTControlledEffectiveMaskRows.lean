import OAI.Computability.NearSquareRoot.CRTControlledMaskRowCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowsTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # Uniformly generated controlled masks on whole fixed-prefix rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Adic Strip Loom Packed NamedPacked Filter CommonRegisters
open PhysicalWalsh.XorWindow MaskRowCommand

/-- Use the same physical framing commands whether or not the low reserve
covers the row program's polynomial setup degree. -/
noncomputable def maskRowFrame {X : Type} (r : Regime X) (P n : X → ℕ)
    (hp : r.Has (tally ∘ P)) (hn : r.Has (tally ∘ n)) {U : X → Type} (u : (x : X) → Series (U x))
    (f g : (x : X) → Input (P x) (n x) (U x)) : Frame where
  apply := windowRowsCmd r P n hp hn u f g
  effective := windowRowsCmd_effective r P n hp hn u f g
  within R := by
    obtain ⟨S,hS,hw⟩ := ((eventually_gt_atTop R).and (windowRowsCmd_within r P n hp hn u f g)).exists
    exact ⟨S,by omega,fun c hc => hw c (RegisterSelect.within_mono hS.le _ hc)⟩

/-- The physical template for a complete controlled mask is fixed before the
rectangle implementation and its exponent are supplied. The row scanner pays
for the actual prefix control vector, with the remaining reserve in the low field. -/
theorem boundedReservedMaskRowsOnTotal {X : Type} {r : Regime X} {l : X → ℕ}
    (A H i : X → ℕ) (hA : r.Has (tally ∘ A)) {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let K x := A x + h x + h x
    ∃ t : Template, ∀ c ρ, 0 ≤ ρ → rectContract c ρ →
    (∃ T S : X → ℕ, EffectiveBoundedTask.Runs (t.eval c) T S
      (together r.header (cloth (fun x => line 2 (K x)) u f))
      (cloth (fun x => line 2 (K x)) u (fun x a => f x (flatMask (A x) 0 0 (ctrl x) a)))) ∧
    ∃ D : ℕ, ∀ {Y : Type}
      (pick : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, 0 < m y) →
      (∀ y, l (pick y) = 2^(B y)*m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) → (∀ y, factor y ≤ 2^(A (pick y))) →
      let V y := 2^(K (pick y)+B y)*m y
      EffectiveBoundedTask.Runs (t.eval c) (fun y => V y*(factor y+1)) V
        (together r.header (cloth (fun x => line 2 (K x)) u f) ∘ pick)
        (cloth (fun x => line 2 (K x)) u (fun x a => f x (flatMask (A x) 0 0 (ctrl x) a)) ∘ pick) := by
  intro h K
  let n (x : X) := 0 + h x + 0 + h x + 0
  let view x := prefixRowJoin (A x) 0 (h x) 0 0
  let perm x := flatMask (H := H x) (A x) 0 0 (ctrl x)
  let src x := rowInput (view x) (f x)
  let dst x := rowInput (view x) (f x ∘ perm x)
  have hn : r.Has (tally ∘ n) := by
    have add := (hc.pair hc).ez (Easy.append (X := Unit))
    convert add using 1
    funext x
    simp only [Function.comp_apply,n,h,tally,Nat.zero_add,Nat.add_zero,List.replicate_add]
  let frame := maskRowFrame r A n hA hn u src dst
  obtain ⟨t,run⟩ := fixedHighMaskTemplate A H i hA u ctrl hc shape sparse mask z f
  refine ⟨.frame frame t,fun c ρ hρ rect => ?_⟩
  have step : LocalRowsAt r A n hA u src dst l (Spindle.modes h (τ := ρ)) (t.eval c) := by
    have q := run c ρ hρ rect
    change BreezeAt _ _ _ _ _ _ _ at q
    simpa only [LocalRowsAt,src,dst,rowInput_lookup,Function.comp_def,Spindle.modes,h,n,view,perm] using q
  constructor
  · obtain ⟨T,S,all⟩ := windowRowsOnNamedTotal r A n hA hn u src dst (LocalRowsAt.total r A n hA u src step)
    refine ⟨T,S,?_⟩
    change EffectiveBoundedTask.Runs (windowRowsCmd r A n hA hn u src dst (t.eval c)) _ _ _ _
    apply PhysicalWalsh.AgendaOps.conform all (fun _ => rfl) (fun _ => rfl)
    · intro x
      exact congrArg (Tree.fork _) (store_input (u x) (view x) (f x))
    · intro x
      exact store_input (u x) (view x) (f x ∘ perm x)
  · obtain ⟨D,go⟩ := windowRowsOnNamed r A n hA hn u src dst z step
    refine ⟨D,fun {Y} pick B m Q factor scale pos packed low rate high => ?_⟩
    have out := go pick B m Q factor (fun y => (packed y).le) scale pos low rate high
    change EffectiveBoundedTask.Runs (windowRowsCmd r A n hA hn u src dst (t.eval c)) _ _ _ _
    apply PhysicalWalsh.AgendaOps.conform out
    · intro y; simp only [PhysicalWalsh.XorReserve.volume,n,K,Nat.zero_add,Nat.add_zero,Nat.add_assoc]
    · intro y; simp only [PhysicalWalsh.XorReserve.volume,n,K,Nat.zero_add,Nat.add_zero,Nat.add_assoc]
    · intro y
      change Tree.fork _ (store _ (rowInput _ _)) = Tree.fork _ _
      exact congrArg (Tree.fork _) (store_input (u (pick y)) (view (pick y)) (f (pick y)))
    · intro y
      exact store_input (u (pick y)) (view (pick y)) (f (pick y) ∘ perm (pick y))

/-- The physical template for a complete controlled mask is fixed before the
rectangle implementation and its exponent are supplied. The row scanner pays
for the actual prefix control vector, with the remaining reserve in the low field. -/
theorem boundedReservedMaskRowsOn {X : Type} {r : Regime X} {l : X → ℕ}
    (A H i : X → ℕ) (hA : r.Has (tally ∘ A)) {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let K x := A x + h x + h x
    ∃ t : Template, ∀ c ρ, 0 ≤ ρ → rectContract c ρ → ∃ D : ℕ, ∀ {Y : Type}
      (pick : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, 0 < m y) →
      (∀ y, l (pick y) = 2^(B y)*m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) → (∀ y, factor y ≤ 2^(A (pick y))) →
      let V y := 2^(K (pick y)+B y)*m y
      EffectiveBoundedTask.Runs (t.eval c) (fun y => V y*(factor y+1)) V
        (together r.header (cloth (fun x => line 2 (K x)) u f) ∘ pick)
        (cloth (fun x => line 2 (K x)) u (fun x a => f x (flatMask (A x) 0 0 (ctrl x) a)) ∘ pick) := by
  obtain ⟨t,run⟩ := boundedReservedMaskRowsOnTotal A H i hA u ctrl hc shape sparse mask z f
  exact ⟨t,fun c ρ hr rect => (run c ρ hr rect).2⟩

end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
