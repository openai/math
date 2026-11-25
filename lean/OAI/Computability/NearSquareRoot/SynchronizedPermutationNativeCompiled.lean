import OAI.Computability.NearSquareRoot.SynchronizedPermutationNativeEnvelope
import OAI.Computability.NearSquareRoot.SynchronizedPermutationNativeFrame
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveMaskRows
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepMask

/-! # One generated native switch program with total and fast executions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective
open IntegerMultiplication Code Adic Strip Packed Loom Dims Staff Space
open PhysicalWalsh.AgendaOps

noncomputable section

private theorem rules_le {X : Type} {U : X → Type} (u : (x : X) → Series (U x)) (n B m : X → ℕ)
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x) (x : X) :
    (ReservePack.restoreRulers u n B x).count ≤ 7 * ReservePack.volume n B m x := by
  have hp : 0 < ReservePack.volume n B m x :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (hm x))
  have array : 2^(n x) * 2^(B x) ≤ ReservePack.volume n B m x := by
    unfold ReservePack.volume ReservePack.records ReservePack.packed
    rw [← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (hm x)
  have bits : (u x).count ≤ ReservePack.volume n B m x :=
    (hu x).trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))
  change size (tally ((line 2 (n x)).cart (line 2 (B x))).count) +
    size (tally (u x).count) + 1 ≤ 7*ReservePack.volume n B m x
  simp only [size_tally,tally_length,Series.count_cart,lineSize]
  omega

/-- Compute the sparse switch on the original, ungrouped array. Every admissible
rectangle command gives a terminating execution at every literal reserve parameter.
When the prescribed storage pays the polynomial setup, the identical emitted instructions
have the advertised fast clock and linear peak. -/
theorem nativePreparedMaskTemplate {X : Type} {r : Regime X} (A H i B m : X → ℕ)
    (hA : Realizes r A) (hB : Realizes r B)
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : Realizes r (extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (H x) 0+1)*(32*i x) ≤ 2^width (H x) 0)
    (mask : (fixedRowRegime r A hA).Has fun w => List.ofFn (ctrl w.1 w.2))
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0 + B x) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let k x := A x+h x+h x+B x
    let src := together r.header (cloth (fun x => line 2 (k x)) u f)
    let dst := cloth (fun x => line 2 (k x)) u (fun x a => f x (flatMask (A x) 0 (B x) (ctrl x) a))
    ∃ t : Template, ∀ c ρ, 0 ≤ ρ → rectContract c ρ →
      (∃ T S : X → ℕ, EffectiveBoundedTask.Runs (t.eval c) T S src dst) ∧
      ∃ d : ℕ, ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
        (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, payloadBits d (Q y) ≤ B (pick y)) →
        (∀ y, 2*Spindle.modes h (τ:=ρ) (pick y) ≤ factor y) → (∀ y, factor y ≤ 2^(A (pick y))) →
        let V y := 2^k (pick y)*m (pick y)
        EffectiveBoundedTask.Runs (t.eval c) (fun y => V y*(factor y+1)) V (src ∘ pick) (dst ∘ pick) := by
  intro h k src dst
  let n x := A x+h x+h x
  let mid x := (line 2 (B x)).cart (u x)
  let leaf x (a : Block 2 (n x)) (z : Block 2 (B x) × U x) := f x ((tile 2 (n x) (B x)).cast (a,z.1)) z.2
  let g x a := f x (flatMask (A x) 0 (B x) (ctrl x) a)
  have ready := (hA.plus hc).plus hc
  obtain ⟨dp,pre,post,start,finish,fast⟩ := ReservePack.nativeEnvelope u n B m f g hm hu ready hB
    (head:=r.header) Regime.self 1 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  let l x := 2^B x*m x
  have z (x : X) : (mid x).count ≤ l x := by
    simp only [mid,Series.count_cart,lineSize,l]
    exact Nat.mul_le_mul_left _ (hu x)
  obtain ⟨body,law⟩ := boundedReservedMaskRowsOnTotal A H i hA mid ctrl hc shape sparse mask z leaf
  have out (x : X) : cloth (fun x => line 2 (n x)) mid
      (fun x a => leaf x (flatMask (A x) 0 0 (ctrl x) a)) x = ReservePack.grouped u n B g x := by
    apply congrArg (stripe _)
    funext a
    apply congrArg (strip _)
    funext s
    exact congrArg (fun a => f x a s.2) (flatMask_suffix (p:=A x) (i:=i x) (H:=H x) (g:=0) (B:=B x) (ctrl x) a s.1).symm
  refine ⟨NativeFrame.wrap pre post body,fun c ρ hρ rect => ?_⟩
  obtain ⟨⟨T,S,hr⟩,db,sharp⟩ := law c ρ hρ rect
  have raw := conform hr (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) out
  refine ⟨NativeFrame.arbitrary body start raw finish,max dp db,?_⟩
  intro Y pick Q factor scale room rate high
  have pfit (y) : payloadBits dp (Q y) ≤ B (pick y) := (Nat.mul_le_mul_right _ (le_max_left ..)).trans (room y)
  have bfit (y) : payloadBits db (Q y) ≤ B (pick y) := (Nat.mul_le_mul_right _ (le_max_right ..)).trans (room y)
  have ins := sharp pick (B ∘ pick) (m ∘ pick) Q factor scale (fun y => hm (pick y)) (fun _ => rfl) bfit rate high
  let V y := 2^(k (pick y))*m (pick y)
  have vol (y : Y) : ReservePack.volume n B m (pick y) = V y := by
    simp only [ReservePack.volume,ReservePack.records,ReservePack.packed,V,k,n,pow_add,Nat.mul_assoc]
  have core := conform ins (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun y => out (pick y))
  have wrap := NativeFrame.fitted body (conform (fast pick Q scale pfit) vol vol (fun _ => rfl) (fun _ => rfl))
    core (conform (finish.on pick) vol vol (fun _ => rfl) (fun _ => rfl))
    (fun y => (rules_le u n B m hm hu (pick y)).trans (Nat.mul_le_mul_left 7 (vol y).le)) (fun _ => le_rfl)
  apply wrap.bound 2 1
  · intro y
    have hv : V y ≤ V y*(factor y+1) := Nat.le_mul_of_pos_right _ (by omega)
    change V y+V y*(factor y+1)+1 ≤ 2*(V y*(factor y+1)+1)
    omega
  · intro y
    change V y+1 ≤ 1*(V y+1)
    simp

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
