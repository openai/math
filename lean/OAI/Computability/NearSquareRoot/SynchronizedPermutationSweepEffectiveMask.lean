import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveNative
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepMask

/-! # Running grouped candidate-specific mask commands on native record arrays -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication Code Adic Strip Packed Loom Dims Staff Space EffectiveBoundedTask

noncomputable section

/-- The grouped pass moves the two guarded fields and leaves every suffix
bit and its payload in place. Its record on the restored tape is the original
native addressing formula on the entire array. Candidate-specific arena
allowances are retained through both fixed grouping passes. -/
theorem nativePreparedMaskFamilyAt {X : Type} {r : Regime X} (A H i B m : X → ℕ)
    (hA : Realizes r A) (hB : Realizes r B)
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : Realizes r (extent H (fun _ => 0) i))
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0 + B x) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let n x := A x + h x + h x
    let k x := n x + B x
    let mid x := (line 2 (B x)).cart (u x)
    let leaf x (a : Block 2 (n x)) (z : Block 2 (B x) × U x) := f x ((tile 2 (n x) (B x)).cast (a,z.1)) z.2
    ∃ D : ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (pick : ∀ p, Y p → X)
      (Q factor S : ∀ p, Y p → ℕ),
      (∀ p y, r.scale (pick p y) ≤ Q p y) → (∀ p y, payloadBits D (Q p y) ≤ B (pick p y)) →
      let V p y := 2^(k (pick p y))*m (pick p y)
      let T p y := V p y*(factor p y+1)
      (∀ p y, V p y ≤ S p y) →
      Family T S (fun p => together r.header (cloth (fun x => line 2 (n x)) mid leaf) ∘ pick p)
        (fun p => cloth (fun x => line 2 (n x)) mid (fun x a => leaf x (flatMask (A x) 0 0 (ctrl x) a)) ∘ pick p) →
      Family T S (fun p => together r.header (cloth (fun x => line 2 (k x)) u f) ∘ pick p)
        (fun p => cloth (fun x => line 2 (k x)) u (fun x a => f x (flatMask (A x) 0 (B x) (ctrl x) a)) ∘ pick p) := by
  intro h n k mid leaf
  let g x (a : Block 2 (k x)) := f x (flatMask (A x) 0 (B x) (ctrl x) a)
  have ready : Realizes r n := (hA.plus hc).plus hc
  obtain ⟨D,pack⟩ := ReservePack.aroundFamilyOnAt u n B m f g hm hu ready hB
    (head := r.header) Regime.self 1 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  refine ⟨D,?_⟩
  intro P inst Y pick Q factor S scale room V T space run
  have volume p (y : Y p) : ReservePack.volume n B m (pick p y) = V p y := by
    simp only [V,k,ReservePack.volume,ReservePack.records,ReservePack.packed,pow_add,Nat.mul_assoc]
  have out p (y : Y p) : cloth (fun x => line 2 (n x)) mid
      (fun x a => leaf x (flatMask (A x) 0 0 (ctrl x) a)) (pick p y) = ReservePack.grouped u n B g (pick p y) := by
    apply congrArg (stripe _)
    funext a
    apply congrArg (strip _)
    funext z
    let x := pick p y
    let low := z.1
    change f x ((tile 2 (n x) (B x)).cast (flatMask (H := H x) (A x) 0 0 (ctrl x) a,low)) z.2 =
      f x (flatMask (H := H x) (A x) 0 (B x) (ctrl x) ((tile 2 (n x) (B x)).cast (a,low))) z.2
    have eq := flatMask_suffix (p := A x) (i := i x) (H := H x) (g := 0) (B := B x) (ctrl x) a low
    exact congrArg (fun v => f x v z.2) eq.symm
  have fitted := pack pick Q T S scale room (fun p y => (volume p y).trans_le (space p y))
    (run.conform (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) out)
  obtain ⟨c,R,he,hR,hc⟩ := fitted
  refine ⟨c,R,he,hR,fun p => ⟨(hc p).1,(hc p).2.bound 2 1 ?_ (fun _ => by simp)⟩⟩
  intro y
  have positive : V p y ≤ T p y := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change ReservePack.volume n B m (pick p y)+T p y+1 ≤ 2*(T p y+1)
  rw [volume]
  omega


/-- With a linearly bounded grouped program, restoring the original tape
preserves the exact native-volume space allowance. -/
theorem nativePreparedMaskFamily {X : Type} {r : Regime X} (A H i B m : X → ℕ)
    (hA : Realizes r A) (hB : Realizes r B)
    {U : X → Type} (u : (x : X) → Series (U x))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (hc : Realizes r (extent H (fun _ => 0) i))
    (hm : ∀ x, 0 < m x) (hu : ∀ x, (u x).count ≤ m x)
    (f : (x : X) → Block 2 (A x + cap (i x) (H x) 0 + cap (i x) (H x) 0 + B x) → U x → Bead) :
    let h := extent H (fun _ => 0) i
    let n x := A x + h x + h x
    let k x := n x + B x
    let mid x := (line 2 (B x)).cart (u x)
    let leaf x (a : Block 2 (n x)) (z : Block 2 (B x) × U x) := f x ((tile 2 (n x) (B x)).cast (a,z.1)) z.2
    ∃ D : ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (pick : ∀ p, Y p → X)
      (Q factor : ∀ p, Y p → ℕ),
      (∀ p y, r.scale (pick p y) ≤ Q p y) → (∀ p y, payloadBits D (Q p y) ≤ B (pick p y)) →
      let V p y := 2^(k (pick p y))*m (pick p y)
      let T p y := V p y*(factor p y+1)
      Family T V (fun p => together r.header (cloth (fun x => line 2 (n x)) mid leaf) ∘ pick p)
        (fun p => cloth (fun x => line 2 (n x)) mid (fun x a => leaf x (flatMask (A x) 0 0 (ctrl x) a)) ∘ pick p) →
      Family T V (fun p => together r.header (cloth (fun x => line 2 (k x)) u f) ∘ pick p)
        (fun p => cloth (fun x => line 2 (k x)) u (fun x a => f x (flatMask (A x) 0 (B x) (ctrl x) a)) ∘ pick p) := by
  intro h n k mid leaf
  obtain ⟨D,run⟩ := nativePreparedMaskFamilyAt A H i B m hA hB u ctrl hc hm hu f
  refine ⟨D,?_⟩
  intro P inst Y pick Q factor scale room V T
  exact run pick Q factor V scale room (fun _ _ => le_rfl)

end
end Controlled

end NearSquareRoot
end Computability
end OAI
