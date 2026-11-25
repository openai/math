import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepPlace
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain

/-! # Effective conjugation of the native sparse switch pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout

open IntegerMultiplication Code Adic Strip Packed Loom Dims Staff Space EffectiveBoundedTask PositionProgram

noncomputable section

/-- Extract both physical relocation tables from typed metadata. The first
projection is the table applied after the mask and the second places the
natural records before the mask. -/
theorem relocationTables {X H : Type} [Codec H] {r : Regime X} {k : X → ℕ}
    (π : (x : X) → Equiv.Perm (Fin (k x))) (metadata : X → H) (supplied : r.Has metadata)
    (tables : H → Reflections.Table × Reflections.Table) (project : Easy tables)
    (emit : ∀ x, tables (metadata x) = (Reflections.table (π x),Reflections.table (π x).symm)) :
    (r.Has fun x => Reflections.table (π x)) ∧ (r.Has fun x => Reflections.table (π x).symm) := by
  have both := supplied.ez project
  constructor
  · simpa only [emit] using both.ez (Easy.fst (X := Reflections.Table) (Y := Reflections.Table))
  · simpa only [emit] using both.ez (Easy.snd (X := Reflections.Table) (Y := Reflections.Table))

private theorem projectTable {P X : Type} [Primcodable P] {Y : P → Type} {r : Regime X}
    {V : X → ℕ} (ripe : r.ripe fun x => (V x : ℝ)) (pick : ∀ p, Y p → X)
    {T S : ∀ p, Y p → ℕ} (time : ∀ p y, V (pick p y) ≤ T p y) (space : ∀ p y, V (pick p y) ≤ S p y)
    {table : X → Reflections.Table} (tab : r.Has table) :
    Family T S (fun p y => r.header (pick p y)) (fun p y => send (table (pick p y))) := by
  have extract : Family (fun p y => V (pick p y)) (fun p y => V (pick p y))
      (fun p y => r.header (pick p y)) (fun p y => send (table (pick p y))) :=
    Family.joint ((boundedOfCarries (tab.cooked ripe)).on (fun z : Sigma Y => pick z.1 z.2))
  exact extract.mono time space

/-- Position the complete record array, run the prepared flat mask, and undo
the placement. The input is the original shared header and native cloth.
The clock and arena can vary by candidate and by runtime input. -/
theorem effectiveNaturalBatchAt {X : Type} {r : Regime X} (A G i B : X → ℕ)
    (π : (x : X) → Equiv.Perm (Fin (maskWidth (A x) (i x) (G x) (B x))))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    {U : X → Type} (u : (x : X) → Series (U x))
    (f : (x : X) → Block 2 (maskWidth (A x) (i x) (G x) (B x)) → U x → Bead)
    (forward : r.Has fun x => Reflections.table (π x)) (backward : r.Has fun x => Reflections.table (π x).symm)
    (ripe : r.ripe fun x => ((2^maskWidth (A x) (i x) (G x) (B x)*(u x).count : ℕ) : ℝ))
    {P : Type} [Primcodable P] {Y : P → Type} (pick : ∀ p, Y p → X) (T S : ∀ p, Y p → ℕ) :
    let k x := maskWidth (A x) (i x) (G x) (B x)
    let V x := 2^(k x)*(u x).count
    let slots x := line 2 (k x)
    let first x (a : Block 2 (k x)) := f x ((permuteNative (π x)).symm a)
    let second x (a : Block 2 (k x)) := first x (flatMask (H := G x-1) (A x) 0 (B x) (ctrl x) a)
    (∀ p y, V (pick p y) ≤ T p y) → (∀ p y, V (pick p y) ≤ S p y) →
    Family T S
        (fun p => together (fun x => send (Reflections.table (π x).symm)) (cloth slots u f) ∘ pick p)
        (fun p => cloth slots u (fun x a => f x (flatBitPullback (π x).symm a)) ∘ pick p) →
    Family T S (fun p => together r.header (cloth slots u first) ∘ pick p) (fun p => cloth slots u second ∘ pick p) →
    Family T S
        (fun p => together (fun x => send (Reflections.table (π x))) (cloth slots u second) ∘ pick p)
        (fun p => cloth slots u (fun x a => second x (flatBitPullback (π x) a)) ∘ pick p) →
    Family T S (fun p => together r.header (cloth slots u f) ∘ pick p)
        (fun p => cloth slots u (fun x a => f x (naturalStage (π x) (ctrl x) a)) ∘ pick p) := by
  intro k V slots first second time space place mask undo
  let head p (y : Y p) := r.header (pick p y)
  let big p (y : Y p) := (head p y).count+T p y
  have grow p (y : Y p) : T p y ≤ big p y := Nat.le_add_left ..
  let start p := cloth slots u f ∘ pick p
  let left p := cloth slots u first ∘ pick p
  let right p := cloth slots u second ∘ pick p
  let finish p := cloth slots u (fun x a => f x (naturalStage (π x) (ctrl x) a)) ∘ pick p
  have pre : Family T S (fun p y => (head p y).fork (start p y)) left := by
    apply Family.projectHeader (projectTable ripe pick time space backward)
    apply place.conform (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    intro p y
    apply congrArg (stripe _)
    funext a
    change strip _ (f _ (flatBitPullback (π _).symm a)) = strip _ (f _ ((permuteNative (π _)).symm a))
    rw [nativeUnplace]
  have post : Family T S (fun p y => (head p y).fork (right p y)) finish := by
    apply Family.projectHeader (projectTable ripe pick time space forward)
    apply undo.conform (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    intro p y
    apply congrArg (stripe _)
    funext a
    change strip _ (second _ (flatBitPullback (π _) a)) = strip _ (second _ (permuteNative (π _) a))
    rw [nativePullback]
  have stage := Family.threeStages (s := S) (header := head) (t := big)
    (fun p y => Nat.le_add_right ..) (pre.mono grow (fun _ _ => le_rfl))
    (mask.mono grow (fun _ _ => le_rfl)) (post.mono grow (fun _ _ => le_rfl))
  obtain ⟨K,hK⟩ := (Regime.self.cooked ripe).small
  obtain ⟨c,R,eff,hR,hc⟩ := stage
  refine ⟨c,R,eff,hR,fun p => ⟨(hc p).1,(hc p).2.bound (K+1) 1 ?_ (fun _ => by simp)⟩⟩
  intro y
  have cap : (head p y).count ≤ K*V (pick p y) := by
    have cap := hK (pick p y)
    change ((head p y).count : ℝ) ≤ (K:ℝ)*(V (pick p y):ℝ) at cap
    exact_mod_cast cap
  have enough := cap.trans (Nat.mul_le_mul_left K (time p y))
  change (head p y).count + T p y + 1 ≤ (K+1)*(T p y+1)
  simp only [Nat.succ_mul,Nat.mul_succ]
  omega

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
