import OAI.Computability.NearSquareRoot.CRTControlledEffectiveXor

/-! # Named masked-XOR programs on flat binary stripes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic Packed

noncomputable section

/-- The priced masked XOR on a pair of physical binary blocks. -/
theorem maskedBlockTemplate {X : Type} {r : Regime X} {l : X → ℕ} (rect : Cmd → ℝ → Prop) (H i : X → ℕ)
    (P G S : X → Tape) {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Pin (P x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : Told r P) (hg : Told r G) (hs : Told r S)
    (sw : RectangleProgram (r := r) (l := l) rect P G S u (extent H (fun _ => 0) i))
    (ready : Strip.Trace r (fun x => layout (P x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → SpanKey (P x) (G x) (S x) (Block 2 (cap (i x) (H x) 0)) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let s := fun x => stock 2 (P x) (G x) (S x) (n x)
    Program rect n r (fun x => (s x).count) l
      (together r.header (cloth s u f)) (cloth s u fun x a =>
        f x (a.1, maskBlock (b x a.1) a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2)) := by
  let n := extent H (fun _ => 0) i
  let raw := fun x => stock 2 (P x) (G x) (S x) (n x)
  let rows := rotationLayout H (fun _ => 0) i P G S
  let block (x : X) := package (H x) 0 (i x)
  let v (x : X) : Adopt (rows x) (raw x) := (Adopt.same _).split <|
    (block x).split ((Adopt.same _).split ((block x).split (Adopt.same _)))
  have transfer (g : (x : X) → SpanKey (P x) (G x) (S x) (Block 2 (n x)) → U x → Bead) :
      cloth raw u g = cloth rows u (fun x a => g x ((v x).cast a)) := by
    funext x
    exact (v x).packet _
  have w := maskedXorTemplate rect H (fun _ => 0) i P G S u hp hg hs shape hc z sw b sparse ready
    (fun x a => f x ((v x).cast a))
  have hb (x : X) (a : RotationAddress H (fun _ => 0) i P G S x) :
      maskBlock (b x a.1) ((block x).cast a.2.1) =
        (block x).cast (maskTarget (b x a.1) a.2.1) := by simp [maskBlock, block]
  change Program rect _ r (fun x => (raw x).count) l (together _ (cloth raw u f))
    (cloth raw u fun x a => f x (a.1, maskBlock (b x a.1) a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2))
  rw [← funext (fun x => (v x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth rows u)
  funext x a
  change f x (a.1, maskBlock (b x a.1) ((block x).cast a.2.1), a.2.2.1,
    (block x).cast a.2.2.2.1, a.2.2.2.2) = _
  rw [hb x a]
  rfl


/-- One fixed program template for a flat-address mask pass, with an arbitrary named rectangle. -/
theorem flatControlledTemplate {X : Type} {r : Regime X} {l : X → ℕ} (rect : Cmd → ℝ → Prop) (H i p g s : X → ℕ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Block 2 (p x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (sw : RectangleProgram (r := r) (l := l) rect (fun x => field 2 (p x)) (fun x => field 2 (g x))
      (fun x => field 2 (s x)) u (extent H (fun _ => 0) i))
    (ctrl : Strip.Trace r (fun x => line 2 (p x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    Program rect n r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a)) := by
  let n := extent H (fun _ => 0) i
  let P x := field 2 (p x)
  let G x := field 2 (g x)
  let S x := field 2 (s x)
  let raw x := stock 2 (P x) (G x) (S x) (n x)
  let flat x := line 2 (p x + n x + g x + n x + s x)
  let view x := flatSpan (p x) (n x) (g x) (s x)
  have w := maskedBlockTemplate rect H i P G S u b hc shape sparse
    (Told.carrier (q := 2) (by decide) p hp) (Told.carrier (q := 2) (by decide) g hg)
    (Told.carrier (q := 2) (by decide) s hs) sw ctrl z
    (fun x a => f x ((view x).cast a))
  have transfer (k : (x : X) → Block 2 (p x + n x + g x + n x + s x) → U x → Bead) :
      cloth flat u k = cloth raw u (fun x a => k x ((view x).cast a)) := by
    funext x
    exact (view x).packet _
  dsimp only
  change Program rect _ r (fun x => (flat x).count) l (together r.header (cloth flat u f))
    (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a))
  rw [← funext (fun x => (view x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth raw u)
  funext x a
  unfold flatMask
  change f x ((view x).cast (((view x).cast.symm ((view x).cast a)).1,
    maskBlock (b x (((view x).cast.symm ((view x).cast a)).1)) (((view x).cast.symm ((view x).cast a)).2.1),
    ((view x).cast.symm ((view x).cast a)).2.2)) = _
  rw [Equiv.symm_apply_apply]

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
