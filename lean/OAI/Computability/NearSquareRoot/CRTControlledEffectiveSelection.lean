import OAI.Computability.NearSquareRoot.CRTControlledEffectiveFlat
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectangle

/-! # Named sources for masked XOR with the canonical rectangle interface -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic Packed
noncomputable section

/-- Substitute a rectangular binary program into the prepared masked XOR. -/
theorem flatTemplate {X : Type} {r : Regime X} {l : X → ℕ} (H i p g s : X → ℕ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Block 2 (p x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (ctrl : Strip.Trace r (fun x => line 2 (p x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    Program rectContract n r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a)) := by
  let P x := field 2 (p x)
  let G x := field 2 (g x)
  let S x := field 2 (s x)
  have guard (x : X) (j : ℕ) (e : j ∈ P x ++ G x ++ S x) : j ≤ Net.Shuttle.base := by
    simp only [List.mem_append] at e
    rcases e with (a|a)|a
    all_goals exact ((ivory (p := 2) (by decide) j a).2).trans Net.Shuttle.base_large.le
  exact flatControlledTemplate rectContract H i p g s u b hc shape sparse hp hg hs
    (rectangleProgram P G S _ hc (Told.carrier (q := 2) (by decide) p hp)
      (Told.carrier (q := 2) (by decide) g hg) (Told.carrier (q := 2) (by decide) s hs)
      guard l u z) ctrl z f

/-- The selector directory is read from the runtime header for every physical input. -/
theorem flatSelectedTemplate {X : Type} {r : Regime X} {l : X → ℕ} (H i p g s : X → ℕ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (p x)))
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (indices : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (p x)))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    let b x (a : Block 2 (p x)) j := ((src x j).map (prefixBit a)).getD false
    Program rectContract n r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x a => f x (flatMask (p x) (g x) (s x) (b x) a)) := by
  let b x (a : Block 2 (p x)) j := ((src x j).map (prefixBit a)).getD false
  have bits : Strip.Trace r (fun x => line 2 (p x)) (fun _ a => send (List.ofFn (prefixBit a))) := by
    simp only [prefixBit_list]
    exact Curtain.aims (fun _ a => least a) (Curtain.issues p hp)
      _ (Easy.finite title).mapping.poly
  have ctrl : Strip.Trace r (fun x => line 2 (p x)) (fun x a => send (List.ofFn (b x a))) := by
    have F := selectedTrace _ _ bits indices
    simpa only [selectBits_ofFn, b] using F
  exact flatTemplate H i p g s u b hc shape sparse hp hg hs ctrl z f

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
