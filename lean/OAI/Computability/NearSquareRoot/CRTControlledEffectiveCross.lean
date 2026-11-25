import OAI.Computability.NearSquareRoot.CRTControlledEffectiveSelection
import OAI.Computability.NearSquareRoot.CRTControlledCross

/-! # The occupied residue of a cross-chunk XOR as a command template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective

open IntegerMultiplication Code Adic Strip Strip.Dims Loom Packed Staff
noncomputable section

/-- Charge a full-word P192 pass using the widths, residual shift, and original
(unshifted) finite-source table from the header. -/
theorem trimmedSelectedTemplate {X : Type} {R : Regime X} {l : X → ℕ} (H i p N g s r : X → ℕ)
    {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (p x)))
    (fit : ∀ x, r x + cap (i x) (H x) 0 ≤ N x)
    (hc : R.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : R.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : R.Has (tally ∘ p)) (hN : R.Has (tally ∘ N)) (hg : R.Has (tally ∘ g))
    (hs : R.Has (tally ∘ s)) (hr : R.Has (tally ∘ r))
    (indices : R.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (p x)))
    (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (p x + N x + g x + N x + s x) → U x → Bead) :
    let flat x := line 2 (p x + N x + g x + N x + s x)
    Program rectContract (extent H (fun _ => 0) i) R (fun x => (flat x).count) l
      (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (trimmedMask (p x) (N x) (g x) (s x) (r x) (fit x) (src x) a)) := by
  let h := extent H (fun _ => 0) i
  let top x := trimTop (N x) (r x) (h x)
  let P x := p x+top x
  let G x := r x+g x+top x
  let S x := r x+s x
  let raw x := line 2 (P x+h x+G x+h x+S x)
  let full x := line 2 (p x+N x+g x+N x+s x)
  let c x := trimCast (p x) (N x) (g x) (s x) (r x) (h x) (fit x)
  have ht : R.Has (tally ∘ top) := ((show Realizes R N from hN).minused hr).minused hc
  have w := flatSelectedTemplate H i P G S u (fun x j => (src x j).map (trimPort (top x)))
    hc shape sparse ((show Realizes R p from hp).plus ht) (((show Realizes R r from hr).plus hg).plus ht)
    ((show Realizes R r from hr).plus hs)
    (shiftedSelectorHeader src ht indices) z (fun x a => f x ((c x).cast a))
  have transfer (v : (x : X) → Block 2 (p x+N x+g x+N x+s x) → U x → Bead) :
      cloth full u v = cloth raw u (fun x a => v x ((c x).cast a)) := by
    funext x
    exact (c x).packet _
  change Program rectContract _ R (fun x => (full x).count) l (together R.header (cloth full u f))
    (cloth full u fun x a => f x (trimmedMask (p x) (N x) (g x) (s x) (r x) (fit x) (src x) a))
  rw [← funext (fun x => (c x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth raw u)
  funext x a
  change f x ((c x).cast (flatMask (P x) (G x) (S x) (trimSource (top x) (src x))
    ((c x).cast.symm ((c x).cast a)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Option.map_map, Function.comp_def]
  rfl

/-- All dimensions and selector indices for an occupied pass are manufactured from
the three rulers and the table of the original position gate. -/
theorem crossFitTemplate {X : Type} {R : Regime X} {l : X → ℕ}
    (N G r : X → ℕ) (read : (x : X) → Fin (N x) → Option (Fin (N x)))
    (hg : ∀ x, 0 < G x) (fit : ∀ x, r x+G x ≤ N x)
    (hn : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x)))
    (sparse : ∀ x, (3 * crossExtent (N x) (G x) (r x) + 1) * (32 * slots (N x) (G x) (r x)) ≤
        2 ^ width (G x-1) 0)
    {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x)
    (f : (x : X) → Block 2 (crossWidth (N x)) → U x → Bead) :
    let flat x := line 2 (crossWidth (N x))
    Program rectContract (fun x => crossExtent (N x) (G x) (r x))
      R (fun x => (flat x).count) l (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)) := by
  let H := fun x => G x-1
  let i := fun x => slots (N x) (G x) (r x)
  have hh : Realizes R H := hG.minused (Realizes.fix 1)
  have si : Realizes R i := ((hn.minused hr).dividing hG).minused (Realizes.fix 1)
  have c : Realizes R (extent H (fun _ => 0) i) :=
    (si.plus (Realizes.fix 1)).times ((hh.plus (Realizes.fix 1)).plus (Realizes.fix 0))
  have sh : R.Has (fun x => signs (H x) 0 (i x)) :=
    Regime.Has.pair hh (Regime.Has.pair (Realizes.fix 0) si)
  have run := trimmedSelectedTemplate H i N N (fun _ => 0) (fun _ => 0) r u
    (fun x => crossRead (read x) (G x) (r x)) (fun x => crossFit (hg x) (fit x)) c sh sparse
    hn hn (Realizes.fix 0) (Realizes.fix 0) hr (crossReadHeader N G r read hg hn hG hr tab) z f
  simpa only [crossResidueMask,dite_eq_left (fit _),extent,crossExtent,H,i,crossWidth,Nat.add_zero] using run

end
end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
