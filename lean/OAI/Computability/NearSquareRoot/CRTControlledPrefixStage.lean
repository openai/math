import OAI.Computability.NearSquareRoot.CRTControlledLift
import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # Applying a flat address pass below a binary prefix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Adic IntegerMultiplication.Packed IntegerMultiplication.Loom
open IntegerMultiplication.Code

def prefixView {p n k : ℕ} (size : p+n=k) :
    Adopt ((line 2 p).cart (line 2 n)) (line 2 k) :=
  (tile 2 p n).thenDo (castN 2 _ _ size)

def underPrefix {p n k : ℕ} (size : p+n=k) (f : Block 2 n → Block 2 n)
    (word : Block 2 k) : Block 2 k :=
  let v := (prefixView size).cast
  let t := v.symm word
  v (t.1,f t.2)

theorem prefixView_least {p n k : ℕ} (size : p+n=k) (a : Block 2 p) (b : Block 2 n) :
    least ((prefixView size).cast (a,b)) = least b ++ least a := by
  subst k
  change (most ((tile 2 p n).cast (a,b))).reverse = _
  rw [tile_most, List.reverse_append]
  rfl

/-- A single flat inner command handles all high-prefix settings simultaneously. -/
theorem binaryPrefixPass {X : Type} {r : Regime X} {width : X → ℕ} {rate : X → ℝ}
    (p n k : X → ℕ) (size : ∀ x, p x + n x = k x)
    (hp : r.Has (tally ∘ p)) (hn : r.Has (tally ∘ n))
    {U : X → Type} (u : (x : X) → Series (U x)) (hu : ∀ x, (u x).count ≤ width x)
    (move : (x:X) → Block 2 (n x) → Block 2 (n x))
    (inner : ∀ fs : (z : (x : X) × Block 2 (p x)) → Block 2 (n z.1) → U z.1 → Bead,
      let ys := fun (z : (x : X) × Block 2 (p x)) => line 2 (n z.1)
      let rr := r.pull (Sigma.fst : ((x : X) × Block 2 (p x)) → X)
      let su := fun z : (x : X) × Block 2 (p x) => u z.1
      Breeze (fun z => rate z.1) rr (fun z => (ys z).count) (fun z => width z.1)
        (together rr.header (cloth ys su fs)) (cloth ys su (fun z a => fs z (move z.1 a))))
    (f : (x : X) → Block 2 (k x) → U x → Bead) :
    let flat x := line 2 (k x)
    Breeze rate r (fun x => (flat x).count) width (together r.header (cloth flat u f))
      (cloth flat u (fun x a => f x (underPrefix (size x) (move x) a))) := by
  let P x := line 2 (p x)
  let T x := line 2 (n x)
  let C x := (P x).cart (T x)
  let flat x := line 2 (k x)
  let v x := prefixView (size x)
  let fs := fun (z : (x : X) × Block 2 (p x)) (a : Block 2 (n z.1)) => f z.1 ((v z.1).cast (z.2,a))
  let input := fun x (a : Block 2 (p x) × Block 2 (n x)) => strip (u x) (fs ⟨x,a.1⟩ a.2)
  let output := fun x (a : Block 2 (p x) × Block 2 (n x)) => strip (u x) (fs ⟨x,a.1⟩ (move x a.2))
  have ps := terminal (p:=2) (by decide) p hp
  have ts := terminal (p:=2) (by decide) n hn
  have live := cloth_size C u (ps.product ts) (fun x a => f x ((v x).cast a)) hu
  have run := prefixPass P T ps ts input output live (inner fs)
  have put (q : (x:X) → Block 2 (k x) → U x → Bead) :
      cloth flat u q = cloth C u (fun x a => q x ((v x).cast a)) := by
    funext x; exact (v x).packet _
  change Breeze rate r (fun x => (flat x).count) width (together r.header (cloth flat u f)) (cloth flat u _)
  rw [← funext (fun x => (v x).cost), put f, put]
  convert run using 1
  apply congrArg (stackRun C)
  funext x a
  change strip (u x) (f x (underPrefix (size x) (move x) ((v x).cast a))) = _
  unfold underPrefix
  change strip (u x) (f x ((v x).cast
    (((v x).cast.symm ((v x).cast a)).1, move x ((v x).cast.symm ((v x).cast a)).2))) = _
  rw [Equiv.symm_apply_apply]

end Controlled

end NearSquareRoot
end Computability
end OAI
