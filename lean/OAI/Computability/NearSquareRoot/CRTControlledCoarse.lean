import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # Exchanging two contiguous chunks of the full binary word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Adic IntegerMultiplication.Packed IntegerMultiplication.Loom
open IntegerMultiplication.Code

noncomputable section

/-- Each argument records an actual contiguous part of one flat address. -/
def flatExchange (p h g s : ℕ) (a : Block 2 (p+h+g+h+s)) : Block 2 (p+h+g+h+s) :=
  let v := flatSpan p h g s
  v.cast (swapper _ _ _ (v.cast.symm a))

theorem flatExchange_apply {p h g s : ℕ}
    (a : SpanKey (field 2 p) (field 2 g) (field 2 s) (Block 2 h)) :
    flatExchange p h g s ((flatSpan p h g s).cast a) =
      (flatSpan p h g s).cast (swapper _ _ _ a) := by
  simp [flatExchange]

theorem flatExchange_least {p h g s : ℕ} (a : Block 2 (p+h+g+h+s)) :
    let parts := (flatSpan p h g s).cast.symm a
    least (flatExchange p h g s a) = least parts.2.2.2.2 ++ least parts.2.1 ++
      least parts.2.2.1 ++ least parts.2.2.2.1 ++ least parts.1 := by
  simp [flatExchange,flatSpan_least,List.append_assoc]

theorem flatExchangeStage {X : Type} {r : Regime X} {l : X → ℕ}
    (p h g s : X → ℕ) (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (sw : RectInterchange r h ρ) (hp : r.Has (tally ∘ p)) (hh : r.Has (tally ∘ h))
    (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s)) (hl : ∀ x, (u x).count ≤ l x)
    (f : (x:X) → Block 2 (p x+h x+g x+h x+s x) → U x → Bead) :
    let flat x := line 2 (p x+h x+g x+h x+s x)
    Breeze (Spindle.modes h (τ := ρ)) r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u (fun x a => f x (flatExchange (p x) (h x) (g x) (s x) a))) := by
  let P x := field 2 (p x)
  let G x := field 2 (g x)
  let S x := field 2 (s x)
  let raw x := stock 2 (P x) (G x) (S x) (h x)
  let flat x := line 2 (p x+h x+g x+h x+s x)
  let view x := flatSpan (p x) (h x) (g x) (s x)
  have allBits (x : X) (j : ℕ) (e : j ∈ P x ++ G x ++ S x) : j ≤ Net.Shuttle.base := by
    simp only [List.mem_append] at e
    rcases e with (ha|ha)|ha
    all_goals exact ((ivory (p := 2) (by decide) j ha).2).trans Net.Shuttle.base_large.le
  have w := sw P G S hh (Told.carrier (q:=2) (by decide) p hp)
    (Told.carrier (q:=2) (by decide) g hg) (Told.carrier (q:=2) (by decide) s hs)
    allBits l u hl (fun x a => f x ((view x).cast a))
  have transfer (k : (x:X) → Block 2 (p x+h x+g x+h x+s x) → U x → Bead) :
      cloth flat u k = cloth raw u (fun x a => k x ((view x).cast a)) := by
    funext x
    exact (view x).packet _
  change Breeze _ r (fun x => (flat x).count) l (together r.header (cloth flat u f))
    (cloth flat u _)
  rw [← funext (fun x => (view x).cost), transfer f, transfer]
  simpa only [view,flatExchange_apply] using w

end
end Controlled

end NearSquareRoot
end Computability
end OAI
