import OAI.Computability.NearSquareRoot.CRTControlledCoarse

/-! # Choosing source, target and auxiliary among three equal chunks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Adic IntegerMultiplication.Packed IntegerMultiplication.Loom
open IntegerMultiplication.Code

inductive ChunkSwap where
  | leftMiddle | leftRight | middleRight
deriving DecidableEq, Inhabited

namespace ChunkSwap

def front : ChunkSwap → ℕ → ℕ
  | .middleRight, n => n
  | _, _ => 0

def gap : ChunkSwap → ℕ → ℕ
  | .leftRight, n => n
  | _, _ => 0

def back : ChunkSwap → ℕ → ℕ
  | .leftMiddle, n => n
  | _, _ => 0

def apply {A : Type} : ChunkSwap → A × A × A → A × A × A
  | .leftMiddle, (a,b,c) => (b,a,c)
  | .leftRight, (a,b,c) => (c,b,a)
  | .middleRight, (a,b,c) => (a,c,b)

theorem apply_twice {A : Type} (s : ChunkSwap) (a : A × A × A) :
    s.apply (s.apply a) = a := by cases s <;> rfl

abbrev triple (n : ℕ) := (line 2 n).cart ((line 2 n).cart (line 2 n))

def view (s : ChunkSwap) (n : ℕ) :
    Adopt (stock 2 (field 2 (s.front n)) (field 2 (s.gap n)) (field 2 (s.back n)) n) (triple n) :=
  match s with
  | .leftMiddle => (Adopt.omitL _).thenDo ((Adopt.same _).split (Adopt.omitL _))
  | .leftRight => (Adopt.omitL _).thenDo ((Adopt.same _).split ((Adopt.same _).split (Adopt.skip _)))
  | .middleRight => (Adopt.same _).split ((Adopt.same _).split ((Adopt.omitL _).thenDo (Adopt.skip _)))

theorem view_apply (s : ChunkSwap) (n : ℕ)
    (a : SpanKey (field 2 (s.front n)) (field 2 (s.gap n)) (field 2 (s.back n)) (Block 2 n)) :
    (s.view n).cast (swapper _ _ _ a) = s.apply ((s.view n).cast a) := by
  cases s <;> rfl

/-- A single charged command across all input-selected transpositions. Its rectangular
interchange descriptors say where the one unchanged chunk lies. -/
theorem physical {X : Type} {r : Regime X} {l : X → ℕ} (s : X → ChunkSwap)
    (n : X → ℕ) (ρ : ℝ) {U : X → Type} (u : (x:X) → Series (U x))
    (sw : RectInterchange r n ρ) (hn : r.Has (tally ∘ n))
    (hp : r.Has fun x => tally ((s x).front (n x)))
    (hg : r.Has fun x => tally ((s x).gap (n x)))
    (hb : r.Has fun x => tally ((s x).back (n x)))
    (hl : ∀ x, (u x).count ≤ l x)
    (f : (x:X) → (Block 2 (n x) × Block 2 (n x) × Block 2 (n x)) → U x → Bead) :
    let t x := triple (n x)
    Breeze (Spindle.modes n (τ:=ρ)) r (fun x => (t x).count) l
      (together r.header (cloth t u f)) (cloth t u (fun x a => f x ((s x).apply a))) := by
  let P x := field 2 ((s x).front (n x))
  let G x := field 2 ((s x).gap (n x))
  let B x := field 2 ((s x).back (n x))
  let raw x := stock 2 (P x) (G x) (B x) (n x)
  let t x := triple (n x)
  let v x := (s x).view (n x)
  have bounds (x : X) (j : ℕ) (e : j ∈ P x ++ G x ++ B x) : j ≤ Net.Shuttle.base := by
    simp only [List.mem_append] at e
    rcases e with (h|h)|h
    all_goals exact ((ivory (p:=2) (by decide) j h).2).trans Net.Shuttle.base_large.le
  have w := sw P G B hn (Told.carrier (q:=2) (by decide) _ hp)
    (Told.carrier (q:=2) (by decide) _ hg) (Told.carrier (q:=2) (by decide) _ hb)
    bounds l u hl (fun x a => f x ((v x).cast a))
  have transfer (k : (x:X) → (Block 2 (n x) × Block 2 (n x) × Block 2 (n x)) → U x → Bead) :
      cloth t u k = cloth raw u (fun x a => k x ((v x).cast a)) := by
    funext x
    exact (v x).packet _
  change Breeze _ r (fun x => (t x).count) l (together r.header (cloth t u f))
    (cloth t u _)
  rw [← funext (fun x => (v x).cost), transfer f, transfer]
  simpa only [v,raw,P,G,B,view_apply] using w

end ChunkSwap
end Controlled

end NearSquareRoot
end Computability
end OAI
