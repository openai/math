import OAI.Computability.NearSquareRoot.BoundedProduct

/-! # Compiling stream operations in the scope of a recursive Walsh call

The local scan constant can depend on the fixed instruction template. Each
execution of the recursive command is charged its supplied time exactly once.
The child arena has coefficient one even when several children are executed.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space

/-- The two charges at a recursive node. `permit` is the interpretation of the
open return environment at the current width; `t` and `s` bound one child. -/
structure Meter (U : Type*) where
  scan : U → ℕ
  arena : U → ℕ
  arena_le : ∀ u, arena u ≤ scan u
  permit : Env → U → ℕ → ℕ → Prop

variable {U X Y : Type*} {m : Meter U} {n n' : ℕ} {u : X → U} {q r v : X → Tree}

/-- Time and resident-space bounds for a specified closed command. -/
def ClosedRuns (c : Cmd) (time space : X → ℕ) (q r : X → Tree) : Prop :=
  ∃ C : ℕ, ∀ x env p b, DeckCap b p →
    BoundedFits env c (pile 0 (q x) p) (pile 0 (r x) p)
      (C*(time x+1)) (b+C*(space x+1)) (C*(space x+1))

namespace ClosedRuns

variable {c : Cmd} {time space : X → ℕ}

theorem on (h : ClosedRuns c time space q r) (v : Y → X) :
    ClosedRuns c (time ∘ v) (space ∘ v) (q ∘ v) (r ∘ v) := by
  obtain ⟨C,h⟩ := h
  exact ⟨C,fun y => h (v y)⟩

theorem mono {time' space' : X → ℕ} (h : ClosedRuns c time space q r)
    (ht : ∀ x, time x ≤ time' x) (hs : ∀ x, space x ≤ space' x) : ClosedRuns c time' space' q r := by
  obtain ⟨C,h⟩ := h
  refine ⟨C,fun x env p b hb => ?_⟩
  have t := Nat.mul_le_mul_left C (Nat.succ_le_succ (ht x))
  have s := Nat.mul_le_mul_left C (Nat.succ_le_succ (hs x))
  exact (h x env p b hb).mono t (Nat.add_le_add_left s b) s

end ClosedRuns

/-- One fixed instruction segment with an explicit count of recursive invocations. -/
def Runs (cmd : Cmd) (m : Meter U) (n : ℕ) (u : X → U) (q r : X → Tree) : Prop :=
  ∃ C : ℕ, ∀ x env t s, m.permit env (u x) t s → ∀ parked base,
    DeckCap base parked → BoundedFits env cmd (pile 0 (q x) parked) (pile 0 (r x) parked)
      (C * (m.scan (u x) + 1) + n * t) (base + (C * (m.arena (u x) + 1) + s))
      (C * (m.arena (u x) + 1) + s)

/-- Existence of an open command at the specified time and storage bounds. -/
def OpenRun (m : Meter U) (n : ℕ) (u : X → U) (q r : X → Tree) : Prop := ∃ cmd, Runs cmd m n u q r

namespace Runs

theorem closed {c : Cmd} (h : ClosedRuns c (m.scan ∘ u) (m.arena ∘ u) q r) : Runs c m 0 u q r := by
  obtain ⟨C,h⟩ := h
  refine ⟨C,fun x env t s _ p b hp => ?_⟩
  exact (h x env p b hp).mono (by simp) (by dsimp only [Function.comp_apply]; omega)
    (by dsimp only [Function.comp_apply]; omega)

end Runs

namespace OpenRun

theorem on (h : OpenRun m n u q r) (f : Y → X) :
    OpenRun m n (u ∘ f) (q ∘ f) (r ∘ f) := by
  obtain ⟨c,C,h⟩ := h
  exact ⟨c,C,fun y => h (f y)⟩

theorem closed (h : BoundedTask (m.scan ∘ u) (m.arena ∘ u) q r) : OpenRun m 0 u q r := by
  obtain ⟨c,h⟩ := h
  exact ⟨c,Runs.closed h⟩

/-- Closed linear-time shuffling whose entire input fits the resident array. -/
theorem easy {A B : Type*} [Codec A] [Codec B] (f : A → B) (hf : Easy f) (a : X → A)
    (C : ℕ) (hs : ∀ x, size (a x) ≤ C * (m.arena (u x) + 1)) :
    OpenRun m 0 u (fun x => send (a x)) (fun x => send (f (a x))) := by
  apply closed
  apply (BoundedTask.of_time (hf.on a)).bound (2*C+1) (2*C+1)
  · intro x
    have H := (hs x).trans <| Nat.mul_le_mul_left C (Nat.succ_le_succ (m.arena_le _))
    change size (a x) ≤ C*(m.scan (u x)+1) at H
    change size (a x) + 1 ≤ (2*C+1)*(m.scan (u x) + 1)
    rw [Nat.succ_mul, Nat.two_mul, Nat.add_mul]; omega
  · intro x
    change size (a x) + size (a x) + 1 ≤ (2*C+1)*(m.arena (u x) + 1)
    rw [Nat.succ_mul, Nat.two_mul, Nat.add_mul]; have := hs x; omega

end OpenRun

namespace Runs

theorem seq {c d : Cmd} (h : Runs c m n u q r) (g : Runs d m n' u r v) :
    Runs (c.join d) m (n+n') u q v := by
  obtain ⟨C,h⟩ := h
  obtain ⟨D,g⟩ := g
  refine ⟨C+D+2,fun x env t s ok p b hp => ?_⟩
  have h₁ := h x env t s ok p b hp
  have h₂ := g x env t s ok p b hp
  let peak := (C+D+2)*(m.arena (u x)+1)+s
  have ec : C*(m.arena (u x)+1)+s+1 ≤ peak := by dsimp only [peak]; simp only [Nat.add_mul]; omega
  have ed : D*(m.arena (u x)+1)+s ≤ peak := by dsimp only [peak]; simp only [Nat.add_mul]; omega
  exact ((h₁.mono le_rfl (Nat.add_le_add_left (by omega : _ ≤ peak) b) le_rfl).join
    (h₂.mono le_rfl (Nat.add_le_add_left ed b) ed) ec).mono
    (by simp only [Nat.add_mul]; omega) le_rfl le_rfl

/-- The left input field is at the stack head. A sibling bank remains parked
beneath it throughout a child invocation, costing only its resident volume. -/
theorem left {c : Cmd} (h : Runs c m n u q r) (spect : X → Tree) (D : ℕ)
    (hs : ∀ x, (spect x).count ≤ D*(m.arena (u x)+1)) :
    Runs (splitRoot 0 (fun _ => .pass) (c.join (pack 0))) m n u
      (fun x => .fork (q x) (spect x)) (fun x => .fork (r x) (spect x)) := by
  obtain ⟨C,h⟩ := h
  refine ⟨C+D+8, fun x env t s ok p b hp => ?_⟩
  let cap := b + ((C+D+8)*(m.arena (u x)+1)+s)
  let dep := (C+D+8)*(m.arena (u x)+1)+s
  have sub := h x env t s ok (pile 0 (spect x) p) _ (hp.pile 0 _)
  have room : b+(spect x).count+(C*(m.arena (u x)+1)+s)+1 ≤ cap := by
    dsimp [cap]; simp only [Nat.add_mul]; have := hs x; omega
  have ret : C*(m.arena (u x)+1)+s+1 ≤ dep := by dsimp [dep]; simp only [Nat.add_mul]; omega
  have first := sub.mono le_rfl (by omega : _ ≤ cap) le_rfl
  obtain ⟨_,_,run⟩ := sub
  have fin := (show DeckCap _ (pile 0 (r x) (pile 0 (spect x) p)) from run.finish).coverFork.mono room
  have ini := (show DeckCap _ (pile 0 (q x) (pile 0 (spect x) p)) from run.start).coverFork.mono room
  have full := BoundedFits.pair (c := fun _ => .pass)
    (first.join (BoundedFits.pack _ _ _ _ env (depth := dep) fin) ret) ini (by omega)
  exact full.mono (by simp only [Nat.add_mul]; omega) le_rfl le_rfl

end Runs

namespace OpenRun

theorem seq (h : OpenRun m n u q r) (g : OpenRun m n' u r v) : OpenRun m (n+n') u q v := by
  obtain ⟨c,h⟩ := h
  obtain ⟨d,g⟩ := g
  exact ⟨c.join d,h.seq g⟩

theorem left (h : OpenRun m n u q r) (spect : X → Tree) (D : ℕ)
    (hs : ∀ x, (spect x).count ≤ D*(m.arena (u x)+1)) :
    OpenRun m n u (fun x => .fork (q x) (spect x)) (fun x => .fork (r x) (spect x)) := by
  obtain ⟨c,h⟩ := h
  exact ⟨_,h.left spect D hs⟩

end OpenRun
end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
