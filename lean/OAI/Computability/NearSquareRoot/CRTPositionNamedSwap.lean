import OAI.Computability.NearSquareRoot.CRTPositionNamedSwapView
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectangle
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectPrep
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectRate

/-! # Named physical rectangle for a native full-width chunk swap -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication Code Strip Strip.Dims Adic Packed Loom Staff
open NamedPacked Effective InterchangeROMBinary

open private measuredChunk from OAI.Computability.NearSquareRoot.CRTPositionChunkSwap

variable {X : Type} {r : Regime X} (q : X → Fin 3 × Fin 3) (k : X → ℕ)

private abbrev front (x : X) := k x % 3 + (swapOf (q x)).front (k x / 3)
private abbrev gap (x : X) := (swapOf (q x)).gap (k x / 3)
private abbrev back (x : X) := (swapOf (q x)).back (k x / 3)

private theorem dimensions (hq : r.Has q) (hk : Realizes r k) :
    Told r (fun x => field 2 (front q k x)) ∧ Told r (fun x => field 2 (gap q k x)) ∧
    Told r (fun x => field 2 (back q k x)) := by
  have n := hk.dividing (Realizes.fix 3)
  have F := measuredChunk hq n .middleRight ChunkSwap.front (by intro s k; cases s <;> rfl)
  have G := measuredChunk hq n .leftRight ChunkSwap.gap (by intro s k; cases s <;> rfl)
  have B := measuredChunk hq n .leftMiddle ChunkSwap.back (by intro s k; cases s <;> rfl)
  exact ⟨Told.carrier (by decide) _ ((hk.rem (Realizes.fix 3)).plus F), Told.carrier (by decide) _ G,
    Told.carrier (by decide) _ B⟩

private theorem guard (x : X) (d : ℕ)
    (h : d ∈ field 2 (front q k x) ++ field 2 (gap q k x) ++ field 2 (back q k x)) :
    d ≤ Net.Shuttle.base := by
  simp only [List.mem_append] at h
  rcases h with (h|h)|h <;> exact ((ivory (p:=2) (by decide) d h).2).trans Net.Shuttle.base_large.le

variable {l : X → ℕ} {U : X → Type} (u : (x : X) → Series (U x))
  (f : (x : X) → Block 2 (k x) → U x → Bead)

private theorem swapInput :
    cloth (fun x => line 2 (k x)) u f =
      cloth (fun x => swapStock (k x) (swapOf (q x))) u
        (fun x a => f x ((swapView (k x) (swapOf (q x))).cast a)) := by
  funext x
  exact (swapView (k x) (swapOf (q x))).packet _

private theorem swapOutput :
    cloth (fun x => line 2 (k x)) u (fun x a => f x (swapNative (k x) (q x) a)) =
      cloth (fun x => swapStock (k x) (swapOf (q x))) u
        (fun x a => f x ((swapView (k x) (swapOf (q x))).cast (swapper _ _ _ a))) := by
  rw [swapInput q k]
  simp_rw [swapView_apply]

/-- Compile the header prelude once for the entire geometry family. The command
is shared by every payload width, payload, rectangle file, and exponent. -/
theorem swapNativeEmitter (hq : r.Has q) (hk : Realizes r k) :
    ∃ pre : Cmd, ∀ (l : X → ℕ) {U : X → Type} (u : (x : X) → Series (U x)),
      (∀ x, (u x).count ≤ l x) → ∀ (f : (x : X) → Block 2 (k x) → U x → Bead)
      (c : Cmd) (ρ : ℝ) (D : ℕ), 0 ≤ ρ → RectPhysical c ρ D →
      let t x := line 2 (k x)
      BreezeAt (pre.join c) (Spindle.modes k (τ := ρ)) r (fun x => (t x).count) l
        (together r.header (cloth t u f)) (cloth t u (fun x a => f x (swapNative (k x) (q x) a))) := by
  obtain ⟨F,G,B⟩ := dimensions q k hq hk
  let n x := k x / 3
  let op x := swapOf (q x)
  obtain ⟨pre,prep⟩ := prepareRect _ _ _ n (hk.dividing (Realizes.fix 3)) F G B
  refine ⟨pre,?_⟩
  intro l U u hu f c ρ D hρ hc t
  let v := fun x a => f x ((swapView (k x) (op x)).cast a)
  have body := native_beads hc hρ _ _ _ n (hk.dividing (Realizes.fix 3)) F G B (guard q k) l u hu v
  have run := (prep l u hu v ρ hρ).next body
  change BreezeAt _ _ _ (fun x => (line 2 (k x)).count) _ _ _
  rw [← funext (fun x => (swapView (k x) (op x)).cost), swapOutput q k u f, swapInput q k u f]
  apply run.raise
  intro x
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.div_le_self (k x) 3)) hρ

/-- Instantiate the coarse transposition in the effective position-program template. -/
theorem swapNativeProgram (hq : r.Has q) (hk : Realizes r k) (hu : ∀ x, (u x).count ≤ l x) :
    let t x := line 2 (k x)
    Program rectContract k r (fun x => (t x).count) l
      (together r.header (cloth t u f)) (cloth t u (fun x a => f x (swapNative (k x) (q x) a))) := by
  obtain ⟨pre,go⟩ := swapNativeEmitter q k hq hk
  refine ⟨.next (.fixed pre) .rectangle,?_⟩
  rintro c ρ hρ ⟨D,rect⟩
  exact go l u hu f c ρ D hρ rect

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
