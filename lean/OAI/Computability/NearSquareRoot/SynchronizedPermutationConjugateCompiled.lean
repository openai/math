import OAI.Computability.NearSquareRoot.SynchronizedPermutationConjugateCommand
import OAI.Computability.NearSquareRoot.SynchronizedPermutationNativeCompiled
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepPlace
import OAI.Computability.NearSquareRoot.CRTPositionRouterTotal

/-! # A single arithmetic batch command with both total and fast executions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout

open IntegerMultiplication Code Adic Strip Packed Loom Dims Staff Space EffectiveBoundedTask PositionProgram
open Controlled.Effective (Template)
open PhysicalWalsh.AgendaOps (conform)

noncomputable section

/-- The two placement calls and the flat-mask template share the supplied rectangular
interchanger. The very same command works for every pair of reserve guesses. For
sufficient guesses and an adequate suffix and prefix it runs at the stated position
and switch rates using space linear in the true array volume. -/
theorem compiledNaturalBatch {X : Type} {r : Regime X} (A G i B : X → ℕ)
    (hA : Realizes r A) (hB : Realizes r B)
    (hc : Realizes r (extent (fun x => G x-1) (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (G x-1) 0 (i x))
    (sparse : ∀ x, (3*cap (i x) (G x-1) 0+1)*(32*i x) ≤ 2^width (G x-1) 0)
    (π : (x : X) → Equiv.Perm (Fin (maskWidth (A x) (i x) (G x) (B x))))
    (ctrl : (x : X) → Block 2 (A x) → Fin (i x) → Bool)
    (selectors : (fixedRowRegime r A hA).Has fun z => List.ofFn (ctrl z.1 z.2))
    (forward : r.Has fun x => Reflections.table (π x)) (backward : r.Has fun x => Reflections.table (π x).symm)
    {U : X → Type} (u : (x : X) → Series (U x)) (positive : ∀ x, 0 < (u x).count)
    (f : (x : X) → Block 2 (maskWidth (A x) (i x) (G x) (B x)) → U x → Bead)
    (ripe : r.ripe fun x => ((2^maskWidth (A x) (i x) (G x) (B x)*(u x).count : ℕ) : ℝ)) :
    let h := extent (fun x => G x-1) (fun _ => 0) i
    let k x := maskWidth (A x) (i x) (G x) (B x)
    let V x := 2^(k x)*(u x).count
    let src := together r.header (cloth (fun x => line 2 (k x)) u f)
    let dst := cloth (fun x => line 2 (k x)) u (fun x z => f x (naturalStage (π x) (ctrl x) z))
    ∃ (pre post : Cmd) (mid : Template), ∀ c ρ, 0 ≤ ρ → Controlled.Effective.rectContract c ρ →
      (∀ a b, ∃ T S : X → ℕ, Runs (Controlled.Effective.BatchCmd.compile pre post mid a b c) T S src dst) ∧
      ∃ d : ℕ, ∀ a b, d ≤ a → d ≤ b → ⌈ρ⌉₊+2 ≤ b →
        ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
          (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, payloadBits d (Q y) ≤ B (pick y)) →
          (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) →
          (∀ y, factor y ≤ 2^(A (pick y))) →
          Runs (Controlled.Effective.BatchCmd.compile pre post mid a b c) (fun y => V (pick y)*(positionFactor ρ (k (pick y))+factor y+1))
            (V ∘ pick) (src ∘ pick) (dst ∘ pick) := by
  intro h k V src dst
  let first x (z : Block 2 (k x)) := f x ((permuteNative (π x)).symm z)
  let second x (z : Block 2 (k x)) := first x (flatMask (H := G x-1) (A x) 0 (B x) (ctrl x) z)
  let natural x (z : Block 2 (k x)) := f x (naturalStage (π x) (ctrl x) z)
  have placed : (fun x z => f x (flatBitPullback (π x).symm z)) = first := by
    funext x z
    rw [← nativeUnplace]
  have undone : (fun x z => second x (flatBitPullback (π x) z)) = natural := by
    funext x z
    rw [← nativePullback]
    rfl
  obtain ⟨pre,hpre⟩ := boundedOfCarries (backward.cooked ripe)
  obtain ⟨post,hpost⟩ := boundedOfCarries (forward.cooked ripe)
  have preRun : Runs pre V V r.header (fun x => send (Reflections.table (π x).symm)) := hpre
  have postRun : Runs post V V r.header (fun x => send (Reflections.table (π x))) := hpost
  obtain ⟨mid,law⟩ := Controlled.Effective.nativePreparedMaskTemplate A (fun x => G x-1) i B
    (fun x => (u x).count) hA hB u ctrl hc shape sparse selectors positive (fun _ => le_rfl) first
  refine ⟨pre,post,mid,fun rect ρ hρ contract => ?_⟩
  obtain ⟨raw,dMask,fast⟩ := law rect ρ hρ contract
  obtain ⟨dRoute,route⟩ := routeCmd_runs hρ contract
  constructor
  · intro a b
    obtain ⟨ta,ra⟩ := routeCmd_total hρ contract a b k u positive (fun x => (π x).symm) f
    obtain ⟨tb,rb⟩ := routeCmd_total hρ contract a b k u positive π second
    rw [placed] at ra
    rw [undone] at rb
    exact Controlled.Effective.BatchCmd.runsSome ⟨V,V,preRun⟩ ⟨V,V,postRun⟩
      ⟨_,_,Runs.of_time ra⟩ raw ⟨_,_,Runs.of_time rb⟩
  · refine ⟨max dRoute dMask,?_⟩
    intro a b ha hb hbρ Y pick Q factor scale low rate high
    have left := route a b ((le_max_left ..).trans ha) ((le_max_left ..).trans hb) hbρ k u positive
      (fun x => (π x).symm) f
    have right := route a b ((le_max_left ..).trans ha) ((le_max_left ..).trans hb) hbρ k u positive π second
    unfold PositionCmd.PositionRuns at left right
    rw [placed] at left
    rw [undone] at right
    have lowMask (y : Y) : payloadBits dMask (Q y) ≤ B (pick y) :=
      (Nat.mul_le_mul_right _ (le_max_right dRoute dMask)).trans (low y)
    have masked := fast pick Q factor scale lowMask rate high
    let T y := V (pick y)*(positionFactor ρ (k (pick y))+factor y+1)
    have stepPos (y) : V (pick y)*(positionFactor ρ (k (pick y))+1) ≤ T y :=
      Nat.mul_le_mul_left _ (by omega)
    have stepMask (y) : V (pick y)*(factor y+1) ≤ T y :=
      Nat.mul_le_mul_left _ (by omega)
    have fits y : V (pick y) ≤ T y := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    obtain ⟨K,head⟩ := (Regime.self.cooked ripe).small
    apply Controlled.Effective.BatchCmd.run (t := T) (s := V ∘ pick) K _
      ((preRun.on pick).mono fits (fun _ => le_rfl)) ((postRun.on pick).mono fits (fun _ => le_rfl))
      ((left.on pick).mono stepPos (fun _ => le_rfl)) (masked.mono stepMask (fun _ => le_rfl))
      ((right.on pick).mono stepPos (fun _ => le_rfl))
    intro y
    have cap := head (pick y)
    change ((r.header (pick y)).count : ℝ) ≤ (K : ℝ) * (V (pick y) : ℝ) at cap
    exact (show (r.header (pick y)).count ≤ K*V (pick y) by exact_mod_cast cap).trans
      (Nat.mul_le_mul_left _ ((fits y).trans (Nat.le_succ _)))

end
end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
