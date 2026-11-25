import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveChoice
import OAI.Computability.NearSquareRoot.SynchronizedPermutationConjugateCompiled

/-! # A single emitted batch program for both unrestricted and fast executions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader.PassPoint
open IntegerMultiplication Code Adic Strip Loom Packed FixedPoint Controlled Controlled.PermutationLayout
open Space PositionProgram SynchronizedPermutationBudget EffectiveBoundedTask

noncomputable section
set_option maxHeartbeats 500000

abbrev source (s : Input) := Tree.fork (send s.1.descriptor) (beads s)
abbrev result (s : Input) := beads (move s)

noncomputable def charge (ρ : ℝ) (p : PassPoint) : ℕ :=
  p.volumeB*(positionFactor ρ p.k+rowFactor p.k ρ+1)

/-- The source template works for all choices of the three reserve parameters,
including choices too small for the target complexity. A single degree, fixed
before the choices of either relocation reserve or the low mask reserve,
suffices for the sharp resource bounds on the very same command. -/
theorem compile :
    ∃ (pre post : Cmd) (mid : Controlled.Effective.Template), ∀ (rect : Cmd) (ρ : ℝ),
      0 ≤ ρ → ρ ≤ 1 → Controlled.Effective.rectContract rect ρ →
      (∀ a b, ∃ time space : Input → ℕ,
        Runs (Controlled.Effective.BatchCmd.compile pre post mid a b rect) time space source result) ∧
      ∃ d : ℕ, ∀ a b, d ≤ a → d ≤ b → ⌈ρ⌉₊+2 ≤ b →
        ∀ {Y : Type} (pick : Y → Input), (∀ y, d ≤ (pick y).1.D) →
          Runs (Controlled.Effective.BatchCmd.compile pre post mid a b rect)
            (fun y => charge ρ (pick y).1) (fun y => (pick y).1.volumeB) (source ∘ pick) (result ∘ pick) := by
  let point := fun s : Input => s.1
  let r := regime point
  let A := fun s : Input => s.1.high
  let G := fun s : Input => guardWidth s.1.k
  let i := fun s : Input => s.1.count
  let B := fun s : Input => s.1.suffix
  have supplied : r.Has (fun x =>
      ((tally (point x).k,tally (A x),tally (G x-1),tally (i x),tally (B x)),
        (point x).descriptor.2) : Input → PlacedHeader) := by
    convert available point using 1
    funext x
    exact (congrArg (fun y : PlacedHeader => (y.1,(point x).descriptor.2)) (geometry (point x))).symm
  obtain ⟨_,hA,_,_,hB,hc,shape,_⟩ := geometryHas (fun s => s.1.k) A (fun s => G s-1) i B
    (fun s => s.1.descriptor.2) supplied
  have vol (s : Input) : 2^s.1.nativeWidth*(grain s).count = volumeB s.1 := by
    simp [s.1.placement.width,grain,volumeB]
  have ripe : r.ripe (fun s => ((2^s.1.nativeWidth*(grain s).count : ℕ) : ℝ)) := by
    simp only [vol]
    apply ripeOfPolyScale r (fun s => s.1.k) (fun s => volumeB s.1) (Dom.base _)
    intro s
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by decide) (Nat.succ_pos _))
  have pos (s : Input) : 0 < (grain s).count := by simp [grain]
  obtain ⟨tab,inv⟩ := placementHas point
  obtain ⟨pre,post,mid,program⟩ := compiledNaturalBatch A G i B hA hB hc shape (fun s => s.1.sparse)
    (fun s => s.1.placement.route) (fun s => s.1.placement.flag) (flagHas point hA) tab inv
    grain pos nativePayload ripe
  refine ⟨pre,post,mid,fun rect ρ lo hi leaf => ?_⟩
  obtain ⟨total,d,fast⟩ := program rect ρ lo leaf
  have initial (s : Input) : together r.header (cloth charts grain nativePayload) s = source s :=
    congrArg (Tree.fork (send s.1.descriptor)) (initialBeads s)
  have final_ (s : Input) :
      cloth charts grain (fun s a => nativePayload s (naturalStage s.1.placement.route s.1.placement.flag a)) s = result s :=
    finalBeads s
  constructor
  · intro a b
    obtain ⟨T,S,run⟩ := total a b
    refine ⟨T,S,?_⟩
    rw [← funext initial,← funext final_]
    exact run
  · refine ⟨d,?_⟩
    intro a b goodA goodB room Y pick enough
    have run := fast a b goodA goodB room pick (fun y => (pick y).1.k) (fun y => rowFactor (pick y).1.k ρ)
      (fun _ => le_rfl) (fun y => Nat.mul_le_mul_right _ (enough y)) (fun y => (pick y).1.rate lo hi)
      (fun y => (pick y).1.factor_high lo hi)
    obtain ⟨C,h⟩ := run
    refine ⟨C,fun y env decks base cap => ?_⟩
    have proof := h y env decks base cap
    change BoundedFits env _ (pile 0 (together r.header (cloth charts grain nativePayload) (pick y)) decks)
      (pile 0 (cloth charts grain (fun s a => nativePayload s (naturalStage s.1.placement.route s.1.placement.flag a)) (pick y)) decks)
      (C*((2^(pick y).1.nativeWidth*(grain (pick y)).count)*
        (positionFactor ρ (pick y).1.nativeWidth+rowFactor (pick y).1.k ρ+1)+1))
      (base+C*(2^(pick y).1.nativeWidth*(grain (pick y)).count+1))
      (C*(2^(pick y).1.nativeWidth*(grain (pick y)).count+1)) at proof
    rw [initial,final_,vol,(pick y).1.placement.width] at proof
    exact proof

end
end Benes.PackedBatchHeader.PassPoint

end NearSquareRoot
end Computability
end OAI
