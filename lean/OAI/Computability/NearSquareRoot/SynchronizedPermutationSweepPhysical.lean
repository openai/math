import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepConjugate
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepHas
import OAI.Computability.NearSquareRoot.SynchronizedPermutationActualPull

/-! # Execute the compiled batch at the declared Fourier record addresses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Adic Loom Packed Strip Staff
open Controlled Controlled.PermutationLayout BoxFin NearSquareRoot.Space PositionProgram

noncomputable section
set_option maxHeartbeats 500000

private theorem transport {a k : ℕ} (e : a = k) {U : Type} (u : Series U)
    (f : Block 2 k → U → Bead) :
    stripe (line 2 a) (fun z => strip u (f (castWord e z))) =
      stripe (line 2 k) (fun z => strip u (f z)) := by
  subst k
  rfl

/-- The actual geometry rulers and switch plan suffice to execute the batch.
Both sides are the raw bead array in increasing order of the declared address,
with the output payload pulled from the switch network's source address. -/
theorem physical {X : Type} {r : Regime X} (k L A G b low : X → ℕ) (ρ : ℝ) (hρ : 1/2 < ρ)
    (box : X → List (ℕ × ℕ)) [∀ x j, NeZero (modulus (box x) j)]
    (hb : ∀ x, BoxShape.Valid (k x) (L x) (box x)) (hd : ∀ x, 4 ≤ (box x).length)
    (code : X → Staging) (tables : (x : X) → Fin ((box x).length/4) → RawTable)
    (which : (x : X) → Fin ((box x).length/4) → ℕ) (stage : X → Bool × ℕ) (batch : X → ℕ)
    (supply : r.Has (fun x => ((tally (k x),tally (A x),tally (G x-1),tally (b x),tally (low x)),code x) : X → PlacedHeader))
    (cert : ∀ x, RealizesBatch (p := A x) (b := b x) (G := G x) (low := low x)
      (hb x) (hd x) (code x) (tables x) (which x) (stage x) (batch x))
    (small : Dom k r.scale)
    (sparse : ∀ x, (3*cap (b x) (G x-1) 0+1)*(32*b x) ≤ 2^width (G x-1) 0)
    {U : X → Type} (u : (x : X) → Series (U x)) (positive : ∀ x, 0 < (u x).count)
    (v : (x : X) → PackedAddress Unit (physicalWidth (box := box x)) → U x → Bead) :
    let h := extent (fun x => G x-1) (fun _ => 0) b
    let V x := 2^(k x)*(u x).count
    let rank x := recordAddress (hb x) (hd x)
    let net x := batchStage (which x) (physicalWidth (box := box x)) (fun _ : Unit => tables x) (stage x) (batch x)
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (Q factor : Y → ℕ),
      (∀ y, r.scale (pick y) ≤ Q y) → (∀ y, payloadBits D (Q y) ≤ low (pick y)) →
      (∀ y, 2*Spindle.modes h (τ := ρ) (pick y) ≤ factor y) →
      (∀ y, factor y ≤ 2^(A (pick y))) →
      BoundedTask (fun y => V (pick y)*(positionFactor ρ (k (pick y))+factor y+1)) (V ∘ pick)
        (together r.header (cloth (fun x => line 2 (k x)) u (fun x a => v x (rank x a))) ∘ pick)
        (cloth (fun x => line 2 (k x)) u (fun x a => scatter (net x) (v x) (rank x a)) ∘ pick) := by
  obtain ⟨_,hA,_,_,hB,hc,shape,key⟩ := geometryHas k A (fun x => G x-1) b low code supply
  choose eq π ctrl emit mask _ pull _ using (fun x => RealizesBatch.pull (hb x) (hd x) (cert x))
  have get : r.Has (fun x => Reflections.table (π x)) := by
    have ready := key.ez (show Easy (fun s : Staging => s.1.1) from Easy.fst.compose Easy.fst)
    simpa only [emit] using ready
  have undo : r.Has (fun x => Reflections.table (π x).symm) := by
    have ready := key.ez (show Easy (fun s : Staging => s.1.2) from Easy.fst.compose Easy.snd)
    simpa only [emit] using ready
  have selectors : (fixedRowRegime r A hA).Has (fun z => List.ofFn (ctrl z.1 z.2)) := by
    simpa only [mask] using maskBits_has A hA code key
  let rank x := recordAddress (hb x) (hd x)
  let net x := batchStage (which x) (physicalWidth (box := box x)) (fun _ : Unit => tables x) (stage x) (batch x)
  let f x a := v x (rank x (castWord (eq x) a))
  have whole := ripeOfPolyScale r k (fun x => 2^(k x)*(u x).count) small
    (fun x => Nat.le_mul_of_pos_right _ (positive x))
  have ripe : r.ripe (fun x => ((2^maskWidth (A x) (b x) (G x) (low x)*(u x).count : ℕ) : ℝ)) := by
    simpa only [eq] using whole
  obtain ⟨D,run⟩ := naturalBatch A G b low ρ hρ hA hB hc shape sparse π ctrl selectors get undo u positive f ripe
  refine ⟨D,fun pick Q factor scale enough rate hi => ?_⟩
  apply (run pick Q factor scale enough rate hi).conform (fun y => by simp only [eq])
    (fun y => by simp only [Function.comp_apply,eq])
  · intro y
    exact congrArg (Tree.fork (r.header (pick y)))
      (transport (eq (pick y)) (u (pick y)) (fun a => v (pick y) (rank (pick y) a)))
  · intro y
    let x := pick y
    refine Eq.trans ?_ (transport (eq x) (u x) (fun a => scatter (net x) (v x) (rank x a)))
    apply congrArg (stripe _)
    funext a
    exact congrArg (strip (u x)) (pull x (v x) a)

end
end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
