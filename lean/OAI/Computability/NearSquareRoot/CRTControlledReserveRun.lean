import OAI.Computability.NearSquareRoot.CRTControlledReserveAddress
import OAI.Computability.NearSquareRoot.CRTControlledReserveCompiler
import OAI.Computability.NearSquareRoot.CRTControlledFlatSwapList
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Running one reserved matching from a shared P192 header

The header supplies both copies of the exchange list and the header of the
middle program. Each exchange pass reads its copy in the requested direction.
The saved headers and each complete intermediate array fit the same space bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveStage
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Strip NearSquareRoot.Space

noncomputable section

private theorem parkHeader {I : Type} {V T : I → ℕ} {source target header : I → Tree}
    (run : BoundedTask T V source target) (small : Volume (fun i => (V i : ℝ)) header) :
    BoundedTask (fun i => V i + T i) V
      (fun i => .fork (header i) (source i)) (fun i => .fork (header i) (target i)) := by
  obtain ⟨C,hC⟩ := small
  have cap i : (header i).count ≤ C*V i := by
    have h : ((header i).count : ℝ) ≤ (C : ℝ)*V i := hC i
    exact_mod_cast h
  apply (run.right header).bound (C+1) (C+1)
  · intro i
    have h := cap i
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega
  · intro i
    have h := cap i
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega

/-- Save the shared header across a bounded pass, including both the initial
copy and the cost of parking it while the pass runs. -/
theorem retainBoundedHeader {I : Type} {V T : I → ℕ} {source target header : I → Tree}
    (run : BoundedTask T V (fun i => .fork (header i) (source i)) target)
    (base : Carries (fun i => (V i : ℝ)) header header)
    (small : Volume (fun i => (V i : ℝ)) source) (room : ∀ i, V i ≤ T i) :
    BoundedTask T V (fun i => .fork (header i) (source i)) (fun i => .fork (header i) (target i)) := by
  have get := Carries.dropRight base.budget base.small small
  have prep := boundedOfCarries (get.twice (Carries.idles base.budget (base.small.fork small base.budget)))
  exact (prep.compose (parkHeader run base.small)).bound 3 1 (fun i => by have := room i; omega)
    (fun i => by simp)

/-- Execute a compiled stage on complete records. The supplied middle command
reads a flat record permutation and consumes the header prepared for it. -/
theorem boundedRun {I : Type} (k lo hi V T : I → ℕ)
    (s : (i : I) → ReserveStage (k i) (lo i) (hi i))
    (distinct : ∀ i, ∀ a ∈ (s i).moves, a.1 ≠ a.2)
    (D : ℕ) (hlen : ∀ i, (s i).moves.length ≤ D*(k i+1))
    (f : (i : I) → Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (header midHeader : I → Tree)
    (keys : Carries (fun i => (V i : ℝ)) header (fun i => send (flatSwapInput (k i) (s i).moves)))
    (supplyMid : Carries (fun i => (V i : ℝ)) header midHeader)
    (m : (i : I) → Equiv.Perm (Block 2 (k i)))
    (mid : BoundedTask T V
      (fun i => .fork (midHeader i) (stripe (line 2 (k i)) (f i ∘ swapsFlat (s i).moves)))
      (fun i => stripe (line 2 (k i)) ((f i ∘ swapsFlat (s i).moves) ∘ m i))) :
    BoundedTask (fun i => ((s i).moves.length+1)*V i + T i) V
      (fun i => .fork (header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ (s i).flatRead (m i))) := by
  let data i := stripe (line 2 (k i)) (f i)
  let afterMid i := (f i ∘ swapsFlat (s i).moves) ∘ m i
  have volume : Volume (fun i => (V i : ℝ)) data :=
    ⟨1,fun i => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr (inputCap i)⟩
  have get := Carries.dropRight keys.budget keys.small volume
  have prep := boundedOfCarries ((get.chain keys).twice ((get.chain supplyMid).twice (keys.first volume)))
  have fwd := boundedFlatSwaps false k V (fun i => (s i).moves) distinct D hlen f inputCap
  have saved := parkHeader (parkHeader fwd supplyMid.out) keys.out
  have middle := parkHeader mid keys.out
  have back := boundedFlatSwaps true k V (fun i => (s i).moves) distinct D hlen afterMid (fun i => by
    simpa only [afterMid,stripe_count_perm] using inputCap i)
  apply (((prep.compose saved).compose middle).compose back).bound 6 1
  · intro i
    have h : V i ≤ ((s i).moves.length+1)*V i := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · intro i
    simp

/-- A regime whose scale is at most the register width can afford any of
its polynomial header programs in one linear-volume preparation pass. -/
theorem ripeOfWidth {I : Type} {r : Regime I} {k V : I → ℕ}
    (scale : ∀ i, r.scale i ≤ k i) (array : ∀ i, 2^(k i) ≤ V i) :
    r.ripe (fun i => (V i : ℝ)) := by
  constructor
  · intro i
    change (1 : ℝ) ≤ V i
    exact_mod_cast (show 1 ≤ V i from (Nat.two_pow_pos (k i)).trans_le (array i))
  · intro d
    obtain ⟨C,hC⟩ := polynomial_le_multiple_array_length d
    refine ⟨C,fun i => ?_⟩
    have h₁ := Nat.pow_le_pow_left (Nat.succ_le_succ (scale i)) d
    change (((r.scale i+1)^d : ℕ) : ℝ) ≤ (C : ℝ) * V i
    exact_mod_cast (h₁.trans ((hC (k i)).trans (Nat.mul_le_mul_left C (array i))))

/-- Read the swap keys from the actual stage descriptor on the regime header.
The same header supplies the parameters required by the middle program. -/
theorem boundedRunUniform {I : Type} {r : Regime I} (k lo hi V T : I → ℕ)
    (s : (i : I) → ReserveStage (k i) (lo i) (hi i))
    (distinct : ∀ i, ∀ a ∈ (s i).moves, a.1 ≠ a.2)
    (D : ℕ) (hlen : ∀ i, (s i).moves.length ≤ D*(k i+1))
    (f : (i : I) → Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (scale : ∀ i, r.scale i ≤ k i)
    (width : r.Has (fun i => tally (k i)))
    (desc : r.Has (fun i => ReserveProgram.encode (s i)))
    (midHeader : I → Tree) (supplyMid : r.Small midHeader)
    (m : (i : I) → Equiv.Perm (Block 2 (k i)))
    (mid : BoundedTask T V
      (fun i => .fork (midHeader i) (stripe (line 2 (k i)) (f i ∘ swapsFlat (s i).moves)))
      (fun i => stripe (line 2 (k i)) ((f i ∘ swapsFlat (s i).moves) ∘ m i))) :
    BoundedTask (fun i => ((s i).moves.length+1)*V i + T i) V
      (fun i => .fork (r.header i) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ (s i).flatRead (m i))) := by
  have ripe := ripeOfWidth scale (V := V) (fun i => by
    have h := inputCap i
    rw [stripe, Task.forest_count, Series.card, lineSize] at h
    omega)
  have key : r.Has (fun i => flatSwapInput (k i) (s i).moves) := width.pair (desc.ez Easy.fst)
  exact boundedRun k lo hi V T s distinct D hlen f inputCap r.header midHeader (key.cooked ripe)
    (supplyMid.cooked ripe) m mid

end
end Controlled.ReserveStage

end NearSquareRoot
end Computability
end OAI
