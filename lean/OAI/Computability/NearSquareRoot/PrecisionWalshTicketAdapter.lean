import OAI.Computability.NearSquareRoot.PrecisionGridPreparedPass
import OAI.Computability.NearSquareRoot.PhysicalWalshGroupedRate

/-! # Retaining the chronological Walsh ticket during the physical branch

The mask is prepared using only the compact ticket while the record stream is
parked. The same ticket is returned alongside the updated records. The address
array contributes its bit volume to the clock and occupied-tape bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code Strip PhysicalWalsh PhysicalWalsh.Pieces

private theorem words_volume {k : ℕ} (x : Fin (2^k) → Record k) :
    (send (Odd.words x)).count ≤ 820*(sparseSpace k+1) := by
  have hv := odd_volume_le k
  have hn := Nat.two_pow_pos k
  have he : size (Odd.words x) = 2^k*(4*(componentBits k+1)+4)+1 := by
    simpa only [Odd.words,List.length_ofFn] using Padding.marks_size (w:=componentBits k) (List.ofFn x)
  change size (Odd.words x) ≤ _
  rw [he]
  unfold Odd.volume at hv
  unfold componentBits
  nlinarith only [hv,hn,Nat.zero_le (2^k),Nat.zero_le (sparseSpace k)]

/-- Frame an actual flag-driven Walsh pass by the header of a setup regime.
The payload and returned data use the original increasing address ordinals. -/
theorem walshPassPrepared {I : Type} {s : Regime I} {k : I → ℕ} {ρ : ℝ} (hr : 0 ≤ ρ)
    {flags : I → List Bool} (available : s.Has flags)
    (x y : (i : I) → Fin (2^k i) → Record (k i))
    (raw : Space.BoundedTask (sparseTime ρ ∘ k) (sparseSpace ∘ k)
      (fun i => send (flags i, Odd.words (x i))) (fun i => send (Odd.words (y i)))) :
    ∃ setup : I → ℕ, Dom s.scale setup ∧
      Space.BoundedTask (fun i => setup i + sparseTime ρ (k i)) (fun i => setup i + sparseSpace (k i))
        (fun i => .fork (s.header i) (send (List.ofFn fun j => Dusk.mark (x i j))))
        (fun i => .fork (s.header i) (send (List.ofFn fun j => Dusk.mark (y i j)))) := by
  let data i := send (Odd.words (x i))
  let mask i := send (flags i)
  have flipped := (Space.BoundedTask.swap data mask).compose raw
  obtain ⟨prep,dom,task⟩ := passPreparedHeader (s:=s) (data:=data) (packet:=mask) available flipped
  let setup i := prep i + (mask i).count
  refine ⟨setup,dom.add available.extent,?_⟩
  have hin (i : I) := words_volume (x i)
  have bound := task.bound 1642 1642
    (time':=fun i => setup i + sparseTime ρ (k i)) (space':=fun i => setup i + sparseSpace (k i)) (by
      intro i
      have ht := space_le_clock hr (k i)
      change prep i + (data i).count + ((data i).count + (mask i).count + sparseTime ρ (k i)) + 1 ≤
        1642*(prep i + (mask i).count + sparseTime ρ (k i)+1)
      have h : (data i).count ≤ _ := hin i
      omega) (by
      intro i
      change prep i + (data i).count + max ((data i).count + (mask i).count) (sparseSpace (k i)) + 1 ≤
        1642*(prep i + (mask i).count + sparseSpace (k i)+1)
      have h : (data i).count ≤ _ := hin i
      omega)
  simpa only [data,Odd.words,List.map_ofFn,Function.comp_def] using bound

end FixedPoint

end NearSquareRoot
end Computability
end OAI
