import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix

/-! # Applying a padded three-slot command inside a real Walsh lane

The original compact descriptor is parked during the long command. It then
supplies the exact length for cropping the result on the same tape. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Interior

open IntegerMultiplication Code Space SwapPrefix

private theorem header_le (A d : ℕ) (s : Shape) (hd : 1 ≤ d) :
    size (Header.wire A s) ≤ allowance A d s := by
  have pow := Nat.pow_le_pow_right (n:=Header.scale A s+1) (by omega) hd
  rw [pow_one] at pow
  exact (Nat.le_add_right _ 1).trans (pow.trans (Nat.le_add_left ..))

/-- The total task adds the cost of a genuine prefix pad and crop to the
specified interior pass, retaining its separate time and space bounds. -/
theorem realLane {I : Type} (A W : ℕ) (s : I → Shape) (x y : (i:I) → Data (s i))
    (T : I → ℕ) {d : ℕ}
    (run : BoundedTask (fun i => allowance A d (s i) + T i) (allowance A d ∘ s)
      (fun i => send (Header.wire A (s i),stream (paddedSize A W (s i)) (extend A W (s i) (x i))))
      (fun i => send (stream (paddedSize A W (s i)) (y i)))) :
    ∃ e : ℕ, BoundedTask (fun i => allowance A e (s i) + T i) (allowance A e ∘ s)
      (fun i => send (Header.wire A (s i),laneFlat A W (s i) (x i)))
      (fun i => send (laneFlat A W (s i) (y i))) := by
  obtain ⟨p,pad⟩ := padWithHeader A W s x
  obtain ⟨c,cut⟩ := crop A W s y
  let e := max (max p c) (d+1)
  let b i := allowance A e (s i)
  let hd i := Header.wire A (s i)
  let pre i := stream (paddedSize A W (s i)) (extend A W (s i) (x i))
  let out i := stream (paddedSize A W (s i)) (y i)
  have hp : p ≤ e := le_trans (le_max_left ..) (le_max_left ..)
  have hc : c ≤ e := le_trans (le_max_right ..) (le_max_left ..)
  have he : d+1 ≤ e := le_max_right ..
  have hs (i : I) : size (hd i) ≤ b i := header_le A e (s i) (by omega)
  have p1 := pad.mono (time':=b) (space':=b) (fun i => allowance_mono hp (s i)) (fun i => allowance_mono hp (s i))
  have dup := PhysicalWalshGrid.easyWithin b (Easy.identity.pair Easy.fst)
    (fun i => (hd i,pre i)) 20 (fun i => by
      have u := hs i
      have v := stream_cost A W e (s i) _ (extend A W (s i) (x i)) le_rfl
      change size (pre i) ≤ 16*b i+1 at v
      change size (hd i)+size (pre i)+1 ≤ 20*(b i+1)
      omega)
  have core := run.left (send ∘ hd)
  have mid := core.bound (time':=fun i => b i+T i) (space':=b) 1 2 (fun i => by
    have h : allowance A d (s i) ≤ b i := allowance_mono (Nat.le_succ d |>.trans he) (s i)
    change allowance A d (s i)+T i+1 ≤ 1*(b i+T i+1)
    omega) (fun i => by
    have h : allowance A d (s i) ≤ b i := allowance_mono (Nat.le_succ d |>.trans he) (s i)
    have hh := hs i
    change allowance A d (s i)+size (hd i)+1 ≤ 2*(b i+1)
    omega)
  have flip := PhysicalWalshGrid.easyWithin b (Easy.exchange (X:=List Dusk.Pair) (Y:=Header.Wire))
    (fun i => (out i,hd i)) 20 (fun i => by
      have u := hs i
      have v := stream_cost A W e (s i) _ (y i) le_rfl
      change size (out i) ≤ 16*b i+1 at v
      change size (out i)+size (hd i)+1 ≤ 20*(b i+1)
      omega)
  have finish := cut.mono (time':=b) (space':=b) (fun i => allowance_mono hc (s i)) (fun i => allowance_mono hc (s i))
  have assembled := ((((p1.compose dup).compose mid).compose flip).compose finish)
  refine ⟨e,assembled.bound 5 1 ?_ ?_⟩
  · intro i; change b i + b i + (b i+T i)+b i+b i+1 ≤ 5*(b i+T i+1); omega
  · intro i; simp [b]

end PhysicalWalshNode.Interior

end NearSquareRoot
end Computability
end OAI
