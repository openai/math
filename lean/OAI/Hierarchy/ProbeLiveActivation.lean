import OAI.Hierarchy.ProbePurchasedRoots
import OAI.Hierarchy.ProbeActivation
import OAI.Hierarchy.ProbePurchaseScale

namespace OAI
/-! # Activating the actual selected CT probe slots in the adaptive potential -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

/-- The common-frame estimates needed for one purchased link have precisely the
physical tile endpoints, signed direction, and zero-cost sampler equalities of that
purchased list. Distinct post-activation roots may use completely unrelated frames. -/
structure ChainFrame (path : LiveChains S π depth marked) (M η : ℝ)
    (post : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ) where
  inlet : Fin (depth+1) → Coordinates k
  outlet : Fin (depth+1) → Coordinates k
  joined : ∀ j : ℕ, ∀ hj : j+1<depth+1, outlet ⟨j,by omega⟩=inlet ⟨j+1,hj⟩
  priced : ∀ j, |rise M (post (liveSlots S π depth marked (path,j))) -
    max (Source.sign path.2.1.2*(outlet j path.2.1.1-inlet j path.2.1.1)) 0| ≤ η
  probe : |0-max (dist (inlet 0) (outlet (Fin.last depth))-1) 0|≤η

/-- Apply a frame only at roots passing the actual post-test. Every paid probe is
still charged at full, including those with failing discrepancy. -/
theorem live_activation {a M s B u δ η fee : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (upper : s≤1) (hB : 0≤B)
    (calibrate : 4*δ^2 ≤ u) (resolution : η < δ) (long : 1+η < (depth+1:ℕ)*(δ-η))
    (old post : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ)
    (marks : ∀ t c r, r∈marked t c → u ≤ s*(rise M (old (.inr ((r,t),c))))^2)
    (good : Finset (LiveChains S π depth marked))
    (frame : ∀ x : ↥good, ChainFrame S π depth marked x.val M η post) :
    (good.card:ℝ)*(B*u/8)-(Fintype.card (LiveChains S π depth marked):ℝ)*fee ≤
    (s/2)*divergence a M (bonus B) old post-(Fintype.card (LiveChains S π depth marked):ℝ)*fee := by
  classical
  let embed : (↥good × Fin (depth+1)) ↪ (LiveChains S π depth marked × Fin (depth+1)) :=
    (Function.Embedding.subtype _).prodMap (Function.Embedding.refl _)
  let slots := embed.trans (liveSlots S π depth marked)
  let z (p : ↥good) (i : ℕ) := if hi : i<depth+1 then (frame p).inlet ⟨i,hi⟩ else (frame p).outlet (Fin.last depth)
  have start (p : ↥good) : z p 0=(frame p).inlet 0 := by simp [z]
  have finish (p : ↥good) : z p (depth+1)=(frame p).outlet (Fin.last depth) := by simp [z]
  have atIn (p : ↥good) (j : Fin (depth+1)) : z p j.val=(frame p).inlet j := by dsimp only [z]; rw [dite_eq_left j.isLt]
  have atOut (p : ↥good) (j : Fin (depth+1)) : z p (j.val+1)=(frame p).outlet j := by
    by_cases next : j.val+1<depth+1
    · dsimp only [z]; rw [dite_eq_left next]; exact ((frame p).joined j.val next).symm
    · simp only [z,dite_eq_right next]
      have last : Fin.last depth=j := Fin.ext (by simp; omega)
      rw [last]
  have raw := activation_from_frames slots (fun p => p.val.2.1.1) (fun p => p.val.2.1.2)
    z a M s B u δ η fee (Fintype.card (LiveChains S π depth marked)) (bonus B) old post ha hs upper hB
    (fun i => by cases i <;> simp [bonus,hB]) calibrate resolution long (fun _ _ => le_rfl)
    (fun p j => marks _ _ _ (liveSlot_marked S π depth marked p.val j))
    (fun p j => by rw [atOut,atIn]; exact (frame p).priced j)
    (fun p => by simpa only [start,finish] using (frame p).probe)
  simpa only [Fintype.card_coe] using raw

end
end Hierarchy.ProbeStage

end OAI
