import OAI.Computability.NearSquareRoot.FixedCandidateFrame

/-! # Keeping the operand-width ruler across a physical layer

Only the short stage header is passed to the local program. The unary operand
width is parked while it runs and is reattached to the resulting array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code Space FixedCandidate

theorem linearTree {I X Y : Type} [Codec X] [Codec Y] (g : X → Y) (hg : Easy g)
    (x : I → X) {t n : I → ℕ} (K : ℕ) (hn : ∀ i, n i ≤ t i)
    (h : ∀ i, size (x i) ≤ K*(n i+1)) :
    BoundedTask t n (fun i => send (x i)) (fun i => send (g (x i))) := by
  apply (BoundedTask.of_time (hg.on x)).bound (K+1) (2*K+1)
  · intro i
    have u := (h i).trans (Nat.mul_le_mul_left K (Nat.succ_le_succ (hn i)))
    change size (x i) ≤ K*(t i+1) at u
    change size (x i)+1 ≤ (K+1)*(t i+1)
    rw [Nat.add_mul]
    omega
  · intro i
    have u := h i
    change size (x i)+size (x i)+1 ≤ (2*K+1)*(n i+1)
    rw [Nat.add_mul,Nat.mul_assoc]
    omega

/-- Lift a raw-array stage that uses and returns its small descriptor to a
stage on a framed array. It returns the original operand length even if the
stage permutes the entire array. -/
theorem framedStage {I : Type} (n t : I → ℕ) (hn : ∀ i, 2 ≤ n i) (hnt : ∀ i, n i ≤ t i)
    (header : I → Tree) (K : ℕ) (hh : ∀ i, (header i).count ≤ K*(n i+1))
    (x y : (i : I) → Array (n i))
    (raw : BoundedTask t n (fun i => .fork (header i) (send (records (x i))))
      (fun i => .fork (header i) (send (records (y i))))) :
    BoundedTask t n (fun i => .fork (header i) (framed (x i))) (fun i => framed (y i)) := by
  let pack (v : Tree × Tally × List Dusk.Pair) := ((v.1,v.2.2),v.2.1)
  let unpack (v : (Tree × List Dusk.Pair) × Tally) := (v.2,v.1.2)
  have prep := linearTree pack (by unfold pack; fun_prop)
    (fun i => (header i,tally (n i),records (x i))) (K+75001) hnt (fun i => by
      change (Tree.fork (header i) (framed (x i))).count ≤ _
      have := framed_size (hn i) (x i)
      have := hh i
      simp only [Tree.count,Nat.add_mul]
      omega)
  have core := (raw.left (fun i => send (tally (n i)))).bound (time' := t) (space' := n)
    1 4 (fun _ => by simp) (fun i => by change n i + size (tally (n i))+1 ≤ _; simp [size_tally]; omega)
  have done := linearTree unpack (by unfold unpack; fun_prop)
    (fun i => ((header i,records (y i)),tally (n i))) (K+75001) hnt (fun i => by
      have hb := framed_size (hn i) (y i)
      change size (tally (n i), records (y i)) ≤ _ at hb
      have hh' := hh i
      simp only [size_prod,Nat.add_mul] at hb ⊢
      change size (header i) ≤ K*(n i+1) at hh'
      omega)
  exact sequence (sequence prep core) done

end FixedLayer

end NearSquareRoot
end Computability
end OAI
