import OAI.Computability.IntegerMultiplication.Strip.Rails

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I K : Type} {w : I→ℝ} {input : I→Tree} {A : I→Type}

/-- Dynamic preceding field after a fixed narrow one. With ranks transposed directly. -/
theorem bubble (s : Series K) (t : (i:I)→Series (A i)) (v : (i:I)→A i × K→Tree)
    (h : Carries w input (stackRun (fun i => (t i).cart s) v))
    (n : Carries w input (fun i => send (tally (t i).count))) :
    Carries w input (stackRun (fun i => s.cart (t i))
      fun i p => v i (p.2,p.1)) := by
  have g := n.out
  unfold Volume at g
  obtain ⟨D,d⟩ := g
  have c (i) : (t i).count ≤ (D:ℝ)*w i := by
    specialize d i
    change ((size (tally _) : ℕ) : ℝ) ≤ _ at d
    rw [size_tally,tally_length] at d
    push_cast at d
    linarith [show (0:ℝ)≤(t i).count from Nat.cast_nonneg _]
  have hf := carve (v:=v) (fun i => t i) (fun _ : I => s) h
    (n.twice (fixture n.small n.budget (send (tally s.count))))
    ⟨(D+1)*(s.count+1),fun i => by
      calc
       _ ≤ ((D:ℝ)*w i+w i)*(s.count+1) := by
        apply mul_le_mul_of_nonneg_right (add_le_add (c i) (n.budget i)) (by positivity)
       _ = _ := by push_cast; ring⟩
  exact flatten (fun _ => s) t (fun i p => v i (p.2,p.1)) (unlay s t _ hf)

theorem seeds (s : (i:I) → Series (A i)) (n : Carries w input (fun i => send (tally (s i).count))) :
    Carries w input (stackRun s (fun _ _ => (.atom false))) := by
  have h := n.chain (Carries.func n.budget n.out (fun x : Tally => fill () x)
    (by fun_prop))
  suffices e : (fun i => send (fill () (tally (s i).count))) =
      stackRun s (fun _ _ => .atom false) by rwa [e] at h
  funext i
  simp only [stackRun,stripe_simple,Series.count, fill_eq,tally_length,← forest_send]
  induction (s i).explore with
  | nil => rfl
  | cons x l ih => rw [List.length_cons,List.replicate_succ,forest_cons,forest_cons,ih]; rfl

theorem sink (s : Series K) (t : (i:I)→Series (A i)) (v : (i:I)→K × A i→Tree)
    (h : Carries w input (stackRun (fun i => s.cart (t i)) v))
    (n : Carries w input (fun i => send (tally (t i).count))) :
    Carries w input (stackRun (fun i => (t i).cart s)
      fun i p => v i (p.2,p.1)) := by
  obtain ⟨D,d⟩ := n.out
  have c (i) : (t i).count ≤ (D:ℝ)*w i := by
    specialize d i
    change ((size (tally _) : ℕ) : ℝ) ≤ _ at d
    rw [size_tally,tally_length] at d
    push_cast at d
    linarith [show (0:ℝ)≤(t i).count from Nat.cast_nonneg _]
  have hf := carve (v:=v) (fun _ : I => s) (fun i => t i) h
    ((fixture n.small n.budget (send (tally s.count))).twice n)
    ⟨(D+1)*(s.count+1),fun i => by
      calc
       _ ≤ ((s.count:ℝ)+1)*((D:ℝ)*w i+w i) := by
        apply mul_le_mul_of_nonneg_left (add_le_add (c i) (n.budget i)) (by positivity)
       _ = _ := by push_cast; ring⟩
  exact flatten t (fun _ => s) (fun i p => v i (p.2,p.1)) (lay s t _ hf (seeds t n))

end Strip

end IntegerMultiplication
end Computability
end OAI
