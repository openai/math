import OAI.Computability.NearSquareRoot.UniformMultiplicationRelease
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Foundation

/-! # Extending a large-input multiplication program to every positive width

The width comparison is one linear scan. On each of the finitely many short widths,
the ordinary exact product command has bounded time and stack height.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space.BoundedTask

open IntegerMultiplication Code

/-- Dispatch on an already encoded Boolean tag. Both branches operate on the
same payload and return to the same continuation. -/
theorem control {I : Type*} (tag : I → Bool) {t s : I → ℕ} {src dst : I → Tree}
    (hfalse : BoundedTask (fun i : {i // tag i = false} => t i.val) (fun i => s i.val)
      (fun i => src i.val) (fun i => dst i.val))
    (htrue : BoundedTask (fun i : {i // tag i = true} => t i.val) (fun i => s i.val)
      (fun i => src i.val) (fun i => dst i.val)) :
    BoundedTask t (fun i => s i + (src i).count) (fun i => .fork (.atom (tag i)) (src i)) dst := by
  obtain ⟨c,C,hc⟩ := hfalse
  obtain ⟨d,D,hd⟩ := htrue
  refine ⟨decodeBit c d,C+D+10,?_⟩
  intro i env r base hr
  let z := s i + (src i).count
  have cap : DeckCap (base + (C+D+10)*(z+1)) (pile 0 (.fork (.atom (tag i)) (src i)) r) := by
    apply (DeckCap.pile hr _ _).mono
    dsimp [Tree.count,z]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have inc (k : ℕ) (hk : k ≤ C+D) : k*(s i+1) ≤ (C+D+10)*(z+1) :=
    Nat.mul_le_mul (by omega) (by dsimp [z]; omega)
  have done (k : ℕ) (hk : k ≤ C+D) (cmd : Cmd)
      (run : BoundedFits env cmd (pile 0 (src i) r) (pile 0 (dst i) r)
        (k*(t i+1)) (base+k*(s i+1)) (k*(s i+1)))
      (sel : (bif tag i then d else c) = cmd) :
      BoundedFits env (decodeBit c d) (pile 0 (.fork (.atom (tag i)) (src i)) r)
        (pile 0 (dst i) r) ((C+D+10)*(t i+1))
        (base+(C+D+10)*(z+1)) ((C+D+10)*(z+1)) := by
    have run' := run.mono le_rfl (Nat.add_le_add_left (inc k hk) base) (inc k hk)
    rw [← sel] at run'
    apply (BoundedFits.decodeBit run' cap (Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega)))).mono _ le_rfl le_rfl
    have bound := Nat.mul_le_mul_right (t i + 1) hk
    rw [Nat.add_mul (C+D) 10]
    omega
  cases eq : tag i with
  | false => exact done C (by omega) _ (hc ⟨i,eq⟩ env r base hr) (by simp [eq])
  | true => exact done D (by omega) _ (hd ⟨i,eq⟩ env r base hr) (by simp [eq])

end Space.BoundedTask

namespace FixedCandidate

open IntegerMultiplication Code Space

private theorem input_count (i : MultiplicationInput) : (send i.operands).count = 4*i.width+3 := by
  change size i.operands = _
  rw [size_prod, Bits.size_word, Bits.size_word, ← i.val.property]
  change 2*i.width+1+(2*i.width+1)+1 = _
  omega

/-- Compute the small-width flag and retain an intact copy of both operands. -/
private theorem tag_task (K : ℕ) :
    Task (fun i : MultiplicationInput => i.width) (fun i => send i.operands)
      (fun i => Tree.fork (.atom (tags K i)) (send i.operands)) := by
  let f (p : Interface.Pair) := Iter.small (p.1,tally K)
  have hf : Easy f := (Easy.fst.pair (Easy.const _)).compose Iter.small_easy
  have tag (i : MultiplicationInput) : f i.operands = tags K i := by
    simp [f,Iter.small,tags,n0,v,MultiplicationInput.operands]
  have prep := ((hf.pair (Easy.identity (X := Interface.Pair))).on MultiplicationInput.operands)
  apply (prep.bound 5 (b' := fun i : MultiplicationInput => i.width) ?_).conform
    (fun _ => rfl) (fun _ => rfl)
  · intro i
    change Tree.fork (.atom (f i.operands)) _ = _
    rw [tag i]
    rfl
  · intro i
    change (send i.operands).count+1 ≤ _
    rw [input_count]
    omega

private theorem prefix_bound (f : ℕ → ℕ) (K : ℕ) : ∃ M, ∀ i < K, f i ≤ M := by
  induction K with
  | zero => exact ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ K ih =>
    obtain ⟨M,hh⟩ := ih
    refine ⟨max M (f K), fun i hi => ?_⟩
    rcases (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)) with h | rfl
    · exact (hh i h).trans (le_max_left ..)
    · exact le_max_right ..

/-- The P192 finite-input branch, whose entire peak fits a width-linear cap
because its input domain has bounded width. -/
private theorem short_task (K : ℕ) :
    BoundedTask (fun _ : shortS K => 0) (fun i => 8*(MultiplicationInput.width i.val))
      (fun i => send (MultiplicationInput.operands i.val)) (fun i => send (Lea.answer (MultiplicationInput.operands i.val))) := by
  obtain ⟨M,hM⟩ := prefix_bound (fun n => ⌈Lea.goalB n⌉₊) K
  have bound (i : shortS K) : ⌈budgetB i.val⌉₊ ≤ M :=
    hM (n0 i.val) (of_decide_eq_true i.property)
  have source := (winter K).release.bound (b' := fun _ => 0) (M+1) (fun i => by
    simpa using Nat.succ_le_succ (bound i))
  apply (BoundedTask.of_time source).mono (fun _ => le_rfl)
  intro i
  change (send (MultiplicationInput.operands i.val)).count + 0 ≤ _
  rw [input_count]
  have hn : 1 ≤ (MultiplicationInput.width i.val) := i.val.property
  omega

/-- One multiplication command at all positive input widths, with a linear
width check and the same large-input time bound up to additive input length. -/
theorem all_widths (K S : ℕ) (T : ℕ → ℕ)
    (fast : BoundedTask (fun i : {p : MultiplicationInput // K ≤ p.width} => T i.val.width)
      (fun i => S*i.val.width) (fun i => send i.val.operands)
      (fun i => send (Lea.answer i.val.operands))) :
    MultiplicationTask (fun n => n + T n) (S+20) (fun i => Lea.answer i.operands) := by
  let s (i : MultiplicationInput) := (S+8)*i.width
  have long := fast.on fun i : longS K =>
    (⟨i.val, Nat.le_of_not_gt (of_decide_eq_false i.property)⟩ :
      {p : MultiplicationInput // K ≤ p.width})
  have run := BoundedTask.control (t := fun i : MultiplicationInput => T i.width) (s := s)
    (src := fun i : MultiplicationInput => send i.operands)
    (dst := fun i : MultiplicationInput => send (Lea.answer i.operands)) (fun i : MultiplicationInput => tags K i)
    (long.mono (fun _ => le_rfl) (fun _ => Nat.mul_le_mul_right _ (by exact Nat.le_add_right S 8)))
    ((short_task K).mono (fun _ => Nat.zero_le _)
      (fun _ => Nat.mul_le_mul_right _ (Nat.le_add_left 8 S)))
  apply ((BoundedTask.of_time (tag_task K)).compose run).mono (fun _ => le_rfl)
  intro i
  rw [input_count]
  have h : 1 ≤ i.width := i.property
  dsimp only [s]
  simp only [Nat.add_mul]
  omega

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
