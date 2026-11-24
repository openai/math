import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Copying the input stacks of an arithmetic call

The fixed list of source and destination ports determines the control table.
Sources may repeat, so an advised word can initialize several ports in one call.
One empty scratch stack serves the entire sequence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.CallCopies

open RAMTape RAMTape.SuccessorFields

variable {K : Type}

/-- Each pair specifies a source and its destination. -/
def copyPlan (scratch : K) : List (K × K) → FiniteRoutine K
  | [] => .ret
  | p :: ps => (prependCopy p.1 p.2 scratch).followedBy (copyPlan scratch ps)

/-- Destinations are distinct, sources are read-only, and scratch is separate. -/
abbrev Valid (scratch : K) (pairs : List (K × K)) : Prop :=
  (pairs.map Prod.snd).Nodup ∧
  (∀ k ∈ pairs.map Prod.fst, k ∉ pairs.map Prod.snd) ∧
  scratch ∉ pairs.map Prod.fst ∧ scratch ∉ pairs.map Prod.snd

variable [DecidableEq K]

private def fill (pairs : List (K × K)) (source base : Stacks K) : Stacks K :=
  pairs.foldl (fun bank p => Function.update bank p.2 (source p.1)) base

/-- The destinations contain the corresponding original source values. -/
def copied (pairs : List (K × K)) (s : Stacks K) : Stacks K :=
  pairs.foldl (fun bank p => Function.update bank p.2 (s p.1)) s

private theorem fill_outside (pairs : List (K × K)) (source base : Stacks K) (k : K)
    (hk : k ∉ pairs.map Prod.snd) : fill pairs source base k = base k := by
  induction pairs generalizing base with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    exact (ih (Function.update base p.2 (source p.1)) hk.2).trans (Function.update_of_ne hk.1 ..)

theorem copied_outside (pairs : List (K × K)) (s : Stacks K) (k : K)
    (hk : k ∉ pairs.map Prod.snd) : copied pairs s k = s k :=
  fill_outside pairs s s k hk

private theorem fill_at (pairs : List (K × K)) (source base : Stacks K)
    (hn : (pairs.map Prod.snd).Nodup) {p : K × K} (hp : p ∈ pairs) :
    fill pairs source base p.2 = source p.1 := by
  induction pairs generalizing base with
  | nil => simp at hp
  | cons q ps ih =>
    obtain ⟨hq, hn'⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (fill_outside ps source _ p.2 hq).trans (Function.update_self ..)
    · exact ih _ hn' hp

theorem copied_at (pairs : List (K × K)) (s : Stacks K) (hn : (pairs.map Prod.snd).Nodup)
    {p : K × K} (hp : p ∈ pairs) : copied pairs s p.2 = s p.1 :=
  fill_at pairs s s hn hp

private theorem run_from (scratch : K) (pairs : List (K × K)) (source base : Stacks K) (M : ℕ)
    (valid : Valid scratch pairs) (ht : base scratch = [])
    (reads : ∀ p ∈ pairs, base p.1 = source p.1) (empty : ∀ p ∈ pairs, base p.2 = [])
    (bound : ∀ p ∈ pairs, (source p.1).length ≤ M) :
    ∃ t ≤ pairs.length * (5*M+2) + 1, (copyPlan scratch pairs).Runs t base (fill pairs source base) := by
  induction pairs generalizing base with
  | nil => exact ⟨1, by simp, Routine.runs_ret base⟩
  | cons p ps ih =>
    obtain ⟨hn, hd, hs, ht'⟩ := valid
    obtain ⟨hfresh, hn'⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.mem_cons, not_or] at hs ht'
    have head := hd p.1 (List.mem_cons_self ..)
    simp only [List.map_cons, List.mem_cons, not_or] at head
    have member (q : K × K) (hq : q ∈ ps) := List.mem_cons_of_mem p hq
    have hvalid : Valid scratch ps := ⟨hn', fun k hk hk' =>
      hd k (List.mem_cons_of_mem _ hk) (List.mem_cons_of_mem _ hk'), hs.2, ht'.2⟩
    let mid := Function.update base p.2 (source p.1)
    have hread := reads p (List.mem_cons_self ..)
    have hempty := empty p (List.mem_cons_self ..)
    have first : (prependCopy p.1 p.2 scratch).Runs (5 * (source p.1).length + 2) base mid := by
      simpa only [hread, hempty, List.append_nil] using
        prependCopy_runs p.1 p.2 scratch head.1 (Ne.symm hs.1) (Ne.symm ht'.1) base ht
    obtain ⟨t, hb, tail⟩ := ih mid hvalid (by simpa [mid, ht'.1] using ht) (by
      intro q hq
      have hne : q.1 ≠ p.2 := fun e => hd q.1 (List.mem_map.mpr ⟨q, member q hq, rfl⟩)
        (List.mem_cons.mpr (.inl e))
      simpa [mid, hne] using reads q (member q hq)) (by
      intro q hq
      have hne : q.2 ≠ p.2 := fun e => hfresh (List.mem_map.mpr ⟨q, hq, e⟩)
      simpa [mid, hne] using empty q (member q hq)) (fun q hq => bound q (member q hq))
    refine ⟨_, ?_, first.followedBy tail⟩
    have hhead := bound p (List.mem_cons_self ..)
    calc
      5 * (source p.1).length + 2 + t ≤ (5*M+2) + (ps.length * (5*M+2)+1) :=
        Nat.add_le_add (by omega) hb
      _ = (p :: ps).length * (5*M+2) + 1 := by rw [List.length_cons, Nat.add_mul]; ring

/-- Each destination starts empty and receives one source copy. Each source
bit costs five instructions, each copy tests for the end twice, and the
final return costs one instruction. -/
theorem copyPlan_runs (scratch : K) (pairs : List (K × K)) (s : Stacks K) (M : ℕ)
    (valid : Valid scratch pairs) (ht : s scratch = [])
    (empty : ∀ p ∈ pairs, s p.2 = []) (bound : ∀ p ∈ pairs, (s p.1).length ≤ M) :
    ∃ t ≤ pairs.length * (5*M+2) + 1, (copyPlan scratch pairs).Runs t s (copied pairs s) :=
  run_from scratch pairs s s M valid ht (fun _ _ => rfl) empty bound

end SliceArithmetic.CallCopies

end VPVNP
end Computability
end OAI
