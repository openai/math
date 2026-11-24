import OAI.Computability.VPVNP.CompressorExecutionTrace
import OAI.Computability.VPVNP.CompressorSourceBankFrame

/-! # Low-memory frames for arbitrary finite native prefixes

A partial successful execution may stop inside a pass with no accepting
extension. The frame invariant covers such prefixes directly. Once a
complete choice segment has been consumed, the same test continues in
its actual successor state and memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BranchSegments

open BurstRAM SourceBankFrame Compression

variable {w cap lo : ℕ} {Q : Type*} {P : BurstRAM.Program w Q} {st : Option (Word w)} {m : Memory w}

namespace Cut

/-- Low-memory stability of each branch and each successful prefix of the branch cut, including
prefixes ending before branch selection completes. -/
structure PrefixFrame {I : Type*} (c : Cut P cap st m I) (lo : ℕ) : Prop where
  parts : ∀ i, Stable lo m (c.part i).logs
  «prefix» : ∀ bs rs, runSegment P cap st m bs = some rs →
    Stable lo m rs ∨ ∃ i tail, bs = (c.part i).bits ++ tail

private theorem partial_empty (n : ℕ) {logs rs : List (Report w)} {bs : List (List Bool)}
    (empty : runSegment P cap st m (List.replicate n []) = some logs) (frame : Stable lo m logs)
    (run : runSegment P cap st m bs = some rs) : Stable lo m rs ∨ ∃ tail, bs = List.replicate n [] ++ tail := by
  induction n generalizing st m logs rs bs with
  | zero => exact Or.inr ⟨bs,rfl⟩
  | succ n ih =>
    simp only [List.replicate_succ] at empty ⊢
    cases st with
    | none => contradiction
    | some a =>
      cases bs with
      | nil =>
        cases Option.some.inj run
        exact Or.inl trivial
      | cons b bs =>
        rw [runSegment] at empty run
        cases he : execute P cap (P.start a) m [] with
        | none => simp [he] at empty
        | some x =>
          cases hb : execute P cap (P.start a) m b with
          | none => simp [hb] at run
          | some y =>
            obtain ⟨rfl,rfl⟩ := execute_empty_forces he hb
            simp only [he,Option.map_eq_some_iff] at empty run
            obtain ⟨more,hm,rfl⟩ := empty
            obtain ⟨rest,hr,rfl⟩ := run
            rcases ih hm frame.2 hr with f | ⟨tail,ht⟩
            · exact Or.inl ⟨frame.1,f⟩
            · exact Or.inr ⟨tail,congrArg (List.cons []) ht⟩

/-- An arbitrary finite run either preserves all reserved low cells or
has already consumed the entire forced interval. -/
theorem deterministic_prefix (s : Segment P cap st m) (n : ℕ) (quiet : s.bits = List.replicate n [])
    (frame : Stable lo m s.logs) {bs rs} (run : runSegment P cap st m bs = some rs) :
    Stable lo m rs ∨ ∃ tail, bs = s.bits ++ tail := by
  rw [quiet]
  exact partial_empty n (quiet ▸ s.run) frame run

theorem PrefixFrame.deterministic (s : Segment P cap st m) (n : ℕ) (quiet : s.bits = List.replicate n [])
    (stable : Stable lo m s.logs) : (Cut.deterministic s n quiet).PrefixFrame lo := by
  refine ⟨fun _ => stable,fun bs rs run => ?_⟩
  exact (deterministic_prefix s n quiet stable run).imp id fun ⟨t,ht⟩ => ⟨(),t,ht⟩

variable {I : Type*} {c : Cut P cap st m I}

theorem PrefixFrame.bind (h : c.PrefixFrame lo) {J : I → Type*}
    {k : ∀ i, Cut P cap (c.part i).state (c.part i).memory (J i)}
    (hk : ∀ i, (k i).PrefixFrame lo) : (c.bind k).PrefixFrame lo := by
  refine ⟨fun i => (h.parts i.1).append ((hk i.1).parts i.2),fun bs rs run => ?_⟩
  rcases h.prefix bs rs run with stable | ⟨i,tail,rfl⟩
  · exact Or.inl stable
  · rw [PrimedSchedule.runSegment_append,(c.part i).run] at run
    change (runSegment P cap (c.part i).state (c.part i).memory tail).map _ = some rs at run
    obtain ⟨more,rest,rfl⟩ := Option.map_eq_some_iff.mp run
    rcases (hk i).prefix tail more rest with f | ⟨j,t,ht⟩
    · exact Or.inl ((h.parts i).append f)
    · exact Or.inr ⟨⟨i,j⟩,t,by simp only [ht,Cut.bind,Segment.append,List.append_assoc]⟩

theorem PrefixFrame.before (s : Segment P cap st m) (n : ℕ) (quiet : s.bits = List.replicate n [])
    (stable : Stable lo m s.logs) {k : Cut P cap s.state s.memory I} (hk : k.PrefixFrame lo) :
    (Cut.before s n quiet k).PrefixFrame lo := by
  have joined := (PrefixFrame.deterministic s n quiet stable).bind (fun _ : Unit => hk)
  refine ⟨fun i => joined.parts ⟨(),i⟩,fun bs rs run => ?_⟩
  exact (joined.prefix bs rs run).imp id fun ⟨z,tail,ht⟩ => ⟨z.2,tail,ht⟩

theorem PrefixFrame.afterChoice (h : c.PrefixFrame lo) (k : ∀ i, Segment P cap (c.part i).state (c.part i).memory)
    (n : I → ℕ) (quiet : ∀ i, (k i).bits = List.replicate (n i) [])
    (stable : ∀ i, Stable lo (c.part i).memory (k i).logs) : (c.afterChoice k n quiet).PrefixFrame lo := by
  have joined := h.bind fun i => PrefixFrame.deterministic (k i) (n i) (quiet i) (stable i)
  refine ⟨fun i => joined.parts ⟨i,()⟩,fun bs rs run => ?_⟩
  exact (joined.prefix bs rs run).imp id fun ⟨z,tail,ht⟩ => ⟨z.1,tail,ht⟩

end Cut

namespace ExecutionTrace

variable {R : Type*} [CommSemiring R] {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X}

/-- The local frame proof required at each actual pass and terminal close. -/
def Framed {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X} {st m}
    (t : ExecutionTrace P cap E st m) (lo : ℕ) : Prop :=
  match t with
  | .done s _ _ _ => Stable lo m s.logs
  | .more c next => c.PrefixFrame lo ∧ ∀ i, Framed (next i) lo

theorem Framed.cut {t : ExecutionTrace P cap E st m} (h : Framed t lo) : t.cut.PrefixFrame lo := by
  induction t with
  | done s n quiet halt => exact Cut.PrefixFrame.deterministic s n quiet h
  | more c next ih => exact h.1.bind fun i => ih i (h.2 i)

/-- Every finite successful prefix of the whole native execution preserves
the low bank, including prefixes on branches that cannot reach a leaf. -/
theorem Framed.stable {t : ExecutionTrace P cap E st m} (h : Framed t lo) {bs rs}
    (run : runSegment P cap st m bs = some rs) : Stable lo m rs := by
  rcases h.cut.prefix bs rs run with frame | ⟨z,tail,rfl⟩
  · exact frame
  · rw [PrimedSchedule.runSegment_append,(t.cut.part z).run] at run
    change (runSegment P cap (t.cut.part z).state (t.cut.part z).memory tail).map _ = some rs at run
    rw [t.stopped z] at run
    cases tail with
    | nil =>
      change some ((t.cut.part z).logs ++ []) = some rs at run
      rw [List.append_nil] at run
      exact Option.some.inj run ▸ h.cut.parts z
    | cons b tail => contradiction

end ExecutionTrace
end CompressorRecords.BranchSegments

end VPVNP
end Computability
end OAI
