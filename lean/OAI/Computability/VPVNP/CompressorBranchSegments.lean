import OAI.Computability.VPVNP.CompressorOnlineRowInverse
import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.LiveDeterministicPaths

/-! # Factoring a native compression pass at its term-selection row

Every surrounding descriptor scan has a verified run on empty choice tapes.
An accepting stream must follow those scans exactly. The selector row is
inverted on the actual intervening memory, and its source-worker inverse
recovers the selected term. Concatenation preserves the remaining native
calls, their reports and the memory used by the next compression level.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BranchSegments
open BurstRAM

variable {w : ℕ} {Q : Type*} {P : BurstRAM.Program w Q} {cap : ℕ}
variable {st : Option (Word w)} {m : Memory w}

/-- A finite initial portion of a run of the fixed table. -/
structure Segment (P : BurstRAM.Program w Q) (cap : ℕ) (st : Option (Word w)) (m : Memory w) where
  /-- One choice tape for each successive native call in the segment. -/
  bits : List (List Bool)
  /-- Reports returned by those calls, in execution order. -/
  logs : List (Report w)
  run : runSegment P cap st m bits = some logs

namespace Segment

variable (s : Segment P cap st m)

/-- The cursor returned by the segment, computed from its initial state and reports. -/
def state := endState st s.logs
/-- External memory obtained by applying all events in the segment to its initial memory. -/
def memory := after m (eventLog s.logs)

/-- Concatenate consecutive runs, feeding the first segment's ending cursor and memory to the
second. -/
def append (t : Segment P cap s.state s.memory) : Segment P cap st m where
  bits := s.bits ++ t.bits
  logs := s.logs ++ t.logs
  run := by
    rw [PrimedSchedule.runSegment_append,s.run]
    change (runSegment P cap s.state s.memory t.bits).map _ = _
    rw [t.run]; rfl

@[simp] theorem append_state (t : Segment P cap s.state s.memory) : (s.append t).state = t.state :=
  endState_append _ _ _

@[simp] theorem append_memory (t : Segment P cap s.state s.memory) : (s.append t).memory = t.memory :=
  SourceWalk.after_append _ _ _

/-- The zero-call segment with empty tape and report lists. -/
def empty (P : BurstRAM.Program w Q) (cap : ℕ) (st : Option (Word w)) (m : Memory w) : Segment P cap st m :=
  ⟨[],[],rfl⟩

/-- Once the choice prefix is known, the reports and continuation memory
are uniquely determined by native execution. -/
theorem remainder {tail : List (List Bool)} {logs : List (Report w)}
    (run : runSegment P cap st m (s.bits ++ tail) = some logs) (halt : endState st logs = none) :
    ∃ more, logs = s.logs ++ more ∧ runSegment P cap s.state s.memory tail = some more ∧
      endState s.state more = none := by
  rw [PrimedSchedule.runSegment_append,s.run] at run
  change (runSegment P cap s.state s.memory tail).map _ = some logs at run
  obtain ⟨more,hr,rfl⟩ := Option.map_eq_some_iff.mp run
  exact ⟨more,rfl,hr,(endState_append st s.logs more).symm.trans halt⟩

end Segment

/-- Distinct mathematical choices have incompatible prefixes on the physical
tape, and every accepting run starts with one of these prefixes. -/
structure Cut (P : BurstRAM.Program w Q) (cap : ℕ) (st : Option (Word w)) (m : Memory w) (I : Type*) where
  /-- The initial native segment associated with each possible branch index. -/
  part : I → Segment P cap st m
  separate : ∀ i j a b, (part i).bits ++ a = (part j).bits ++ b → i = j
  cover : ∀ bs rs, runSegment P cap st m bs = some rs → endState st rs = none →
    ∃ i tail, bs = (part i).bits ++ tail

namespace Cut

variable {I : Type*} (c : Cut P cap st m I)

/-- Restore the precise logs and native execution of the suffix. -/
theorem split {bs rs} (run : runSegment P cap st m bs = some rs) (halt : endState st rs = none) :
    ∃ i tail more, bs = (c.part i).bits ++ tail ∧ rs = (c.part i).logs ++ more ∧
      runSegment P cap (c.part i).state (c.part i).memory tail = some more ∧
      endState (c.part i).state more = none := by
  obtain ⟨i,tail,rfl⟩ := c.cover bs rs run halt
  obtain ⟨more,hl,hr,hh⟩ := (c.part i).remainder run halt
  exact ⟨i,tail,more,rfl,hl,hr,hh⟩

/-- The next branch tree is chosen in the actual memory left by this one. -/
def bind {J : I → Type*} (k : ∀ i, Cut P cap (c.part i).state (c.part i).memory (J i)) :
    Cut P cap st m (Sigma J) where
  part z := (c.part z.1).append ((k z.1).part z.2)
  separate := by
    rintro ⟨i,x⟩ ⟨j,y⟩ a b h
    change ((c.part i).bits ++ ((k i).part x).bits) ++ a = ((c.part j).bits ++ ((k j).part y).bits) ++ b at h
    simp only [List.append_assoc] at h
    cases c.separate i j _ _ h
    cases (k i).separate x y _ _ (List.append_cancel_left h)
    rfl
  cover := by
    intro bs rs run halt
    obtain ⟨i,tail,more,hb,_,hr,hh⟩ := c.split run halt
    obtain ⟨j,rest,hj⟩ := (k i).cover tail more hr hh
    exact ⟨⟨i,j⟩,rest,by simp only [hb,hj,Segment.append,List.append_assoc]⟩

/-- A run on empty choices is forced call by call, even if a later term
selection has no valid branches. -/
def deterministic (s : Segment P cap st m) (n : ℕ) (hb : s.bits = List.replicate n []) :
    Cut P cap st m Unit where
  part _ := s
  separate _ _ _ _ _ := Subsingleton.elim _ _
  cover bs rs run halt := by
    obtain ⟨rest,_,e,_,_⟩ := LiveProgram.split_empty_segment (hb ▸ s.run) run halt
    exact ⟨(),rest,hb.symm ▸ e⟩

/-- Prepend a forced part without adding an index to the selected terms. -/
def before (s : Segment P cap st m) (n : ℕ) (emptyBits : s.bits = List.replicate n [])
    (k : Cut P cap s.state s.memory I) : Cut P cap st m I where
  part i := s.append (k.part i)
  separate i j a b h := by
    change (s.bits ++ (k.part i).bits) ++ a = (s.bits ++ (k.part j).bits) ++ b at h
    simp only [List.append_assoc] at h
    exact k.separate i j _ _ (List.append_cancel_left h)
  cover bs rs run halt := by
    obtain ⟨_,tail,more,hb,_,hr,hh⟩ := (deterministic s n emptyBits).split run halt
    obtain ⟨i,rest,e⟩ := k.cover tail more hr hh
    exact ⟨i,rest,by simpa only [Segment.append,deterministic,List.append_assoc,e] using hb⟩

/-- Attach the forced output-directory scans for each selected term. -/
def afterChoice (k : ∀ i, Segment P cap (c.part i).state (c.part i).memory)
    (n : I → ℕ) (emptyBits : ∀ i, (k i).bits = List.replicate (n i) []) : Cut P cap st m I where
  part i := (c.part i).append (k i)
  separate i j a b h := by
    change ((c.part i).bits ++ (k i).bits) ++ a = ((c.part j).bits ++ (k j).bits) ++ b at h
    simp only [List.append_assoc] at h
    exact c.separate i j _ _ h
  cover bs rs run halt := by
    obtain ⟨i,tail,more,hb,_,hr,hh⟩ := c.split run halt
    obtain ⟨_,rest,e⟩ := (deterministic (k i) (n i) (emptyBits i)).cover tail more hr hh
    exact ⟨i,rest,by simpa only [Segment.append,deterministic,List.append_assoc,e] using hb⟩

/-- Physical path bijection, retaining a cap or observation on the entire
concatenated report sequence. -/
noncomputable def pathsEquiv (allow : List (Report w) → Prop) :
    (Σ i, LiveProgram.PathsFrom P cap (c.part i).state (c.part i).memory
      (fun rs => allow ((c.part i).logs ++ rs))) ≃ LiveProgram.PathsFrom P cap st m allow := by
  let join : (Σ i, LiveProgram.PathsFrom P cap (c.part i).state (c.part i).memory
      (fun rs => allow ((c.part i).logs ++ rs))) → LiveProgram.PathsFrom P cap st m allow := fun z =>
    ⟨(c.part z.1).bits ++ z.2.val,by
      obtain ⟨rs,hr,hh,allowed⟩ := z.2.property
      let t : Segment P cap (c.part z.1).state (c.part z.1).memory := ⟨z.2.val,rs,hr⟩
      exact ⟨_,((c.part z.1).append t).run,((c.part z.1).append_state t).trans hh,allowed⟩⟩
  apply Equiv.ofBijective join
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have e := congrArg Subtype.val h
    change (c.part i).bits ++ x.val = (c.part j).bits ++ y.val at e
    cases c.separate i j _ _ e
    cases Subtype.ext (List.append_cancel_left e)
    rfl
  · rintro ⟨bs,rs,hr,hh,allowed⟩
    obtain ⟨i,rest,more,hb,rfl,run,halt⟩ := c.split hr hh
    exact ⟨⟨i,rest,more,run,halt,allowed⟩,Subtype.ext hb.symm⟩

end Cut
end CompressorRecords.BranchSegments

end VPVNP
end Computability
end OAI
