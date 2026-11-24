import OAI.Computability.VPVNP.CompressorSourceGroups

/-!
# Packet groups from chronological source walks

The ordinal of a source packet is its position in the window, even when
two workers or two visits coincide. Each packet retains the source
segment's input memory, reports and tapes. An invariant can be carried
along the original report sequence to justify its launch operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM

namespace SourceWalk

variable {w : ℕ} {J : Type*} {src : J → Memory w → List (Report w) → Prop}
variable {js : List J} {m : Memory w} {rs : List (Report w)}

/-- Carry a memory invariant into the input of every source segment and
through the complete report log. -/
theorem with_invariant (walk : SourceWalk src js m rs) {I : Memory w → Prop} (start : I m)
    (step : ∀ j mem logs, src j mem logs → I mem → I (after mem (eventLog logs))) :
    SourceWalk (fun j mem logs ↦ src j mem logs ∧ I mem) js m rs ∧ I (after m (eventLog rs)) := by
  induction walk with
  | done => exact ⟨.done _, start⟩
  | @next j js m xs ys head _ ih =>
    obtain ⟨tail,finish⟩ := ih (step _ _ _ head start)
    exact ⟨.next ⟨head,start⟩ tail, by rwa [after_append]⟩

/-- An actual walk that writes only outside a region keeps the reference
memory's operands there at every packet start, and in the final memory. -/
theorem with_agreement (walk : SourceWalk src js m rs) (region : ℕ → Prop) (reference : Memory w)
    (start : SourceTransport.Agree region reference m)
    (writes : SourceTransport.Writes (fun x ↦ ¬ region x) (eventLog rs)) :
    SourceWalk (fun j mem logs ↦ src j mem logs ∧ SourceTransport.Agree region reference mem) js m rs ∧
      SourceTransport.Agree region reference (after m (eventLog rs)) := by
  induction walk with
  | done => exact ⟨.done _, start⟩
  | @next j js m xs ys head _ ih =>
    rw [eventLog,List.flatMap_append] at writes
    have first : SourceTransport.Writes (fun x ↦ ¬ region x) (eventLog xs) :=
      fun a v h ↦ writes a v (List.mem_append_left _ h)
    have rest : SourceTransport.Writes (fun x ↦ ¬ region x) (eventLog ys) :=
      fun a v h ↦ writes a v (List.mem_append_right _ h)
    have next : SourceTransport.Agree region reference (after m (eventLog xs)) :=
      fun i hi ↦ (start i hi).trans (SourceTransport.after_outside m first (not_not_intro hi)).symm
    obtain ⟨tail,finish⟩ := ih next rest
    exact ⟨.next ⟨head,start⟩ tail, by rwa [after_append]⟩

end SourceWalk

namespace SourceOnline.Group

open BlockPlanner DescriptorSpace

/-- Assemble a complete window from its actual runs. The certificate is
indexed by the label occurrence, so it can use that occurrence's physical
calendar ordinal directly. -/
theorem of_window_walk {J : Type*} {w : ℕ} {A : Script} {L : Layout} {base : Word w} {cap ordinal total : ℕ}
    {src : J → Memory w → List (Report w) → Prop} {stages : List J}
    (labels : Fin stages.length → Visit A w)
    {m : Memory w} {rs : List (Report w)} (walk : SourceWalk src stages m rs)
    (cert : ∀ i mem logs, src stages[i.val] mem logs →
      (labels i).Runs mem logs ∧ Checked A L cap ⟨labels i,mem,logs⟩ ∧
      Prepared A L base (ordinal+i.val) total ⟨labels i,mem,logs⟩) :
    ∃ ps : List (Packet A w), ps.map SourceWalk.Packet.stage = List.ofFn labels ∧
      ps.flatMap SourceWalk.Packet.reports = rs ∧ Group A L base cap ordinal total m ps := by
  induction walk generalizing ordinal with
  | done =>
    exact ⟨[],List.ofFn_zero.symm,rfl,nil⟩
  | @next j js m xs ys head _ ih =>
    rw [@List.ofFn_succ _ js.length labels]
    let first : Packet A w := ⟨labels 0,m,xs⟩
    obtain ⟨run,check,prepare⟩ := cert 0 m xs head
    have firstGroup : Group A L base cap ordinal total m [first] :=
      singleton first rfl run check (by simpa only [Fin.val_zero,Nat.add_zero] using prepare)
    have later (i : Fin js.length) mem logs (hs : src js[i.val] mem logs) :
        (labels i.succ).Runs mem logs ∧ Checked A L cap ⟨labels i.succ,mem,logs⟩ ∧
        Prepared A L base ((ordinal+1)+i.val) total ⟨labels i.succ,mem,logs⟩ := by
      rw [show (ordinal+1)+i.val = ordinal+i.succ.val by simp only [Fin.val_succ]; omega]
      exact cert i.succ mem logs hs
    obtain ⟨ps,stages,reports,group⟩ := ih (fun i ↦ labels i.succ) later
    refine ⟨first::ps, congrArg (labels 0 :: ·) stages, congrArg (xs ++ ·) reports, firstGroup.append ?_⟩
    simpa only [post,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil,first] using group

end SourceOnline.Group
end CompressorRecords

end VPVNP
end Computability
end OAI
