import OAI.Computability.VPVNP.CompressorBlockInitialPackets
import OAI.Computability.VPVNP.CompressorBlockProgram

/-! # Catalog indices and checked packets for the actual initial script -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialScriptPackets

open BurstRAM BlockPlanner DescriptorSpace SourceOnline BlockInitialPackets

variable {w : ℕ}

/-- The script's initial ordinals precede its repeated block. -/
def indices (A : Script) := List.ofFn (fun i : Fin A.initial.length ↦ i.castAdd A.block.length)

theorem visits (A : Script) : (indices A).map A.visit = A.initial := by
  rw [indices,List.map_ofFn]
  change List.ofFn (fun i : Fin A.initial.length ↦ A.visit (i.castAdd A.block.length)) = _
  simp only [A.initial_visit]
  exact List.ofFn_get _

/-- The runtime allocation only changes the directory bounds and the catalog
arity. The four workers use the compiled scalar and array dimensions. -/
theorem actual_order {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} (B : S.Templates)
    (base positions blocks : ℕ) : (BlockProgram.script B).initial =
      order (BlockProgram.layout B base positions blocks) (S.degreeExponent 0) := by rfl

/-- One finite bound covers all planner code and all four source workers. -/
def budget (A : Script) (L : Layout) (a : ℕ) :=
  ∑ i : Fin A.size, max ((A.plan.recipes i).2.code.length+1+2*Schedule.Online.N A.size A.size+5)
    (clock L a+3+4*((A.catalog i).params+1)+2*Schedule.Online.N A.size A.size+5)

theorem budget_bounds (A : Script) (L : Layout) (a : ℕ) (i : Fin A.size) :
    (A.plan.recipes i).2.code.length+1+2*Schedule.Online.N A.size A.size+5 ≤ budget A L a ∧
    clock L a+3+4*((A.catalog i).params+1)+2*Schedule.Online.N A.size A.size+5 ≤ budget A L a := by
  let cost := fun j : Fin A.size ↦ max ((A.plan.recipes j).2.code.length+1+2*Schedule.Online.N A.size A.size+5)
    (clock L a+3+4*((A.catalog j).params+1)+2*Schedule.Online.N A.size A.size+5)
  have bound : cost i ≤ budget A L a :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (cost j)) (Finset.mem_univ i)
  exact ⟨(le_max_left ..).trans bound,(le_max_right ..).trans bound⟩

theorem budget_fixed {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} (B : S.Templates)
    (base positions blocks a : ℕ) :
    budget (BlockProgram.script B) (BlockProgram.layout B base positions blocks) a =
      budget (BlockProgram.script B) (BlockProgram.layout B 0 0 0) a := rfl

/-- A checked initial packet whose catalog phase, public operands, entry memory, fuel, and
choices agree with its attached header visit. -/
def Attached (A : Script) (L : Layout) (pub : Fin 5 → Word w) (s : Word w) (cap : ℕ)
    (p : SourceWalk.Packet (SourceOnline.Visit A w) w) : Prop :=
  SourceOnline.Checked A L cap p ∧
    p.stage = HeaderPacket.attach A p.stage.phase pub s p.input p.stage.fuel p.stage.choices

private theorem labelWalk (A : Script) (L : Layout) (a cap : ℕ) (pub : Fin 5 → Word w) (s : Word w)
    (is : List (Fin A.size)) (m : Memory w) (rs : List (Report w))
    (walk : SourceWalk (BlockInitialPackets.Source L a pub s) (is.map A.visit) m rs)
    (recipe : ∀ i ∈ is, (A.plan.recipes i).2.code.length+1+2*Schedule.Online.N A.size A.size+5 ≤ cap)
    (data : ∀ i ∈ is, clock L a+3+4*((A.catalog i).params+1)+2*Schedule.Online.N A.size A.size+5 ≤ cap) :
    ∃ ps : List (SourceWalk.Packet (SourceOnline.Visit A w) w),
      SourceWalk.Chronological SourceOnline.Visit.Runs m ps ∧ ps.map (fun p ↦ p.stage.phase) = is ∧
      ps.flatMap SourceWalk.Packet.reports = rs ∧ ∀ p ∈ ps, Attached A L pub s cap p := by
  induction is generalizing m rs with
  | nil =>
    cases walk
    exact ⟨[],trivial,rfl,rfl,by simp⟩
  | cons i is ih =>
    cases walk with
    | @next _ _ _ head tail src rest =>
      obtain ⟨fuel,bits,hf,run⟩ := src
      let stage := HeaderPacket.attach A i pub s m fuel bits
      let p : SourceWalk.Packet (SourceOnline.Visit A w) w := ⟨stage,m,head⟩
      have smaller := data i List.mem_cons_self
      have check : Attached A L pub s cap p := ⟨HeaderPacket.attach_checked A i rfl run cap
        (recipe i List.mem_cons_self) (by omega),rfl⟩
      obtain ⟨ps,chron,ord,reports,checks⟩ := ih (after m (eventLog head)) tail rest
        (fun j hj ↦ recipe j (List.mem_cons_of_mem _ hj)) (fun j hj ↦ data j (List.mem_cons_of_mem _ hj))
      refine ⟨p::ps,⟨rfl,HeaderPacket.attach_runs A i rfl run,chron⟩,?_,?_,?_⟩
      · exact congrArg (i :: ·) ord
      · exact congrArg (head ++ ·) reports
      · intro q h
        rcases List.mem_cons.mp h with rfl|inTail
        · exact check
        · exact checks q inTail

/-- The four checked packets use the actual worker labels in the compiled
script and the computed public operands at each successive source memory. -/
theorem attach_initial (A : Script) (L : Layout) (a cap : ℕ) (pub : Fin 5 → Word w) (s : Word w)
    (m : Memory w) (rs : List (Report w)) (shape : A.initial = order L a)
    (walk : SourceWalk (BlockInitialPackets.Source L a pub s) (order L a) m rs)
    (recipe : ∀ i ∈ indices A, (A.plan.recipes i).2.code.length+1+2*Schedule.Online.N A.size A.size+5 ≤ cap)
    (data : ∀ i ∈ indices A, clock L a+3+4*((A.catalog i).params+1)+2*Schedule.Online.N A.size A.size+5 ≤ cap) :
    ∃ ps : List (SourceWalk.Packet (SourceOnline.Visit A w) w),
      SourceWalk.Chronological SourceOnline.Visit.Runs m ps ∧ ps.map (fun p ↦ p.stage.phase) = indices A ∧
      ps.flatMap SourceWalk.Packet.reports = rs ∧ ∀ p ∈ ps, Attached A L pub s cap p :=
  labelWalk A L a cap pub s _ m rs (by rw [visits,shape]; exact walk) recipe data

end CompressorRecords.InitialScriptPackets

end VPVNP
end Computability
end OAI
