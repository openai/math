import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveStreams

/-! # Effective alignment of flat binary table addresses

A finite unary divisor is compiled from the slot count. A fixed segmentation
program splits the resulting equal-width streams before their bits are zipped
into columns. All arities share a single register bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterAlign
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelSelectorAlign Filter
open EffectiveTask (Runs)

open private slotRulers from OAI.Computability.NearSquareRoot.ScheduleRegisterAlign

theorem generate_flat_streams : ∀ᶠ R in atTop, EffectiveTask.Family R
    (fun n (xs : List (Column n)) => xs.length)
    (fun n xs => send (flatBits n xs)) (fun n xs => send (bitStreams n xs)) := by
  let rulerTask := RegisterSelect.easy_eventually (Code.Easy.ruler (Code.Easy.identity (X := List Bool)))
  let segTask := RegisterSelect.easy_eventually (Piecework.easy (X := Bool)).fstCompose
  let dupTask := RegisterSelect.checked_eventually (Task.copy (send (X := List Bool)))
  filter_upwards [eventually_ge_atTop 4,rulerTask,segTask,dupTask] with R hR hr hs hd
  obtain ⟨u,wu,ru⟩ := hr
  obtain ⟨s,ws,rs⟩ := hs
  obtain ⟨d,wd,rd⟩ := hd
  obtain ⟨rep,er,spec⟩ := generate_repeat hR
  have e : Effective ltr (fun n : ℕ => rep (n+1)) := er.comp Computable.succ
  let count (n : ℕ) := (u.join (RegisterDivide.command n)).join (rep (n+1))
  have ec : Effective ltr count := ((effective_const ltr u).join effective_divide).join e
  refine ⟨fun n => (d.join (KernelEffectiveFamily.leftCmd (count n))).join s,
    ((effective_const _ _).join (KernelEffectiveFamily.effective_left ec)).join (effective_const _ _),?_⟩
  intro n
  refine ⟨⟨⟨wd,KernelEffectiveFamily.within_left (by omega) ⟨⟨wu,RegisterDivide.within (by omega) n⟩,
    (spec (n+1)).1⟩⟩,ws⟩,?_⟩
  let src := flatBits n
  let W (xs : List (Column n)) := tally xs.length
  have extract := (show Runs u size send (fun x : List Bool => send (ruler x)) from ru).on src
  have width := (run_divide n).on (fun xs : List (Column n) => xs.length)
  have fit (xs : List (Column n)) : send (ruler (src xs)) = send (tally ((n+1)*xs.length)) := by
    rw [← recover_tally (ruler (src xs))]
    simp [src]
  have width' := (extract.conform (fun _ => rfl) (fun _ => rfl) fit).comp width
  have repeats := (show Runs (rep (n+1)) size send (fun t : Tally => send (List.replicate (n+1) t))
    from (spec (n+1)).2).on W
  have rulers := width'.comp repeats
  have dup := (show Runs d _ _ _ from rd).on src
  have joint := dup.comp (runLeft rulers (fun xs => send (src xs)))
  let packet (xs : List (Column n)) := (List.replicate (n+1) (W xs),src xs)
  have cut := (show Runs s _ _ _ from rs).on packet
  have same (xs : List (Column n)) : (Piecework.segment (packet xs).1 (packet xs).2).1 = bitStreams n xs := by
    dsimp only [packet,W,src,flatBits]
    rw [← slotRulers,Piecework.prescribed]
  have full := joint.comp (cut.conform (fun _ => rfl) (fun _ => rfl) (fun xs => congrArg send (same xs)))
  apply full.bound (20*(n+1)+20)
  intro xs
  have sizeRep (k : ℕ) : size (List.replicate k (W xs)) = k*(2*xs.length+2)+1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp [List.replicate_succ,size_cons,size_tally,W,ih,Nat.succ_mul] at *
      omega
  change size (src xs) + (size (src xs)+xs.length+size (W xs)) + size (packet xs) + 1 ≤
    (20*(n+1)+20)*(xs.length+1)
  rw [show size (packet xs) = size (List.replicate (n+1) (W xs))+size (src xs)+1 from rfl,
    sizeRep,columns_size 0,flat_length,size_tally]
  simp only [W,tally_length]
  ring_nf
  omega

/-- The arity is the sole generator parameter. For each arity the emitted
program aligns every width in time linear in its column count. -/
theorem generate : ∀ᶠ R in atTop, EffectiveTask.Family R
    (fun n (xs : List (Column n)) => xs.length)
    (fun n xs => send (flatBits n xs)) (fun _ xs => send xs) := by
  filter_upwards [generate_flat_streams,generate_streams] with R hf ha
  obtain ⟨f,ef,sf⟩ := hf
  obtain ⟨a,ea,sa⟩ := ha
  refine ⟨fun n => (f n).join (a n),ef.join ea,fun n => ⟨⟨(sf n).1,(sa n).1⟩,?_⟩⟩
  exact ((sf n).2.comp (sa n).2).bound 2 fun x => by change x.length+x.length+1 ≤ 2*(x.length+1); omega

end RegisterAlign

end NearSquareRoot
end Computability
end OAI
