import OAI.Computability.BorderVNP.PackedHistoryBootPaths

/-! # The adaptive history prefix inside the assembled signed evaluator

Split the real evaluation table after its guarded geometry reader, before the private
placement and directory passes. Every successful chronological path runs a history prefix
followed by a continuation on exactly the memory and register bank left by that prefix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Evaluator GeometryAdvice
open private seq_assoc from OAI.Computability.BorderVNP.RoutingISABlockAppend

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- All actual remaining signed instructions after the adaptive pack geometry is available. -/
def afterGeometry (placement groups arguments occurrences : Code) : Code :=
  .block [placement,Packing.Directory.ISA.program,groups,route,arguments,callOwnedCells,occurrences,
    DiagonalTallyRAM.complete,leadEntry]

private theorem evaluation_split (placement groups arguments occurrences : Code) {s m es t mt} :
    Runs pub mac (evaluate (.seq reconstruct placement) groups arguments occurrences) s m es t mt ↔
      Runs pub mac (.seq pinGeometry (afterGeometry placement groups arguments occurrences)) s m es t mt := by
  let tail := Code.block [Packing.Directory.ISA.program,groups,route,arguments,callOwnedCells,occurrences,
    DiagonalTallyRAM.complete,leadEntry]
  change Runs _ _ (.seq preparePins (.seq (.seq reconstruct placement) tail)) _ _ _ _ _ ↔
    Runs _ _ (.seq (.seq preparePins reconstruct) (.seq placement tail)) _ _ _ _ _
  have rewire {z mz gs} : Runs pub mac (.seq (.seq reconstruct placement) tail) z mz gs t mt ↔
      Runs pub mac (.seq reconstruct (.seq placement tail)) z mz gs t mt := seq_assoc.symm
  rw [← seq_assoc]
  simp only [Runs.seq_iff (a := preparePins),rewire]

/-- After the canonical nonzero evaluation tag, a physical startup run is characterized by
its actual dispatch events followed by a run of the selected body with the copied header. -/
theorem evaluation_startup_iff (f : BroadcastFrame) (body : Code) {s m pre z mz head ready saved es t mt}
    (start : Runs pub mac unitStartup s m pre z mz) (copy : Runs pub mac readBroadcast z mz head ready saved)
    (stable : f.Stable (readings ready)) (mode : (saved f.dst).val ≠ 0) :
    Runs pub mac (withStartup body) s m es t mt ↔
      ∃ gs, es = dispatchPrefix f saved pre head++gs ∧
        Runs pub mac body (Function.update ready 10 (saved f.dst)) saved gs t mt := by
  have select : selected f body saved = body := ite_eq_right mode
  have extend : ∃ E : Returns (selected f body saved) pub mac (Function.update ready 10 (saved f.dst)) saved ≃
      Returns (withStartup body) pub mac s m, ∀ v, (E v).val = (dispatchPrefix f saved pre head++v.val.1,v.val.2) :=
    ⟨startupReturnEquiv f body start copy stable,startupReturnEquiv_val f body start copy stable⟩
  rw [select] at extend
  obtain ⟨E,eq⟩ := extend
  constructor
  · intro h
    obtain ⟨v,hv⟩ := E.surjective ⟨(es,t,mt),h⟩
    have joined := (eq v).symm.trans (congrArg Subtype.val hv)
    obtain ⟨events,state⟩ := Prod.mk.inj joined
    refine ⟨v.val.1,events.symm,?_⟩
    obtain ⟨rfl,rfl⟩ := Prod.ext_iff.mp state; exact v.property
  · rintro ⟨gs,rfl,go⟩
    let v : Returns body pub mac (Function.update ready 10 (saved f.dst)) saved := ⟨(gs,t,mt),go⟩
    have run := (E v).property
    rw [eq v] at run; exact run

/-- Every true evaluator run in evaluation mode splits after the history reader. The
chronological trace is an exact concatenation; the remaining instructions receive the true
prefix's register bank and memory, including its physical row outputs. -/
theorem evaluation_geometry_iff (f : BroadcastFrame) (placement groups arguments occurrences : Code)
    {s m boot ready saved es t mt} (initial : Runs pub mac JointHeader.bootHeader s m boot ready saved)
    (stable : f.Stable (readings ready)) (mode : (saved f.dst).val ≠ 0) :
    Runs pub mac (assemble ExtendedFrame.install (.seq reconstruct placement) groups arguments occurrences) s m es t mt ↔
      ∃ y : Returns (withStartup pinGeometry) pub mac s m, ∃ gs, es = y.val.1++gs ∧
        Runs pub mac (afterGeometry placement groups arguments occurrences) y.val.2.1 y.val.2.2 gs t mt := by
  obtain ⟨z,mz,pre,head,_,start,copy⟩ := Runs.seq_iff.mp initial
  rw [← withStartup_evaluate,evaluation_startup_iff f _ start copy stable mode]
  constructor
  · rintro ⟨bs,rfl,go⟩
    obtain ⟨a,ma,fs,gs,rfl,front,last⟩ := Runs.seq_iff.mp ((evaluation_split placement groups arguments occurrences).mp go)
    have prefixRun := (evaluation_startup_iff f pinGeometry start copy stable mode).mpr ⟨fs,rfl,front⟩
    exact ⟨⟨(_,a,ma),prefixRun⟩,gs,(List.append_assoc ..).symm,last⟩
  · rintro ⟨y,gs,rfl,last⟩
    obtain ⟨fs,joined,first⟩ := (evaluation_startup_iff f pinGeometry start copy stable mode).mp y.property
    exact ⟨fs++gs,by rw [joined,List.append_assoc],(evaluation_split placement groups arguments occurrences).mpr (first.seq last)⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
