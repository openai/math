import OAI.Computability.VPVNP.LiveProgramPairAuxiliary
import OAI.Computability.VPVNP.LiveProgramPairDeterministic
import OAI.Computability.VPVNP.LiveAuxiliaryGuardedCopy

/-! # Initializing the seven sparse auxiliary header descriptors in the linked group -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM LiveStageLink
open LiveAuxiliaryHeaders LiveHeaderCopyDispatch
open scoped Fin.CommRing

variable {G : Group} {i : Fin (2^(sizes G).h)} {m : Memory G.w}
  {hdr : Header (pairLengths G i) → Bool} {hist : List (Word G.w)}

/-- The actual initializer has one choice-free path and passes the descriptor
and source arrays intact to the next tag. Only its descriptor words and the
linker's tag are modified. -/
theorem initialized (hlen : hist.length = G.constants.grammarLabels.eval G.g)
    (areas : Areas (desc G) (shadow G) (pairLengths G i) hist.length (source G))
    (inputs : InputArrays (pairLengths G i) hdr hist (source G) m)
    (td : ∀ j f, (address (desc G) j f).val ≠ G.addr.val)
    (ts : ∀ j, (sourceAddress (pairLengths G i) hist.length (source G) j).val ≠ G.addr.val)
    (clock : 82 ≤ G.clockAt Stage.auxiliaryInit) (tag : G.tagged Stage.auxiliaryInit m) :
    ∃ A : Indexed G Stage.auxiliaryInit m Unit,
      Prepared (desc G) (shadow G).val (pairLengths G i) hdr hist (source G) (A.memory ()) ∧
      (∀ a, a ≠ G.addr.val → (a < (desc G).val ∨ (desc G).val+21 ≤ a) → A.memory () a = m a) ∧
      (A.logs ()).length = 1 ∧ ∀ r ∈ A.logs (), r.probes = 25 := by
  let L := pairLengths G i
  let N := hist.length
  let src := source G
  let table := desc G
  let sh := shadow G
  have hleft : m (src 0).val = (L.leftCut : Word G.w) := by simpa [cutLength] using inputs.lengths 0
  have hright : m (src 0+2).val = (L.rightCut : Word G.w) := by simpa [cutLength] using inputs.lengths 2
  obtain ⟨es,hr,descOK,outside,hl,hp,_⟩ :=
    LiveAuxiliaryDescriptorInit.init_native L N sh table (src 0) src 0 m areas.tableFit hleft hright
  let rep : Report G.w := ⟨es,none⟩
  let f := G.clockAt Stage.auxiliaryInit
  have hcall : execute (Pieces.component G.components Stage.auxiliaryInit G.g G.lit) f
      ((Pieces.component G.components Stage.auxiliaryInit G.g G.lit).start 0) m [] = some rep := by
    change execute ((initTable.instantiate G.w
      (Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliary G.constants)).program) f
      (((initTable.instantiate G.w
      (Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliary G.constants)).program).start 0) m [] = _
    rw [init_data G i hist hlen]
    change execute ((LiveOneShot.oneShot (PrimedStackRAM.template LiveAuxiliaryDescriptorInit.ops 27)).instantiate G.w
      (initData L N sh table src)).program f ((LiveAuxiliaryDescriptorInit.program L N sh table (src 0) src).start 0) m [] = _
    rw [LiveOneShot.execute_oneShot]
    have hbig := execute_extend hr (f-79)
    have he : 79+(f-79) = f := by dsimp [f]; omega
    rw [he] at hbig
    exact congrArg (Option.map fun t : Report G.w => (⟨t.events,none⟩ : Report G.w)) hbig
  have run : runSegment (Pieces.component G.components Stage.auxiliaryInit G.g G.lit) f (some 0) m
      (List.replicate 1 []) = some [rep] := by simp [runSegment,hcall]
  have fit : ∀ r ∈ [rep], room G.nextStage G.addr Stage.auxiliaryInit f r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change (es ++ transferEvents G.addr Stage.auxiliaryCopy).length < f
    rw [List.length_append,hl]
    change 78+3 < _
    dsimp [f]; omega
  let A := deterministicIndexed tag run (show endState (some 0) [rep] = none from rfl) fit
    (PreservesTagOnReturns.singleton_accept G.addr m rep rfl)
  have hrep : ordinaryReports (A.traces ()) = [rep] := deterministic_reports ..
  have hm : A.memory () = writeMemory (after m es) G.addr (tagWord G.w Stage.auxiliaryCopy) := by
    change transferMemory G.addr _ (after m (eventLog (ordinaryReports (A.traces ())))) = _
    rw [hrep]
    change writeMemory (after m (es ++ [])) G.addr (tagWord G.w Stage.auxiliaryCopy) = _
    rw [List.append_nil]
  have pre : Prepared table sh.val L hdr hist src (after m es) := by
    refine ⟨descOK,fun j => ?_⟩
    rw [outside _ (areas.sourcesTable j)]
    exact inputs.read j
  refine ⟨A,?_,?_,?_,?_⟩
  · rw [hm]
    constructor
    · exact ⟨fun j => by simpa only [writeMemory,ite_eq_right (td j 0)] using pre.descriptors.ends j,
        fun j => by simpa only [writeMemory,ite_eq_right (td j 1)] using pre.descriptors.sources j,
        fun j => by simpa only [writeMemory,ite_eq_right (td j 2)] using pre.descriptors.targets j⟩
    · intro j; simpa only [writeMemory,ite_eq_right (ts j)] using pre.sources j
  · intro a ha hd; rw [hm,writeMemory,ite_eq_right ha]; exact outside _ hd
  · simp [Indexed.logs,hrep]
  · intro r hr
    rw [Indexed.logs,hrep,List.map_singleton,List.mem_singleton] at hr
    rw [hr,linkedReport_probes]
    change countProbes es + 1 + 1 = 25
    omega

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
