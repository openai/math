import OAI.Computability.VPVNP.LiveProgramPairAuxiliary
import OAI.Computability.VPVNP.LiveProgramPairDeterministic
import OAI.Computability.VPVNP.LiveAuxiliaryGuardedCopy

/-! # The linked sparse-copy stage and the memory passed to the compressed pair -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM LiveStageLink
open LiveAuxiliaryHeaders

variable {G : Group} {i : Fin (2^(sizes G).h)} {m : Memory G.w}
  {hdr : Header (pairLengths G i) → Bool} {hist : List (Word G.w)}

theorem copied (areas : Areas (desc G) (shadow G) (pairLengths G i) hist.length (source G))
    (prepared : Prepared (desc G) (shadow G).val (pairLengths G i) hdr hist (source G) m)
    (fresh : ∀ a < span (pairLengths G i) hist.length, m ((shadow G).val+a) = 0)
    (tagBefore : G.addr.val < (shadow G).val)
    (clock : 71 ≤ G.clockAt Stage.auxiliaryCopy) (tag : G.tagged Stage.auxiliaryCopy m) :
    ∃ A : Indexed G Stage.auxiliaryCopy m Unit,
      (∀ a < span (pairLengths G i) hist.length, A.memory () ((shadow G).val+a) = headerMemory (pairLengths G i) hdr hist a) ∧
      (∀ a, a ≠ G.addr.val → (a < (shadow G).val ∨ (shadow G).val+span (pairLengths G i) hist.length ≤ a) →
        A.memory () a = m a) ∧
      (A.logs ()).length = populated (pairLengths G i) hist.length + 1 ∧
      ∀ r ∈ A.logs (), r.probes ≤ 14 := by
  let L := pairLengths G i
  let N := populated L hist.length
  let f := G.clockAt Stage.auxiliaryCopy
  let P := Pieces.component G.components Stage.auxiliaryCopy G.g G.lit
  obtain ⟨active,closed,hg,hh,hm,hlen,hactive,hclose,hprobe,_,frame⟩ :=
    LiveAuxiliaryStages.guarded_copy_native areas.shadowFit areas.countFit areas.separated f
      (show 68 ≤ _ by omega) G.addr (Or.inl tagBefore) prepared
  let rs := active ++ [closed]
  have hr : runSegment P f (some 0) m (List.replicate (N+1) []) = some rs := by
    change runSegment (LiveAuxiliaryStages.copy.instantiate G.w
      (Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.auxiliaryCopy G.constants)).program _ _ _ _ = _
    rw [copy_data]
    exact hg
  have bounds (r : Report G.w) (hr : r ∈ rs) : r.events.length < 68 ∧ r.probes ≤ 12 := by
    rcases List.mem_append.mp hr with ha | hc
    · exact ⟨(hactive r ha).1,(hactive r ha).2.1⟩
    · obtain rfl := List.mem_singleton.mp hc; omega
  have fit (r : Report G.w) (hr : r ∈ rs) : room G.nextStage G.addr Stage.auxiliaryCopy f r := by
    obtain ⟨hb,_⟩ := bounds r hr
    cases r with
    | mk es result =>
      cases result with
      | none =>
        change (es ++ transferEvents G.addr Stage.pair).length < f
        rw [List.length_append]; change es.length + 3 < _
        change es.length < _ at hb
        dsimp [f]; omega
      | some st =>
        change es.length < _
        change es.length < _ at hb
        dsimp [f]; omega
  let A := deterministicIndexed tag hr hh fit frame
  have hrep : ordinaryReports (A.traces ()) = rs := deterministic_reports ..
  have hout : A.memory () = writeMemory (install (shadow G).val L hdr hist areas.shadowFit m)
      G.addr (tagWord G.w Stage.pair) := by
    change transferMemory G.addr _ (after m (eventLog (ordinaryReports (A.traces ())))) = _
    rw [hrep,hm]
    rfl
  refine ⟨A,?_,?_,?_,?_⟩
  · intro a ha
    rw [hout,writeMemory,ite_eq_right (show (shadow G).val+a ≠ G.addr.val by omega)]
    exact install_read _ _ _ _ _ _ _ (fresh _ ha)
  · intro a ha houtside; rw [hout,writeMemory,ite_eq_right ha]
    exact install_outside _ _ _ _ _ _ _ houtside
  · simp [Indexed.logs,hrep,rs,hlen]
  · intro r hr
    rw [Indexed.logs,hrep,List.mem_map] at hr
    obtain ⟨r,hin,rfl⟩ := hr
    rw [linkedReport_probes]
    have h := (bounds _ hin).2
    split <;> omega

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
