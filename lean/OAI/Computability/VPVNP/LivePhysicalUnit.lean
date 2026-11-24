import OAI.Computability.VPVNP.LiveProgramHeaderFlags
import OAI.Computability.VPVNP.LiveProgramHeader
import OAI.Computability.VPVNP.LiveProgramUnit
import OAI.Computability.VPVNP.LiveHeaderFieldUnitPadding

/-!
# The physical unit-mode group has one capped native path

The starting memory is the paper's distributed processor header, with zero
default outside it. The theorem runs the complete header and outer router,
including the mode agreement and zero-padding checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.UnitGroup
open BurstRAM LiveHeaderProgram LiveHeaderSchedule LiveHeader ChainAssignments PairStages

theorem physical_card_one (G : Group) (hw : 4 ≤ G.g.w) (fuel : 154 ≤ G.clock)
    (advice : CutSchedule.Bits (Header.sizes G.constants G.g).advice)
    (cuts : AllCuts (Header.sizes G.constants G.g).h (Header.sizes G.constants G.g).delta)
    (i : Fin (2^((Header.sizes G.constants G.g).h+1)))
    (bounds : Fields.Bounds (Header.sizes G.constants G.g) (Header.base G.g) G.g.d G.g.w)
    (hi : (Header.sizes G.constants G.g).h+2 ≤ 2^G.g.d) (had : (Header.sizes G.constants G.g).advice ≤ 2^G.g.d)
    (ht : stages.length ≤ 2^G.g.w) (mode : physicalTag cuts i = some .unit)
    (pads : ∀ side, Fields.ValidPadding (Header.sizes G.constants G.g) cuts i .unit side)
    {S H : ℕ} (hc : costBound (Header.sizes G.constants G.g) + 3 ≤ S*H) (hH : 11 ≤ H) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (physicalMemory (d := G.g.d) hw advice cuts i) (withinCaps S H)) = 1 := by
  let m := physicalMemory (d := G.g.d) hw advice cuts i
  obtain ⟨logs,hr,he,out,tagged,_,hcost,hprobes⟩ := Header.valid_prefix G.constants G.evaluator G.pair G.g
    G.lit G.clock hw advice cuts i .unit bounds hi had ht fuel mode pads
  have hrun : runSegment G.P G.clock (some 0) m (List.replicate (callBound (Header.sizes G.constants G.g)) []) = some logs := by
    rw [G.program_eq]; exact hr
  have hmode : (after m (eventLog logs)) ((Router.mode.data G.g G.lit) 0).val = 0 :=
    HeaderFlags.mode G.constants G.g G.lit bounds.fit out
  rw [← G.program_eq]
  apply card_one G (by change 2 ≤ G.g.w; omega) (by omega) hrun he hmode tagged
  apply (cap_iff G S H logs).2
  exact ⟨by omega, fun r hr => by have := hprobes r hr; omega, by omega⟩

/-- Disagreeing incident modes or malformed padding make the entire native
path set empty, regardless of the clock-independent path cap. -/
theorem physical_card_zero (G : Group) (hw : 4 ≤ G.g.w) (fuel : 154 ≤ G.clock)
    (advice : CutSchedule.Bits (Header.sizes G.constants G.g).advice)
    (cuts : AllCuts (Header.sizes G.constants G.g).h (Header.sizes G.constants G.g).delta)
    (i : Fin (2^((Header.sizes G.constants G.g).h+1)))
    (bounds : Fields.Bounds (Header.sizes G.constants G.g) (Header.base G.g) G.g.d G.g.w)
    (hi : (Header.sizes G.constants G.g).h+2 ≤ 2^G.g.d) (had : (Header.sizes G.constants G.g).advice ≤ 2^G.g.d)
    (ht : stages.length ≤ 2^G.g.w)
    (invalid : ¬ ∃ tag, physicalTag cuts i = some tag ∧ ∀ side, Fields.ValidPadding (Header.sizes G.constants G.g) cuts i tag side)
    (cap : List (Report G.w) → Prop) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (physicalMemory (d := G.g.d) hw advice cuts i) cap) = 0 := by
  apply Nat.card_eq_zero.mpr (Or.inl ?_)
  refine ⟨?_⟩
  rintro ⟨bs,logs,hr,hh,_⟩
  exact invalid (Header.necessary G.constants G.evaluator G.pair G.g G.lit G.clock hw advice cuts i
    bounds hi had ht fuel bs logs hr hh)

/-- Whenever the incident bits fail the evaluation-mode test of (9.4), the
entire native path count equals the exact unit summand of the contraction.
This includes unequal mode bits and a zero mode with nonzero payload. -/
theorem physical_unitGroupCount (G : Group) (hw : 4 ≤ G.g.w) (fuel : 154 ≤ G.clock)
    (advice : CutSchedule.Bits (Header.sizes G.constants G.g).advice)
    (cuts : AllCuts (Header.sizes G.constants G.g).h (Header.sizes G.constants G.g).delta)
    (i : Fin (2^((Header.sizes G.constants G.g).h+1)))
    (bounds : Fields.Bounds (Header.sizes G.constants G.g) (Header.base G.g) G.g.d G.g.w)
    (hi : (Header.sizes G.constants G.g).h+2 ≤ 2^G.g.d) (had : (Header.sizes G.constants G.g).advice ≤ 2^G.g.d)
    (ht : stages.length ≤ 2^G.g.w) {S H : ℕ} (hc : costBound (Header.sizes G.constants G.g) + 3 ≤ S*H)
    (hH : 11 ≤ H) (inactive : ¬ (evalCutMode cuts i.castSucc ∧ evalCutMode cuts i.succ)) :
    Nat.card (ActualPaths (machine G.constants G.evaluator G.pair G.g G.lit).program G.clock 0
      (physicalMemory (d := G.g.d) hw advice cuts i) (withinCaps S H)) = unitGroupCount cuts i := by
  classical
  let s := Header.sizes G.constants G.g
  have hd : 0 < s.delta := by have h := bounds.exponents; change 1+s.e ≤ s.delta at h; omega
  have spec := physicalTag_unit hd cuts i s.e s.config
  unfold unitGroupCount
  split_ifs with hz
  · obtain ⟨mode,pad⟩ := spec.mpr hz
    exact physical_card_one G hw fuel advice cuts i bounds hi had ht mode ((Fields.validPadding_unit_iff ..).2 pad) hc hH
  · apply physical_card_zero G hw fuel advice cuts i bounds hi had ht
    rintro ⟨tag,mode,pad⟩
    cases tag with
    | unit => exact hz (spec.mp ⟨mode,(Fields.validPadding_unit_iff ..).1 pad⟩)
    | pair => exact inactive ((physicalTag_pair hd cuts i).1 mode).1
    | tail => exact inactive ((physicalTag_tail hd cuts i).1 mode).1

end LiveProgram.UnitGroup

end VPVNP
end Computability
end OAI
