import OAI.Computability.VPVNP.LiveOutsideBudget
import OAI.Computability.VPVNP.LiveHeaderAcceptance
import OAI.Computability.VPVNP.LiveProgramUnit
import OAI.Computability.VPVNP.LiveProgramHeader

/-!
# Outside costs of the actual live group reports

The outer dispatcher reads its tag once per call and can write a successor
tag on an accepting handoff. The bounds below charge these events on the
real header and router logs, along with the private instruction events.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTraces

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule ChainAssignments

variable {w d : ℕ}

open private guessed_addFuel from OAI.Computability.VPVNP.LiveStageLinkPaths

/-- Total cost, maximal call cost, and maximal private instruction count.
A report logs every instruction except its final return or acceptance. -/
structure Resources (rs : List (Report w)) (total perCall instructions : ℕ) : Prop where
  cost : RAMBuckets.cost Report.probes rs ≤ total
  calls : ∀ r ∈ rs, 1+r.probes ≤ perCall
  work : ∀ r ∈ rs, r.events.length+1 ≤ instructions

theorem Resources.append {rs ts : List (Report w)} {a b c a' b' c' : ℕ}
    (hr : Resources rs a b c) (ht : Resources ts a' b' c') :
    Resources (rs++ts) (a+a') (max b b') (max c c') := by
  constructor
  · rw [RAMBuckets.cost_append]; exact Nat.add_le_add hr.cost ht.cost
  · intro r h
    exact (List.mem_append.mp h).elim (fun h => (hr.calls r h).trans (le_max_left ..))
      (fun h => (ht.calls r h).trans (le_max_right ..))
  · intro r h
    exact (List.mem_append.mp h).elim (fun h => (hr.work r h).trans (le_max_left ..))
      (fun h => (ht.work r h).trans (le_max_right ..))

theorem Resources.cap {rs : List (Report w)} {a b c S H : ℕ} (h : Resources rs a b c)
    (ht : a ≤ S*H) (hl : b ≤ H) : withinCaps S H rs := ⟨h.cost.trans ht,fun r hr => (h.calls r hr).trans hl⟩

private theorem linked_cost_le {t : ℕ} (next : Fin t → Option (Fin t)) (addr : Word w) (stage : Fin t)
    (rs : List (Report w)) :
    RAMBuckets.cost Report.probes (rs.map (LiveStageLink.linkedReport next addr stage)) ≤
      RAMBuckets.cost Report.probes rs + 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,RAMBuckets.cost,List.length_cons,Nat.mul_succ,LiveStageLink.linkedReport_probes]
    split <;> omega

private theorem source_clock {s : Sizes} {base : ℕ} {id : Option LiveHeaderProgram.StageId}
    {m : Memory w} {xs : List (LiveHeaderProgram.StageTrace w)}
    (runs : LiveHeaderProgram.StageRuns s base id m xs) :
    ∀ x ∈ xs, ∀ r ∈ x.reports, r.events.length < x.fuel := by
  induction runs with
  | done => simp
  | cons x hsrc _ _ _ ih =>
    intro y hy r hr
    rcases List.mem_cons.mp hy with rfl | hy
    · exact localSegment_event_bound ((runSegment_iff ..).mp hsrc).1 r hr
    · exact ih y hy r hr

/-- Reports of the actual header stage after the outer D dispatch and
handoff. This map does not add a microcall. -/
def headerReports (p : UniversalMachine.Program) (addr : Word w) (raw : List (Report w)) :=
  raw.map (LiveStageLink.linkedReport (next p) addr LiveProgram.Stage.header)

/-- Every successful physical header path, at any admissible caller clock,
has the same cost and private-work bound as the short compiled run. -/
theorem header_resources (p : UniversalMachine.Program) (outer : Word w) (s : Sizes) (base cap : ℕ)
    (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (bounds : LiveHeaderProgram.Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : LiveHeaderSchedule.stages.length ≤ 2^w) (fuel : 107 ≤ cap) {bs raw}
    (hr : runSegment (LiveHeaderProgram.nativeHeader w s base) cap (some 0)
      (LiveHeader.physicalMemory (d := d) hw advice cuts g) bs = some raw)
    (he : endState (some (0 : Word w)) raw = none) :
    Resources (headerReports p outer raw) (costBound s) 11 154 := by
  obtain ⟨tag,hsel,pads⟩ := (LiveHeaderProgram.accepting_iff s base cap hw advice cuts g bounds indices adv
    tagFit fuel).mp ⟨bs,raw,hr,he⟩
  obtain ⟨rs,_,_,_,_,hcost,hprobe,hunique⟩ := LiveHeaderProgram.valid_native s base cap hw advice cuts g
    tag bounds indices adv tagFit fuel hsel pads
  obtain ⟨_,rfl⟩ := hunique bs raw hr he
  obtain ⟨xs,_,full,good,_,_⟩ := LiveHeaderProgram.complete_stages s base hw advice cuts g tag bounds
    indices adv hsel pads
  let inner : Word w := Fin.ofNat _ base
  have hroom (x : LiveHeaderProgram.StageTrace w) (hx : x ∈ xs) : x.fuel+2*stages.length+5 ≤ cap := by
    have := (good x hx).1
    rw [stage_count]; omega
  have hval : inner.val = base := by
    have hb := bounds.fit
    rw [limit_eq] at hb
    exact Nat.mod_eq_of_lt (by omega)
  have hz : LiveHeader.physicalMemory (d := d) hw advice cuts g inner.val = 0 := by
    have hb := bounds.scratch
    simp [LiveHeader.physicalMemory,RAMMemory.initialMemory,hval,show ¬base < 2^d by omega]
  have hempty (x : LiveHeaderProgram.StageTrace w) (hx : x ∈ xs) (b : List Bool) (hb : b ∈ x.paths) : b = [] := by
    rw [(good x hx).2.1] at hb
    exact (List.mem_replicate.mp hb).2
  have hrows := (LiveHeaderProgram.accepted_path_unique s base cap tagFit full hroom hz hempty hr he).2
  constructor
  · exact (linked_cost_le _ _ _ _).trans hcost
  · intro r h
    obtain ⟨r',hr',rfl⟩ := List.mem_map.mp h
    rw [LiveStageLink.linkedReport_probes]
    have := hprobe r' hr'
    split <;> omega
  · intro r h
    obtain ⟨r',hr',rfl⟩ := List.mem_map.mp h
    have outerLen := LiveStageLink.linkedReport_length_le (next p) outer LiveProgram.Stage.header r'
    rw [hrows] at hr'
    obtain ⟨x,hx,hx'⟩ := List.mem_flatMap.mp hr'
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx'
    have src := source_clock full x hx v hv
    have hclock := (good x hx).1
    have innerLen := LiveStageLink.linkedReport_length_le LiveHeaderProgram.next inner x.id v
    change (LiveStageLink.linkedReport LiveHeaderProgram.next (Fin.ofNat (2^w) base) x.id v).events.length ≤ v.events.length + 2*31+5 at innerLen
    change _ ≤ _ + 2*21+5 at outerLen
    omega

private theorem local_more {C : Type*} (P : BurstRAM.Program w C) {f g : ℕ} (hfg : f ≤ g) {st : Option (Word w)}
    {rs : List (Report w)} (h : LocalSegment P f st rs) : LocalSegment P g st rs := by
  induction rs generalizing st with
  | nil => trivial
  | cons r rs ih =>
    cases st with
    | none => contradiction
    | some st => exact ⟨by simpa only [Nat.add_sub_cancel' hfg] using guessed_addFuel h.1 (g-f),ih h.2⟩

/-- The prefix executed by the outer physical machine has bounded work
at every call, even when the group clock is much larger than 154. -/
theorem actual_header (G : PairStages.Group) (hw : 4 ≤ G.w) (advice : CutSchedule.Bits (Header.sizes G.constants G.g).advice)
    (cuts : AllCuts (Header.sizes G.constants G.g).h (Header.sizes G.constants G.g).delta)
    (i : Fin (2^((Header.sizes G.constants G.g).h+1))) (tag : LiveHeader.Mode.Tag)
    (bounds : LiveHeaderProgram.Fields.Bounds (Header.sizes G.constants G.g) (Header.base G.g) G.g.d G.w)
    (hi : (Header.sizes G.constants G.g).h+2 ≤ 2^G.g.d) (had : (Header.sizes G.constants G.g).advice ≤ 2^G.g.d)
    (ht : stages.length ≤ 2^G.w) (hclock : 154 ≤ G.clock) (mode : LiveHeader.physicalTag cuts i = some tag)
    (pad : ∀ side, LiveHeaderProgram.Fields.ValidPadding (Header.sizes G.constants G.g) cuts i tag side) :
    let s := Header.sizes G.constants G.g
    let m := LiveHeader.physicalMemory (d := G.g.d) hw advice cuts i
    ∃ rs, runSegment G.P G.clock (some 0) m (List.replicate (callBound s) []) = some rs ∧
      endState (some 0) rs = some 0 ∧ LiveHeaderProgram.Output s (Header.base G.g) G.g.d hw advice cuts i tag
        (after m (eventLog rs)) ∧ G.tagged LiveProgram.Stage.mode (after m (eventLog rs)) ∧
      Resources rs (costBound s) 11 154 := by
  obtain ⟨rs,hr,hs,output,htag,_,hc,hp⟩ := Header.valid_prefix G.constants G.evaluator G.pair G.g G.lit 154
    hw advice cuts i tag bounds hi had ht le_rfl mode pad
  have ⟨localRun,hm,hb⟩ := (runSegment_iff ..).mp hr
  refine ⟨rs,?_,hs,output,htag,hc,fun r h => by have := hp r h; omega,fun r h => ?_⟩
  · rw [G.program_eq]
    exact (runSegment_iff ..).mpr ⟨local_more _ hclock localRun,hm,hb⟩
  · exact localSegment_event_bound localRun r h

/-- A selected jump, including the flag read, explicit route write and outer
tag read. No branch bit is charged. -/
theorem router_jump (r : Router) (p : UniversalMachine.Program) (g : Geometry) (lit : LiteralPrefix)
    (i : Fin 3) (flag : Word g.w) (dest : LiveProgram.Stage) :
    Resources [r.outerReport p g lit (r.jumpReport g lit i flag dest)] 4 4 60 := by
  let raw := r.jumpReport g lit i flag dest
  have probes : raw.probes = 2 := by fin_cases i <;> rfl
  have rawLen : raw.events.length ≤ 12 := by
    have := i.isLt
    simp [raw,Router.jumpReport]; omega
  let out := r.outerReport p g lit raw
  have hp : out.probes = 3 := by
    dsimp only [out,Router.outerReport]
    rw [LiveStageLink.linkedReport_probes,r.terminal p]
    simp [probes]
  have hw : out.events.length+1 ≤ 60 := by
    have h := LiveStageLink.linkedReport_length_le (next p) (Pieces.word g lit (.geometry Layout.stageTag)) r.stage raw
    change out.events.length ≤ raw.events.length + 2*21+5 at h
    omega
  change Resources [out] 4 4 60
  refine ⟨by simp [RAMBuckets.cost,hp],?_,?_⟩
  · intro x hx; obtain rfl := List.mem_singleton.mp hx; omega
  · intro x hx; obtain rfl := List.mem_singleton.mp hx; exact hw

/-- Unit mode terminates with one flag read and one outer tag read. -/
theorem router_halt (r : Router) (p : UniversalMachine.Program) (g : Geometry) (lit : LiteralPrefix)
    (i : Fin 3) (flag : Word g.w) :
    Resources [r.outerReport p g lit (r.haltReport g lit i flag)] 3 3 56 := by
  let raw := r.haltReport g lit i flag
  have probes : raw.probes = 1 := by fin_cases i <;> rfl
  have rawLen : raw.events.length ≤ 8 := by
    have := i.isLt
    simp [raw,Router.haltReport]; omega
  let out := r.outerReport p g lit raw
  have hp : out.probes = 2 := by
    dsimp only [out,Router.outerReport]
    rw [LiveStageLink.linkedReport_probes,r.terminal p]
    simp [probes]
  have hw : out.events.length+1 ≤ 56 := by
    have h := LiveStageLink.linkedReport_length_le (next p) (Pieces.word g lit (.geometry Layout.stageTag)) r.stage raw
    change out.events.length ≤ raw.events.length + 2*21+5 at h
    omega
  change Resources [out] 3 3 56
  refine ⟨by simp [RAMBuckets.cost,hp],?_,?_⟩
  · intro x hx; obtain rfl := List.mem_singleton.mp hx; omega
  · intro x hx; obtain rfl := List.mem_singleton.mp hx; exact hw

end LiveProgram.OutsideTraces

end VPVNP
end Computability
end OAI
