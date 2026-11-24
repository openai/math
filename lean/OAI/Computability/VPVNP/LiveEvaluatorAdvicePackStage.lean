import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackSweep

/-!
# Advice packing as a linkable stage

The wrapped table uses the ordinary sweep when rows are allocated. An empty
bank takes one accepting call with zero probes, so the stage linker advances
in both cases. The unique accepting stream has one empty list per call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceBanks

open BurstRAM

variable {w : ℕ}

/-- Allocated nonempty rows have one reset plus one call per column. The
empty bank has one accepting call at its zero cursor. -/
def stageCalls (pub : Fin 5 → Word w) := max 1 (packCalls pub)

/-- At an individual cursor the native stage produces one deterministic report
and advances the entire row-prefix memory, including the empty-bank handoff. -/
theorem stageStep {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) {fuel : ℕ} (hf : stageFuel ≤ fuel)
    (i : ℕ) (hi : i < stageCalls pub) :
    let P := (stageTable.instantiate w pub).program
    let mem := packMemory pub raw m (min i (packCalls pub))
    ∃ es, (∀ bs, execute P fuel (P.start (Fin.ofNat (2^w) i)) mem bs =
      if bs = [] then some ⟨es, packControl w (stageCalls pub) (i+1)⟩ else none) ∧
      after mem es = packMemory pub raw m (min (i+1) (packCalls pub)) ∧ countProbes es ≤ 3 := by
  intro P mem
  by_cases hz : pub 4 = 0
  · have hpack : packCalls pub = 0 := by simp [packCalls, hz]
    have hcount : stageCalls pub = 1 := by simp [stageCalls, hpack]
    have hzero : i = 0 := by omega
    subst i
    have hmem : mem = m := by simp [mem, hpack, packMemory_zero]
    rw [hmem]
    let rep := stageReport pub 0 m
    refine ⟨rep.events, ?_, ?_, stageReport_probes_le ..⟩
    · intro bs
      have hx := execute_stage_empty pub m hz (fun _ => 0) (fun _ => 0) bs hf
      change execute P fuel (P.start 0) m bs = if bs.isEmpty then some rep else none at hx
      have hs : packControl w (stageCalls pub) 1 = none := by simp [packControl, hcount]
      have hr : rep = ⟨rep.events, packControl w (stageCalls pub) 1⟩ := by
        rw [hs]
        simp [rep, stageReport, hz]
      rw [← hr]
      cases bs <;> exact hx
    · simp [hpack, packMemory_zero, rep, stageReport_memory, hz]
  · have hpos : 0 < packCalls pub := by
      have h : 0 < (pub 4).val := Nat.pos_of_ne_zero fun he => hz (Fin.ext he)
      exact Nat.mul_pos h (Nat.succ_pos _)
    have hcount : stageCalls pub = packCalls pub := max_eq_right hpos
    rw [hcount] at hi
    have hm' : mem = packMemory pub raw m i := by rw [show mem = packMemory pub raw m (min i (packCalls pub)) from rfl, min_eq_left hi.le]
    have hsrc : PackSource pub raw mem := hm' ▸ packMemory_source pub raw m L hs i
    let st := Fin.ofNat (2^w) i
    obtain ⟨hcur, hb, hnext⟩ := packStep_guards L mem hsrc i hi
    let rep := stageReport pub st mem
    refine ⟨rep.events, ?_, ?_, stageReport_probes_le ..⟩
    · intro bs
      have hx := execute_stage_step pub st mem hz hcur hb (fun _ => 0) (fun _ => 0) bs hf
      change execute P fuel (P.start st) mem bs = if bs.isEmpty then some rep else none at hx
      have hr : rep = ⟨rep.events, packControl w (stageCalls pub) (i+1)⟩ := by
        rw [hcount, ← hnext]
        simp [rep, stageReport, hz, st]
      rw [← hr]
      cases bs <;> exact hx
    · change after mem (stageReport pub st mem).events = _
      rw [stageReport_memory, ite_eq_right hz, hm']
      rw [min_eq_left hi]
      exact packMemory_step L m hs i hi

/-- The linked-stage table prepares all word rows and has one exact native
stream, including when there are zero output rows. -/
theorem packStageSweep {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) {fuel : ℕ} (hf : stageFuel ≤ fuel) :
    let P := (stageTable.instantiate w pub).program
    ∃ reports, after m (eventLog reports) = packMemory pub raw m (packCalls pub) ∧
      reports.length = stageCalls pub ∧ RAMBuckets.cost Report.probes reports ≤ 4*stageCalls pub ∧
      (∀ r ∈ reports, r.probes ≤ 3 ∧ r.events.length < fuel) ∧
      ∀ bits rs, (runSegment P fuel (some 0) m bits = some rs ∧ endState (some 0) rs = none) ↔
        bits = List.replicate (stageCalls pub) [] ∧ rs = reports := by
  intro P
  let inv := fun i mem => mem = packMemory pub raw m (min i (packCalls pub))
  have initial : inv 0 m := by simp [inv, packMemory_zero]
  have step (i : ℕ) (hi : i < stageCalls pub) (mem : Memory w) (hm : inv i mem) := hm ▸ stageStep L m hs hf i hi
  have hn : 0 < stageCalls pub := Nat.zero_lt_one.trans_le (le_max_left ..)
  have hc : packControl w (stageCalls pub) 0 = some 0 := by simp [packControl, hn.ne]
  have hle : packCalls pub ≤ stageCalls pub := le_max_right ..
  simpa only [hc, inv, min_eq_right hle] using
    deterministic_scan P fuel (stageCalls pub) 3 inv step (stageCalls pub) 0 (Nat.zero_add _) m initial

/-- The wrapper has native path multiplicity one under Lemma 10.1's caps. -/
theorem packStagePathCount {pub : Fin 5 → Word w} {raw : List Bool} (L : PackLayout pub raw)
    (m : Memory w) (hs : PackSource pub raw m) {fuel : ℕ} (hf : stageFuel ≤ fuel)
    {S H : ℕ} (hcost : 4*stageCalls pub ≤ S*H) (hcap : 4 ≤ H) :
    Nat.card (ActualPaths (stageTable.instantiate w pub).program fuel 0 m (withinCaps S H)) = 1 := by
  let paths := ActualPaths (stageTable.instantiate w pub).program fuel 0 m (withinCaps S H)
  obtain ⟨reports, _, _, hc, hcalls, hall⟩ := packStageSweep L m hs hf
  have hwithin : withinCaps S H reports :=
    ⟨hc.trans hcost, fun r hr => by have := (hcalls r hr).1; omega⟩
  have uniq (b : paths) : b.val = List.replicate (stageCalls pub) [] := by
    obtain ⟨rs, hr, he, _⟩ := b.property
    exact ((hall b.val rs).mp ⟨hr, he⟩).1
  have ⟨hr, he⟩ := (hall (List.replicate (stageCalls pub) []) reports).mpr ⟨rfl, rfl⟩
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun a b => Subtype.ext ((uniq a).trans (uniq b).symm)⟩,
      ⟨⟨List.replicate (stageCalls pub) [], reports, hr, he, hwithin⟩⟩⟩

end LiveEvaluatorAdviceBanks

end VPVNP
end Computability
end OAI
