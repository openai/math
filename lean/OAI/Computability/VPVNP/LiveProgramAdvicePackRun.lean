import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveStageSegments
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackStage

/-!
# The three advice pack sweeps in the outer live program

The fixed component dispatches its row cells on the shared external memory.
Every intermediate cursor preserves the stage tag. The last report replaces
the tag by the destination and returns zero. The indirect prefix stage reads
its five public operands from a stable external frame on every call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.AdvicePackRun

open BurstRAM LiveEvaluatorAdviceBanks
open LiveStageLink (tagWord linkedReport)
open CompressorRecords
open scoped Fin.CommRing

/-- External address of the outer stage tag used when the packed advice stages transfer
control. -/
abbrev tagAddr (g : Geometry) (lit : LiteralPrefix) := Pieces.word g lit (.geometry Layout.stageTag)

variable {c : Constants} {p : UniversalMachine.Program} {O : PairTable}
variable {g : Geometry} {lit : LiteralPrefix} {s dest : Stage}
variable {pub : Fin 5 → Word g.w} {raw : List Bool} {cap : ℕ}

private theorem run_fixed {w : ℕ} {C : Type*} (P : BurstRAM.Program w C) (fuel n bound : ℕ)
    (state : ℕ → Word w) (mem : ℕ → Memory w)
    (step : ∀ i < n, ∃ r, execute P fuel (P.start (state i)) (mem i) [] = some r ∧
      r.result = some (state (i+1)) ∧ after (mem i) r.events = mem (i+1) ∧ r.probes ≤ bound) :
    ∃ rs, runSegment P fuel (some (state 0)) (mem 0) (List.replicate n []) = some rs ∧
      endState (some (state 0)) rs = some (state n) ∧ after (mem 0) (eventLog rs) = mem n ∧
      rs.length = n ∧ ∀ r ∈ rs, r.probes ≤ bound ∧ r.events.length < fuel := by
  induction n with
  | zero => exact ⟨[], rfl, rfl, rfl, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨rs, hrun, hstate, hmem, hlen, hcost⟩ := ih (fun i hi => step i (by omega))
    obtain ⟨r, hr, hs, hm, hp⟩ := step n (by omega)
    refine ⟨rs ++ [r], ?_, ?_, ?_, by simp [hlen], ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hrun]
      simp only [Option.bind_some, hstate, hmem, runSegment, hr, Option.map_some]
    · simpa only [endState_append, endState] using hs
    · simpa only [eventLog, List.flatMap_append, List.flatMap_singleton, after, List.foldl_append] using
        (show after (after (mem 0) (eventLog rs)) r.events = _ by rwa [hmem])
    · rw [List.forall_mem_append, List.forall_mem_singleton]
      exact ⟨hcost, hp, (execute_spec hr).1.length_lt⟩

private abbrev image (pub : Fin 5 → Word g.w) (raw : List Bool) (m : Memory g.w) (i : ℕ) :=
  packMemory pub raw m (min i (packCalls pub))

/-- Endpoint and resource specification of the linked advice stage. -/
def LinkedPack (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (dest : Stage) (pub : Fin 5 → Word g.w) (raw : List Bool)
    (m : Memory g.w) (cap probes : ℕ) : Prop :=
  ∃ logs, runSegment (machine c p O g lit).program cap (some 0) m
      (List.replicate (stageCalls pub) []) = some logs ∧
    endState (some 0) logs = some 0 ∧ after m (eventLog logs) =
      writeMemory (packMemory pub raw m (packCalls pub)) (tagAddr g lit) (tagWord g.w dest) ∧
    logs.length = stageCalls pub ∧ ∀ r ∈ logs, r.probes ≤ probes ∧ r.events.length < cap

private theorem lift (m : Memory g.w) (hnext : next p s = some dest) (fit : 21 ≤ 2^g.w)
    (f b : ℕ) (hcap : f+47 ≤ cap) (htag : m (tagAddr g lit).val = tagWord g.w s)
    (outside : (tagAddr g lit).val < (pub 1).val ∨ (pub 1).val+(pub 4).val ≤ (tagAddr g lit).val)
    (step : ∀ i < stageCalls pub,
      let Q := Pieces.component (rows c p O) s g lit
      let mem := image pub raw m i
      ∃ r, execute Q f (Q.start (Fin.ofNat (2^g.w) i)) mem [] = some r ∧
        r.result = packControl g.w (stageCalls pub) (i+1) ∧ after mem r.events = image pub raw m (i+1) ∧
        r.probes ≤ b) : LinkedPack c p O g lit dest pub raw m cap (b+2) := by
  let tag := tagAddr g lit
  let total := stageCalls pub
  let cursor := fun i => if i = total then (0 : Word g.w) else Fin.ofNat (2^g.w) i
  let mem := fun i => if i = total then writeMemory (image pub raw m i) tag (tagWord g.w dest)
    else image pub raw m i
  let P := (machine c p O g lit).program
  have one (i : ℕ) (hi : i < total) : ∃ r, execute P cap (P.start (cursor i)) (mem i) [] = some r ∧
      r.result = some (cursor (i+1)) ∧ after (mem i) r.events = mem (i+1) ∧ r.probes ≤ b+2 := by
    obtain ⟨r, hr, hstate, hmem, hprobes⟩ := step i hi
    have tagged : image pub raw m i tag.val = tagWord g.w s := by
      rw [image, packMemory_outside _ _ _ _ _ outside, htag]
    let out := linkedReport (next p) tag s r
    have hcall := Pieces.execute_component (rows c p O) (next p) Layout.stageTag g lit s fit hcap
      (Fin.ofNat (2^g.w) i) (image pub raw m i) tagged [] r hr
    refine ⟨out, ?_, ?_, ?_, ?_⟩
    · rw [show mem i = image pub raw m i from ite_eq_right hi.ne,
          show cursor i = Fin.ofNat (2^g.w) i from ite_eq_right hi.ne]
      exact hcall
    · rw [show out.result = _ from LiveStageLink.linkedReport_result (next p) tag s r, hstate]
      by_cases hlast : i+1 = total
      · simp only [packControl, cursor, total, ite_eq_left (show i+1 = stageCalls pub from hlast),
          hnext, Option.map_some]
      · simp only [packControl, cursor, show ¬i+1 = stageCalls pub from hlast, hlast, ite_false]
    · rw [show mem i = image pub raw m i from ite_eq_right hi.ne]
      rw [show after (image pub raw m i) out.events = _ from
        LiveStageLink.linkedReport_after (next p) tag s r _, hstate, hmem]
      by_cases hlast : i+1 = total
      · simp only [packControl, mem, total, ite_eq_left (show i+1 = stageCalls pub from hlast), hnext]
      · simp only [packControl, mem, show ¬i+1 = stageCalls pub from hlast, hlast, ite_false]
    · have hp := LiveStageLink.linkedReport_probes (next p) tag s r
      change (linkedReport (next p) tag s r).probes ≤ b+2
      rw [hp]
      split <;> omega
  have ht : 0 < total := Nat.zero_lt_one.trans_le (le_max_left ..)
  have hc : packCalls pub ≤ total := le_max_right ..
  simpa only [LinkedPack, P, cursor, mem, ite_eq_right ht.ne, ite_eq_left rfl, image, tag,
    show Fin.ofNat (2^g.w) 0 = 0 from rfl,
    Nat.zero_min, packMemory_zero, min_eq_right hc] using run_fixed P cap total (b+2) cursor mem one

/-- The linked program executes a directly supplied row packer and advances
to the next stage with its destination tag and zero cursor. -/
theorem linkedPack_direct (L : PackLayout pub raw) (m : Memory g.w) (hs : PackSource pub raw m)
    (hnext : next p s = some dest) (fit : 21 ≤ 2^g.w) (hcap : 80 ≤ cap)
    (htag : m (tagAddr g lit).val = tagWord g.w s)
    (outside : (tagAddr g lit).val < (pub 1).val ∨ (pub 1).val+(pub 4).val ≤ (tagAddr g lit).val)
    (same : ∀ st mem bits, let Q := Pieces.component (rows c p O) s g lit
      let R := (stageTable.instantiate g.w pub).program
      execute Q 33 (Q.start st) mem bits = execute R 33 (R.start st) mem bits) :
    LinkedPack c p O g lit dest pub raw m cap 5 := by
  apply lift m hnext fit 33 3 hcap htag outside
  intro i hi Q mem
  obtain ⟨es, hr, hm, hp⟩ := stageStep L m hs (fuel := 33) le_rfl i hi
  exact ⟨⟨es, packControl g.w (stageCalls pub) (i+1)⟩, (same _ mem []).trans (hr []), rfl, hm, hp⟩

/-- Loading five public operands on every call preserves the same output
memory. The frame remains readable throughout because each of its five
addresses lies outside the bank being written. -/
theorem linkedPack_framed (L : PackLayout pub raw) (m : Memory g.w) (hs : PackSource pub raw m)
    (hnext : next p s = some dest) (fit : 21 ≤ 2^g.w) (hcap : 100 ≤ cap)
    (htag : m (tagAddr g lit).val = tagWord g.w s)
    (outside : (tagAddr g lit).val < (pub 1).val ∨ (pub 1).val+(pub 4).val ≤ (tagAddr g lit).val)
    (base : Word g.w) (hdata : Frame.data base m = pub)
    (frameOutside : ∀ j : Fin 5, (base+Fin.ofNat (2^g.w) j.val).val < (pub 1).val ∨
      (pub 1).val+(pub 4).val ≤ (base+Fin.ofNat (2^g.w) j.val).val)
    (same : ∀ st mem bits, let Q := Pieces.component (rows c p O) s g lit
      let R := (Frame.machine stageTable base).program
      execute Q 53 (Q.start st) mem bits = execute R 53 (R.start st) mem bits) :
    LinkedPack c p O g lit dest pub raw m cap 10 := by
  apply lift m hnext fit 53 8 hcap htag outside
  intro i hi Q mem
  obtain ⟨es, hr, hm, hp⟩ := stageStep L m hs (fuel := 33) le_rfl i hi
  let st := Fin.ofNat (2^g.w) i
  let r : Report g.w := ⟨es, packControl g.w (stageCalls pub) (i+1)⟩
  let wrapped := LiveStageLink.prependLog (Frame.loadEvents base mem 0 5) r
  have bank : Frame.data base mem = pub := by
    rw [← hdata]
    funext j
    exact packMemory_outside pub raw m _ _ (frameOutside j)
  have hsource : execute (stageTable.instantiate g.w pub).program 33
      ((stageTable.instantiate g.w pub).program.start st) mem [] = some r := hr []
  have hwrap := Frame.execute_frame stageTable base st 33 mem []
  dsimp only at hwrap
  rw [bank, hsource] at hwrap
  obtain ⟨_, hpr, _, hmemory, hresult⟩ := Frame.frame_cost base mem 0 5 r
  have hbound : wrapped.probes ≤ 8 := by
    change r.probes ≤ 3 at hp
    change wrapped.probes = 5+r.probes at hpr
    omega
  exact ⟨wrapped, (same st mem []).trans hwrap, hresult, hmemory.trans hm, hbound⟩

end LiveProgram.AdvicePackRun

end VPVNP
end Computability
end OAI
