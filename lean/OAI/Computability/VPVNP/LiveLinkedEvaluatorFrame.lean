import OAI.Computability.VPVNP.LiveLinkedEvaluatorHandoff
import OAI.Computability.VPVNP.LiveProgramAdviceSplice

/-!
# Returning from a framed evaluator stage in the linked program

A native scan supplies its exact reports at fixed operands. If its writes
leave the operand frame and tag intact, the physical program reads the same
operands on every call. Its last call writes the destination stage tag and
returns persistent cursor zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM BurstRAM.PrivateRAM LiveStageLink CompressorRecords

variable {G : Group} {k r p : ℕ} {s dest : Stage} {T : Template p r k}
  {base : Word G.w} {pub : Fin k → Word G.w} {fuel b : ℕ}

private theorem framedSegment (same : ∀ st mem bits,
    let C := Pieces.component G.components s G.g G.lit
    let R := (Frame.machine T base).program
    execute C (fuel+4*k) (C.start st) mem bits = execute R (fuel+4*k) (R.start st) mem bits)
    {st : Option (Word G.w)} {m : Memory G.w} {bs : List (List Bool)} {rs : List (Report G.w)}
    (data : Frame.data base m = pub)
    (run : runSegment (T.instantiate G.w pub).program fuel st m bs = some rs)
    (probes : ∀ rep ∈ rs, rep.probes ≤ b)
    (keep : ∀ rep ∈ rs, ∀ u, after u rep.events G.addr.val = u G.addr.val ∧
      Frame.data base (after u rep.events) = (Frame.data base u : Fin k → Word G.w)) :
    ∃ logs, runSegment (Pieces.component G.components s G.g G.lit) (fuel+4*k) st m bs = some logs ∧
      endState st logs = endState st rs ∧ after m (eventLog logs) = after m (eventLog rs) ∧
      logs.length = rs.length ∧ PreservesTagOnReturns G.addr m logs ∧
      ∀ rep ∈ logs, rep.probes ≤ b+k ∧ rep.events.length < fuel+4*k := by
  induction bs generalizing st m rs with
  | nil =>
    obtain rfl := Option.some.inj run
    exact ⟨[], rfl, rfl, rfl, rfl, trivial, by simp⟩
  | cons bits bs ih =>
    cases st with
    | none => cases run
    | some st =>
      let P := (T.instantiate G.w pub).program
      change runSegment P fuel (some st) m (bits :: bs) = some rs at run
      rw [runSegment] at run
      cases hx : execute P fuel (P.start st) m bits with
      | none => simp [hx] at run
      | some rep =>
        rw [hx, Option.map_eq_some_iff] at run
        obtain ⟨tail, htail, rfl⟩ := run
        have ⟨ht, hf⟩ := keep rep (by simp) m
        obtain ⟨ls, hls, he, hm, hn, hpres, hcost⟩ := ih (hf.trans data) htail
          (fun a ha => probes a (List.mem_cons_of_mem _ ha))
          (fun a ha => keep a (List.mem_cons_of_mem _ ha))
        let z := prependLog (Frame.loadEvents base m 0 k) rep
        have hwrap := Frame.execute_frame T base st fuel m bits
        dsimp only at hwrap
        rw [data, hx] at hwrap
        have hz := (same st m bits).trans hwrap
        have ⟨_, hp, _, hmem, hres⟩ := Frame.frame_cost base m 0 k rep
        change after m z.events = after m rep.events at hmem
        change z.result = rep.result at hres
        change z.probes = k + rep.probes at hp
        change _ = some z at hz
        refine ⟨z :: ls, ?_, ?_, ?_, by simp [hn], ?_, ?_⟩
        · simp only [runSegment, hz, hmem, hres, hls, Option.map_some]
        · simpa only [endState, hres] using he
        · simpa only [eventLog, List.flatMap_cons, after, List.foldl_append] using
            (hmem ▸ hm : after (after m z.events) (eventLog ls) = after (after m rep.events) (eventLog tail))
        · exact ⟨fun _ => (congrFun hmem _).trans ht, hmem ▸ hpres⟩
        · rw [List.forall_mem_cons]
          have := probes rep (by simp)
          exact ⟨⟨by omega, (execute_spec hz).1.length_lt⟩, hcost⟩

/-- Lift a certified native source run through the physical operand loader
and stage dispatcher, including the transfer tag and the private clock. -/
theorem framedReturning {m : Memory G.w} {n : ℕ} {rs : List (Report G.w)}
    (fit : fuel+4*k+47 ≤ G.clock) (tagged : G.tagged s m) (next : G.nextStage s = some dest)
    (data : Frame.data base m = pub)
    (same : ∀ st mem bits, let C := Pieces.component G.components s G.g G.lit
      let R := (Frame.machine T base).program
      execute C (fuel+4*k) (C.start st) mem bits = execute R (fuel+4*k) (R.start st) mem bits)
    (run : runSegment (T.instantiate G.w pub).program fuel (some 0) m (List.replicate n []) = some rs)
    (halt : endState (some (0 : Word G.w)) rs = none) (hlen : rs.length = n)
    (probes : ∀ rep ∈ rs, rep.probes ≤ b)
    (keep : ∀ rep ∈ rs, ∀ u, after u rep.events G.addr.val = u G.addr.val ∧
      Frame.data base (after u rep.events) = (Frame.data base u : Fin k → Word G.w)) :
    Advice.Returning G.P G.clock n (b+k+2) m
      (writeMemory (after m (eventLog rs)) G.addr (tagWord G.w dest)) := by
  obtain ⟨logs, hr, he, hm, hlen', hframe, hcost⟩ := framedSegment same data run probes keep
  obtain ⟨houter, hend, hmem, _⟩ := G.component_completion fit tagged hframe hr (he.trans halt)
  rw [next] at hend
  rw [next, hm] at hmem
  refine ⟨G.linkedLogs s logs, houter, hend, hmem, by simp [linkedLogs, hlen', hlen], ?_⟩
  intro rep hrep
  obtain ⟨inner, hi, rfl⟩ := List.mem_map.mp hrep
  obtain ⟨hp, hl⟩ := hcost inner hi
  refine ⟨?_, ?_⟩
  · rw [linkedReport_probes]
    split <;> omega
  · have hle := linkedReport_length_le G.nextStage G.addr s inner
    change _ ≤ inner.events.length + 2*21+5 at hle
    omega

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
