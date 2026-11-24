import OAI.Computability.VPVNP.RAMProcessorGraphTerminal
import OAI.Computability.VPVNP.RAMTapeSiteGraphRun
import OAI.Computability.VPVNP.RAMTapeSitePostLink

/-!
# Acceptance of the physical site processor on a fixed private bit string

The call controller and the sorting and memory checks share their record block.
For each private string their linked routine stops on every path and its count
is the acceptance bit of the native incident validator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

set_option synthInstance.maxSize 10000

open BurstRAM PrivateRAM LiveProgram

variable {d e w p k : ℕ}

/-- The controller publishes its output record block at the sorter's input port. -/
def perChoice (r : ℕ) (expr : Fin k → PublicExpr) (T : Template p r k) :
    FiniteRoutine (Port r expr) :=
  ((SiteProcessor.callSite T).onPorts (callPorts r expr)).followedBy (post r expr)

/-- Includes boot, the native graph, the complete sorting pass and a final halt tick. -/
def perChoiceBudget (d e w r fuel : ℕ) : ℕ :=
  (r*(8*w+3)+21*w+14) + SiteCutBank.graphBudget r w e fuel + SitePost.budget d e w 0 + 1

variable (r : ℕ) (expr : Fin k → PublicExpr) (x : SiteCutBank.Input d e w)
    (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool)

private theorem edge_spec : (edges x).Spec x.word_ge_two x.cap_lt x.initialWord x.v x.sends :=
  scanSuccessors_spec x.word_ge_two x.cap_lt x.initialWord x.v (sortIncident x.sends x.v) x.sends
    (sortIncident_offset x.sends x.v)

/-- On a valid pair of successor fields the interpreter first checks the calls
and then checks the emitted records against the incident sorting bits. -/
theorem incident_acceptance (hv : x.valid) :
    ((T.instantiate w pub).validateIncident (x.n^x.u) x.initialWord x.headerWord
      x.word_ge_two x.cap_lt x.v (RAMLayout.incidentBits x.sends x.v) bits).1.isSome.toNat =
      match x.validated T pub bits with
      | none => 0
      | some rs => (checkSiteMemory (e := e) x.word_ge_two x.v x.headerWord
          (sortIncident x.sends x.v) (edges x) rs).1.toNat := by
  have hgood := (edge_spec x).valid_iff.mpr hv
  unfold Machine.validateIncident
  change ((if (edges x).valid then _ else _) : Option (List (Report w)) × ℕ).1.isSome.toNat = _
  rw [ite_eq_left hgood]
  dsimp only
  rw [Machine.runBucket_result]
  conv_lhs =>
    pattern validateSite ..
    change x.validated T pub bits
  cases x.validated T pub bits with
  | none => rfl
  | some rs =>
    dsimp only
    change (if (checkSiteMemory (e := e) x.word_ge_two x.v x.headerWord
      (sortIncident x.sends x.v) (edges x) rs).1 then some rs else none).isSome.toNat = _
    cases (checkSiteMemory (e := e) x.word_ge_two x.v x.headerWord
      (sortIncident x.sends x.v) (edges x) rs).1 <;> rfl

/-- Malformed successor fields reject for every private string. -/
theorem invalid_incident (hv : ¬x.valid) :
    ((T.instantiate w pub).validateIncident (x.n^x.u) x.initialWord x.headerWord
      x.word_ge_two x.cap_lt x.v (RAMLayout.incidentBits x.sends x.v) bits).1 = none := by
  have hbad : ¬ (edges x).valid = true := fun h => hv ((edge_spec x).valid_iff.mp h)
  unfold Machine.validateIncident
  change ((if (edges x).valid then _ else _) : Option (List (Report w)) × ℕ).1 = none
  rw [ite_eq_right hbad]

theorem perChoice_complete (s : Stacks (Port r expr)) (hvalid : x.valid)
    (hbare : s ∘ callPorts r expr = (x.bare T pub bits).bare)
    (hready : PostReady r expr x s) (t : ℕ) (ht : perChoiceBudget d e w r (x.n^x.u) ≤ t) :
    (∀ c, (perChoice r expr T).body.count c t s =
      ((T.instantiate w pub).validateIncident (x.n^x.u) x.initialWord x.headerWord
        x.word_ge_two x.cap_lt x.v (RAMLayout.incidentBits x.sends x.v) bits).1.isSome.toNat) ∧
      (∀ c, (perChoice r expr T).body.AllStops c t s) := by
  rw [incident_acceptance r x T pub bits hvalid]
  obtain ⟨m,hm,booted⟩ := SiteProcessor.boot_run T (x.bare T pub bits) x.addrWord rfl rfl
  change m ≤ r*(8*w+3)+3*(0*(w+1)+1)+2 + (0+0+0+21*w+9) at hm
  change SiteProcessor.boot.Runs m (x.bare T pub bits).bare (x.staged T pub bits).bank at booted
  obtain ⟨n,hn,graph⟩ := x.graphOutcome T pub bits hvalid
  unfold SiteCutBank.Input.GraphOutcome at graph
  unfold perChoiceBudget at ht
  have hp := callPorts_injective r expr
  cases he : x.validated T pub bits with
  | none =>
    rw [he] at graph
    have htime : t = (t-(m+n+1))+(m+n)+1 := by omega
    have bad := SiteProcessor.callSite_reject T booted graph
    constructor
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r expr)).body.followedBy
        (post r expr).body).count c t s = 0
      rw [Routine.count_followedBy, FiniteRoutine.count_onPorts _ _ hp, hbare, htime]
      exact (bad.verdict _ (fun _ _ => True) _).1
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r expr)).body.followedBy
        (post r expr).body).AllStops c t s
      rw [Routine.allStops_followedBy, FiniteRoutine.allStops_onPorts _ _ hp, hbare, htime]
      exact (bad.verdict (fun _ _ => 0) _ _).2
  | some rs =>
    rw [he] at graph
    obtain ⟨u, records, hrecords, run⟩ := graph
    let out := (u.afterClose x.word_ge_two (2^e) records).bank
    have hr : (SiteProcessor.callSite T).Runs (m+n) (x.bare T pub bits).bare out :=
      booted.followedBy (SiteProcessor.graphRoutine_run T run)
    have framed := (SiteProcessor.callSite T).runs_onPorts hp s hr
    rw [installStacks_eq hp s _ (fun i => congrFun hbare i)] at framed
    have htime : t = (t-(m+n))+(m+n) := by omega
    have postVerdict := hready.complete r expr x (fun _ => x.headerWord) (edge_spec x) rs records
      hrecords out rfl (t-(m+n)) (by omega)
    constructor
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r expr)).body.followedBy
        (post r expr).body).count c t s = _
      rw [Routine.count_followedBy, htime, framed.count_eq]
      exact postVerdict.1 c
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r expr)).body.followedBy
        (post r expr).body).AllStops c t s
      rw [Routine.allStops_followedBy, htime, framed.allStops_iff]
      exact postVerdict.2 c

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
