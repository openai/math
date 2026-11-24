import OAI.Computability.VPVNP.PairSimulationLeafValidation
import OAI.Computability.VPVNP.RAMProcessorChoiceCount

/-! # The exact path count of the virtual validator on independent half-wires -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM RAMLayout RAMTape LiveProgram PrivateRAM CursorNetwork CursorRouting
open RAMTape.SiteProcessorPorts

set_option synthInstance.maxSize 10000

variable {d e w k p : ℕ} (r : ℕ) (x : VirtualSite.Input d e w) (args : Fin k → Word w)

/-- The site validator that first checks its guard, generates a bounded choice stream, then
tests that stream against the virtual machine. -/
def processor (T : Template p r k) : FiniteRoutine (Port r k) :=
  (guard r k).followedBy ((stream r k).followedBy (perChoice r (expr k) T))

/-- Step budget for the guard, successor checks, choice generation and per-choice validation at
this site. -/
def steps :=
  perChoiceBudget d e w r x.fuel + (4*choiceBound e w x.fuel+1) +
    3 + Successors.steps d w (decide (0 < x.v.val))

private theorem readyToChoose :
    Function.update (Function.update (guarded r x args) (pub r (expr k) ProcessorPublic.budgetPort)
      (List.replicate (choiceBound e w x.fuel) true)) (native r (expr k) (.test .choices)) [] =
      guarded r x args := by
  have hb := guarded_public r x args ProcessorPublic.budgetPort (by decide)
  have hc := guarded_native r x args (.test .choices)
  change guarded r x args (pub r (expr k) ProcessorPublic.budgetPort) =
    List.replicate (choiceBound e w x.fuel) true at hb
  change guarded r x args (native r (expr k) (.test .choices)) = [] at hc
  rw [← hb, Function.update_eq_self, ← hc, Function.update_eq_self]

variable (T : Template p r k)

/-- Number of incident paths of the instantiated virtual machine for this site's fuel, initial
and header words, and incident bits. -/
noncomputable def pathCount := Nat.card ((T.instantiate w args).IncidentPaths x.fuel x.initialWord x.headerWord
  x.hw x.hc x.v (RAMLayout.incidentBits x.sends x.v))

theorem choices_sum :
    ((ProcessorChoices.words (choiceBound e w x.fuel)).map fun bs => (accepts r x args T bs).toNat).sum =
      pathCount r x args T := by
  let shared := (sendArraysEquiv d (2^e) w).symm x.sends
  have h := ProcessorChoices.site_choices (T.instantiate w args) x.fuel x.initialWord (fun _ => x.headerWord)
    x.hw x.hc shared x.v
  simpa only [BurstRAM.incidentBits, shared, Equiv.apply_symm_apply, pathCount, accepts, choiceBound] using h

private theorem stream_verdict (hv : x.valid) (t : ℕ) (ht : perChoiceBudget d e w r x.fuel ≤ t) :
    let proc := (stream r k).followedBy (perChoice r (expr k) T)
    let clock := t + 4*choiceBound e w x.fuel + 1
    (∀ c, proc.body.count c clock (guarded r x args) = pathCount r x args T) ∧
      (∀ c, proc.body.AllStops c clock (guarded r x args)) := by
  intro proc clock
  let credits := List.replicate (choiceBound e w x.fuel) true
  let creditPort := pub r (expr k) ProcessorPublic.budgetPort
  let streamPort := native r (expr k) (.test .choices)
  have hne : creditPort ≠ streamPort := by simp [creditPort, streamPort, pub, native]
  have rs := readyToChoose r x args
  change Function.update (Function.update (guarded r x args) creditPort credits) streamPort [] = _ at rs
  constructor
  · intro c
    let cont := (perChoice r (expr k) T).body.count c
    have h := ProcessorChoices.count creditPort streamPort hne (guarded r x args) credits cont t
    rw [rs, show credits.length = choiceBound e w x.fuel from List.length_replicate] at h
    change ((stream r k).body.followedBy (perChoice r (expr k) T).body).count c clock _ = _
    rw [Routine.count_followedBy, show (stream r k).body.count cont clock (guarded r x args) = _ from h]
    have per (bs : List Bool) : cont t (Function.update (Function.update (guarded r x args) creditPort [])
        streamPort bs) = (accepts r x args T bs).toNat := (perChoice_verdict r x args T bs hv t ht).1 c
    simp only [per, choices_sum]
  · intro c
    let cont := (perChoice r (expr k) T).body.AllStops c
    have h := ProcessorChoices.allStops_iff creditPort streamPort hne (guarded r x args) credits cont t
    rw [rs, show credits.length = choiceBound e w x.fuel from List.length_replicate] at h
    change ((stream r k).body.followedBy (perChoice r (expr k) T).body).AllStops c clock _
    rw [Routine.allStops_followedBy]
    exact h.mpr fun bs _ => (perChoice_verdict r x args T bs hv t ht).2 c

/-- Every possible guard rejection, nominated finite string, private call, and
sorting pass is counted by the fixed finite stack program. -/
theorem processor_spec (t : ℕ) (ht : steps r x ≤ t) :
    (∀ c, (processor r T).body.count c t (bank r x args) = pathCount r x args T) ∧
      (∀ c, (processor r T).body.AllStops c t (bank r x args)) := by
  classical
  let read := Successors.steps d w (decide (0 < x.v.val))
  let nom := 4*choiceBound e w x.fuel + 1
  let inner := t-(2+read+nom)
  have ht' : perChoiceBudget d e w r x.fuel + nom + 3 + read ≤ t := ht
  have hin : perChoiceBudget d e w r x.fuel ≤ inner := by dsimp [inner]; omega
  have hclock : t = (inner + 4*choiceBound e w x.fuel + 1) + 2 + read := by dsimp [nom,inner] at *; omega
  let proc := (stream r k).followedBy (perChoice r (expr k) T)
  have hi (hv : x.valid) := stream_verdict r x args T hv inner hin
  constructor
  · intro c
    let cont := proc.body.count c
    let close := fun f out => cont f (installStacks (guardPort r k) (bank r x args) out)
    have hg := Successors.checked_shared_count x.hw x.hc x.sends (bank r x args ∘ guardPort r k) x.v x.initialWord
      rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl) close (inner+4*choiceBound e w x.fuel+1)
    change ((guard r k).body.followedBy proc.body).count c t _ = _
    rw [Routine.count_followedBy, guard, FiniteRoutine.count_onPorts _ _ (guardPort_injective r k), hclock]
    dsimp only at hg
    by_cases hv : x.valid
    · rw [ite_eq_left (show SuccessorSendOK _ _ _ _ ∧ SuccessorReceiveOK _ _ _ _ from hv)] at hg
      exact hg.trans ((hi hv).1 c)
    · rw [ite_eq_right (show ¬(SuccessorSendOK _ _ _ _ ∧ SuccessorReceiveOK _ _ _ _) from hv)] at hg
      refine hg.trans ?_
      rw [← choices_sum]
      simp [accepts_invalid r x args T _ hv]
  · intro c
    let cont := proc.body.AllStops c
    let close := fun f out => cont f (installStacks (guardPort r k) (bank r x args) out)
    let rem := inner+4*choiceBound e w x.fuel
    have hg := Successors.checked_shared_allStops x.hw x.hc x.sends (bank r x args ∘ guardPort r k) x.v x.initialWord
      rfl rfl rfl rfl rfl rfl rfl (fun _ _ => rfl) close rem
    change ((guard r k).body.followedBy proc.body).AllStops c t _
    rw [Routine.allStops_followedBy, guard, FiniteRoutine.allStops_onPorts _ _ (guardPort_injective r k)]
    have he : t = rem+3+read := by dsimp [rem]; omega
    rw [he]
    exact hg.mpr fun hv => (hi hv).2 c

section Cursor

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
  (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
  (v : Position d) (buf : Buffers d (2^e) w)

/-- The virtual RAM uses its actual 52 registers and 34 public operands.
After the cursor routing tests, the cursor-zero computation realizes the
initial network factor on the supplied four independent buffers. -/
theorem auxiliary_count [NeZero d] (hz : v.1 = 0)
    (hroute : routeAccept (2^e) w v (readBuffer buf) = true)
    (t : ℕ) (ht : steps 52 (auxiliary D hw hc v buf) ≤ t) :
    let x := auxiliary D hw hc v buf
    (∀ c, (processor 52 PrimedCounter.Program.table).body.count c t (bank 52 x D.pub) =
      Nat.card {bs : List Bool // initialAccept D.machine D.fuel 0 (D.initial v.2) hw hc v buf bs = true}) ∧
      (∀ c, (processor 52 PrimedCounter.Program.table).body.AllStops c t (bank 52 x D.pub)) := by
  intro x
  have h := processor_spec 52 x D.pub PrimedCounter.Program.table t ht
  refine ⟨fun c => (h.1 c).trans (Nat.card_congr ?_), h.2⟩
  apply Equiv.subtypeEquivRight
  intro bs
  change (D.machine.validateIncident D.fuel 0 (D.initial v.2) hw hc v.2
    (RAMLayout.incidentBits (sends v buf) v.2) bs).1.isSome = true ↔ _
  rw [sends_incident]
  simp [initialAccept, hroute, hz]

end Cursor
end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
