import OAI.Computability.BorderVNP.TransmissionScan
import OAI.Computability.BorderVNP.TransmissionPinsReplay
import OAI.Computability.BorderVNP.TransmissionPinsEffects

/-! # Inverting the physical transmission bit handlers

Arithmetic address safety alone is assumed. For a sending team, a successful native
return itself establishes equality of the actual source and link words. The only
handler consuming a private bit is the locally shared case.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Whether a fragment has neither stores nor private burst writes. -/
def Code.storeFree : Code → Bool
  | .store .. | .call .. => false
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => a.storeFree && b.storeFree
  | .whileLt _ _ a => a.storeFree
  | _ => true

/-- A store-free returning fragment leaves the entire actual memory unchanged. -/
theorem Runs.memory_eq_of_storeFree {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c s m es t mt} (r : Runs pub macros c s m es t mt) (h : c.storeFree = true) : mt = m := by
  induction r with
  | @atom c s m a t z bits atomic ha hb =>
    cases c <;> simp only [Code.isAtom, Code.storeFree] at atomic h <;> try contradiction
    case binary op d i j =>
      simp only [Code.atom] at ha
      split at ha <;> simp [TeamRAM.Instr.action] at ha
      subst a; rfl
    all_goals simp [Code.atom, TeamRAM.Instr.action] at ha
    all_goals subst a; rfl
  | seq _ _ ih jh =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    exact (jh hr).trans (ih hl)
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    exact ih (by split <;> assumption)
  | whileDone => rfl
  | whileStep _ _ _ ih jh => exact (jh h).trans (ih h)

namespace Transmission

variable {w : ℕ}

/-- Address arithmetic hypotheses for a bit handler. A sender's data check is a
separate assertion that is forced by successful native execution. -/
def Role.addressSafe (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) : Prop :=
  match mode with
  | .sharedHere | .dataHere => True
  | .sendData | .receiveA => (endpoint 10).safeReadOnly w (readings pub) (readings m) (readings s)
  | .receiveB => (endpoint 9).safeReadOnly w (readings pub) (readings m) (readings s)

/-- Choices of one bit interval, empty at every transmitting or receiving endpoint. -/
def Role.bits (mode : Role) (b : Bool) : List Bool := if mode = .sharedHere then [b] else []

/-- A canonical step has precisely the specified choices and physical effects. -/
theorem role_runs_bits (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (b : Bool) (ok : mode.permits pub s m) :
    ∃ es t, Runs pub macros mode.bitCode s m es t (mode.output pub s m b) ∧
      es.flatMap TeamRAM.Event.choices = mode.bits b ∧ sameRange s t ∧ traceCost es ≤ mode.bitCode.slots := by
  by_cases hs : mode = .sharedHere
  · subst mode
    obtain ⟨es,t,r,_,hb,hl⟩ := localShared_runs pub macros s m b
    exact ⟨es,t,r,by simpa [Role.bits] using hb,hl,r.cost_le_slots (by decide)⟩
  · obtain ⟨es,t,r,hc,hl⟩ := role_runs mode pub macros s m b ok
    have hd : mode.bitCode.deterministic = true := by cases mode <;> first | decide | contradiction
    exact ⟨es,t,r, by simpa [Role.bits, hs] using Pins.noChoices r hd, hl, hc⟩

/-- A successful bit-handler return determines its permittedness, its exact memory
update, and its choice string. Sender agreement is inferred from the physical comparison. -/
theorem role_sound (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (safe : mode.addressSafe pub s m) {es t mt}
    (r : Runs pub macros mode.bitCode s m es t mt) :
    let b := (es.flatMap TeamRAM.Event.choices).headD false
    mode.permits pub s m ∧ mt = mode.output pub s m b ∧
      es.flatMap TeamRAM.Event.choices = mode.bits b ∧ sameRange s t ∧ traceCost es ≤ mode.bitCode.slots := by
  let b := (es.flatMap TeamRAM.Event.choices).headD false
  have hp : mode.permits pub s m := by
    cases mode with
    | sendData =>
      have hm := r.memory_eq_of_storeFree (by decide)
      exact ⟨safe, (send_runs_iff pub macros s m safe).mp ⟨es,t, hm ▸ r⟩⟩
    | sharedHere | dataHere | receiveA | receiveB => exact safe
  obtain ⟨fs,u,rr,hbits,hu,hcost⟩ := role_runs_bits mode pub macros s m b hp
  have compat : ∃ tail tail' : List Bool, fs.flatMap TeamRAM.Event.choices ++ tail =
      es.flatMap TeamRAM.Event.choices ++ tail' := by
    rw [hbits, Role.bits]
    by_cases h : mode = .sharedHere
    · simp only [h, ite_true]
      cases he : es.flatMap TeamRAM.Event.choices with
      | nil => exact ⟨[], [b], by simp⟩
      | cons v vs => exact ⟨vs, [], by simp [b, he]⟩
    · exact ⟨es.flatMap TeamRAM.Event.choices, [], by simp [h]⟩
  obtain ⟨u',v',he⟩ := compat
  obtain ⟨etr, eb, em⟩ := DiagonalResidueRAM.unique_returns (by cases mode <;> decide) rr r he
  exact ⟨hp, em.symm, (congrArg (List.flatMap TeamRAM.Event.choices) etr.symm).trans hbits, eb ▸ hu, etr ▸ hcost⟩

end Transmission
end RoutingISA

end BorderVNP
end Computability
end OAI
