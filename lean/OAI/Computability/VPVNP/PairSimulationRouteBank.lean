import OAI.Computability.VPVNP.PairSimulationRouteSchedule

/-!
# Fixed instruction bank for the complete cursor routing scan

Seven scheduler instructions, three three-instruction loops, and two
53-instruction field calls run the entire scan. The two exit labels may
be connected to the surrounding leaf program. The standalone table puts
accept and reject at these exits and requires no public data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RouteBank

open BurstRAM BurstRAM.PrivateRAM RouteSchedule

variable {W p r k : ℕ}

/-- Control labels in scheduler, successor, sorting-phase and sorting-step order. -/
abbrev Control := Fin 7 ⊕ Fin 3 ⊕ Fin 3 ⊕ Fin 3

/-- Geometry, address selection, and the field-bit scan of one invocation. -/
abbrev Call := Fin 30 ⊕ Fin 8 ⊕ Fin 15

/-- The two field calls have separate return labels in the surrounding loops. -/
abbrev Body := Control ⊕ Call ⊕ Call

/-- All instruction addresses, followed by the success and failure exits. -/
abbrev Address := Body ⊕ Fin 2

private def callLabels (place : Call → Fin p) : CallLabels p where
  geom i := place (.inl i)
  addr i := place (.inr (.inl i))
  field i := place (.inr (.inr i))

/-- Relocate all internal labels, both exits, and the register bank. -/
def program (loc : Address → Fin p) (reg : Fin 32 ↪ Fin r) : Program p r where
  reg := reg
  pc i := loc (.inl (.inl (.inl i)))
  succ i := loc (.inl (.inl (.inr (.inl i))))
  phase i := loc (.inl (.inl (.inr (.inr (.inl i)))))
  step i := loc (.inl (.inl (.inr (.inr (.inr i)))))
  sCall := callLabels (fun a => loc (.inl (.inr (.inl a))))
  lCall := callLabels (fun a => loc (.inl (.inr (.inr a))))
  yes := loc (.inr 0)
  no := loc (.inr 1)

private def callText (labels : CallLabels p) (reg : Fin 32 ↪ Fin r)
    (done : Fin p) : Call → Instr 1 p r k
  | .inl i => RouteGeometry.instruction labels.geom (RouteCall.geometryRegs reg) (labels.addr 0) i
  | .inr (.inl i) =>
    RouteAddresses.instruction labels.addr (RouteCall.addressRegs reg) (labels.field 0) i
  | .inr (.inr i) => RouteField.instruction labels.field (RouteCall.fieldRegs reg) done i

/-- Literal, word-width-independent instructions with the requested addresses. -/
def text (loc : Address → Fin p) (reg : Fin 32 ↪ Fin r) (a : Address) : Instr 1 p r k :=
  let P := program loc reg
  match a with
  | .inl (.inl (.inl i)) => P.instruction i
  | .inl (.inl (.inr (.inl i))) =>
    RouteLoop.instruction P.succ (reg 3) (reg 2) (reg 23) (P.sCall.geom 0) (P.pc 3) i
  | .inl (.inl (.inr (.inr (.inl i)))) =>
    RouteLoop.instruction P.phase (reg 3) (reg 2) (reg 23) (P.pc 4) (P.pc 6) i
  | .inl (.inl (.inr (.inr (.inr i)))) =>
    RouteLoop.instruction P.step (reg 4) (reg 28) (reg 23) (P.lCall.geom 14) (P.phase 2) i
  | .inl (.inr (.inl a)) => callText P.sCall reg (P.pc 2) a
  | .inl (.inr (.inr a)) => callText P.lCall reg (P.pc 5) a
  | .inr i => if i = 0 then .accept else .reject

private theorem call_linked (M : Machine W p r k) (loc : Call → Fin p) (reg : Fin 32 ↪ Fin r)
    (done : Fin p) (h : ∀ a, M.code (loc a) = (callText (callLabels loc) reg done a).resize W) :
    let L := callLabels loc
    RouteCall.Linked M L.geom L.addr L.field reg done := by
  constructor
  · intro i
    exact (h (.inl i)).trans (RouteGeometry.resize_instruction ..)
  · intro i
    exact (h (.inr (.inl i))).trans (RouteAddresses.resize_instruction ..)
  · intro i
    exact (h (.inr (.inr i))).trans (RouteField.resize_instruction ..)

/-- The relocated body supplies every scheduler and field-call link. The
caller can install its own instructions at the two exit labels. -/
theorem linked (M : Machine W p r k) (loc : Address → Fin p) (reg : Fin 32 ↪ Fin r)
    (h : ∀ a : Body, M.code (loc (.inl a)) = (text loc reg (.inl a)).resize W) :
    (program loc reg).Linked M := by
  constructor
  · intro i
    exact (h (.inl (.inl i))).trans ((program loc reg).resize_instruction i)
  · intro i
    exact (h (.inl (.inr (.inl i)))).trans (RouteLoop.resize_instruction ..)
  · intro i
    exact (h (.inl (.inr (.inr (.inl i))))).trans (RouteLoop.resize_instruction ..)
  · intro i
    exact (h (.inl (.inr (.inr (.inr i))))).trans (RouteLoop.resize_instruction ..)
  · exact call_linked M _ reg _ (fun a => h (.inr (.inl a)))
  · exact call_linked M _ reg _ (fun a => h (.inr (.inr a)))

private def controlLocations : Control ≃ Fin 16 :=
  ((Equiv.refl _).sumCongr (((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

private def callLocations : Call ≃ Fin 53 :=
  ((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv

/-- Numeric program counters 0–121 contain the body. Counters 122 and
123 are the successful and failed exits. -/
def locations : Address ≃ Fin 124 :=
  (((controlLocations.sumCongr ((callLocations.sumCongr callLocations).trans finSumFinEquiv)).trans
    finSumFinEquiv).sumCongr (Equiv.refl _)).trans finSumFinEquiv

/-- Canonical allocation of the scan's 32 register slots and 124 labels. -/
def canonical : Program 124 32 := program locations (Function.Embedding.refl _)

/-- Complete finite program text, with terminal instructions at its exits. -/
def template : Template 124 32 0 :=
  ⟨1, canonical.pc 0, fun i => text locations (Function.Embedding.refl _) (locations.symm i)⟩

/-- Instantiate the same table at any host word width. -/
def machine (W : ℕ) : Machine W 124 32 0 := template.instantiate W Fin.elim0

theorem machine_linked (W : ℕ) : canonical.Linked (machine W) := by
  apply linked
  intro a
  simp [machine, template, Template.instantiate]

theorem machine_entry (W : ℕ) : (machine W).entry = canonical.pc 0 := rfl

theorem machine_yes (W : ℕ) : (machine W).code canonical.yes = .accept := by
  change (text (k := 0) locations (Function.Embedding.refl _) (locations.symm (locations (.inr 0)))).resize W = _
  rw [locations.symm_apply_apply]
  rfl

theorem machine_no (W : ℕ) : (machine W).code canonical.no = .reject := by
  change (text (k := 0) locations (Function.Embedding.refl _) (locations.symm (locations (.inr 1)))).resize W = _
  rw [locations.symm_apply_apply]
  rfl

end PairSimulation.RouteBank

end VPVNP
end Computability
end OAI
