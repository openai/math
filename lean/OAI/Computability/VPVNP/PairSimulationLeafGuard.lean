import OAI.Computability.VPVNP.PairSimulationLeafStartup
import OAI.Computability.VPVNP.RAMTapeSuccessorTotal
import OAI.Computability.VPVNP.RAMProcessorChoices
import OAI.Computability.VPVNP.RAMTapeSitePostPorts

/-! # Successor fields and the private choice bank of a virtual validator -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM RAMLayout RAMTape LiveProgram PrivateRAM
open RAMTape.SiteProcessorPorts

set_option synthInstance.maxSize 10000

variable {d e w k r p : ℕ}

/-- Map a successor-check port into the leaf processor's cut-register bank. -/
def guardPort (r k : ℕ) : Successors.Port → Port r k :=
  cut r (expr k) ∘ SiteCutBank.ports

theorem guardPort_injective (r k : ℕ) : Function.Injective (guardPort r k) :=
  (cut_injective r _).comp SiteCutBank.ports_injective

/-- The successor check with its ports assigned to the leaf's cut-register bank. -/
def guard (r k : ℕ) : FiniteRoutine (Port r k) := Successors.checked.onPorts (guardPort r k)

/-- The choice-generation routine that reads the processor's public budget and fills its
private choice stack. -/
def stream (r k : ℕ) : FiniteRoutine (Port r k) :=
  .ofRoutine (ProcessorChoices.routine (pub r (expr k) ProcessorPublic.budgetPort)
    (native r (expr k) (.test .choices)))

variable (r : ℕ) (x : VirtualSite.Input d e w) (args : Fin k → Word w)

/-- The successor-port stacks after finishing the incident record and computing the guard
verdict for the virtual site. -/
def finished : Stacks Successors.Port :=
  Successors.guardResult (Successors.sharedFinish x.hc x.sends x.v (bank r x args ∘ guardPort r k))

/-- The leaf's initial stack bank with the results of the successor guard installed on its
assigned ports. -/
noncomputable def guarded : Stacks (Port r k) :=
  installStacks (guardPort r k) (bank r x args) (finished r x args)

/-- The stack bank at interpreter entry, with the generated bits on the choice port and the
spent public budget cleared. -/
noncomputable def entered (bits : List Bool) : Stacks (Port r k) :=
  Function.update (Function.update (guarded r x args) (pub r (expr k) ProcessorPublic.budgetPort) [])
    (native r (expr k) (.test .choices)) bits

theorem guarded_at (i : Successors.Port) :
    guarded r x args (guardPort r k i) = finished r x args i :=
  installStacks_at (guardPort_injective r k) _ _ i

theorem guarded_native (i : SiteProcessor.Port r k) :
    guarded r x args (native r (expr k) i) = bank r x args (native r (expr k) i) :=
  installStacks_outside _ _ (fun j => Ne.symm (native_ne_cut r _ i (SiteCutBank.ports j)))

theorem guarded_public (i : ProcessorPublic.Port) (hi : i ≠ ProcessorPublic.incidentPort) :
    guarded r x args (pub r (expr k) i) = bank r x args (pub r (expr k) i) := by
  by_cases h : ∃ j, SiteCutBank.ports j = Sum.inl i
  · obtain ⟨j,hj⟩ := h
    change guarded r x args (cut r _ (.inl i)) = bank r x args (cut r _ (.inl i))
    rw [← hj, show cut r (expr k) (SiteCutBank.ports j) = guardPort r k j from rfl, guarded_at]
    cases j with
    | address | width | cap | initial | tmp | capTmp =>
      simp only [finished, Successors.guardResult, Successors.sharedFinish, Successors.finish,
        Successors.afterNormalize]
      split <;> rfl
    | incident => exact (hi (Sum.inl.inj hj).symm).elim
    | outPresent | running | verdict | record | word => contradiction
  · exact installStacks_outside _ _ (fun j hh => h ⟨j,cut_injective r _ hh⟩)

theorem entered_native (bits : List Bool) (i : SiteProcessor.Port r k) :
    entered r x args bits (native r (expr k) i) =
      if i = .test .choices then bits else bank r x args (native r (expr k) i) := by
  by_cases hi : i = .test .choices
  · subst i; simp [entered]
  · rw [entered, Function.update_of_ne (by simpa [native] using hi),
      Function.update_of_ne (by simp [native, pub]), guarded_native, ite_eq_right hi]

theorem entered_public (bits : List Bool) (i : ProcessorPublic.Port)
    (hb : i ≠ ProcessorPublic.budgetPort) (hi : i ≠ ProcessorPublic.incidentPort) :
    entered r x args bits (pub r (expr k) i) = bank r x args (pub r (expr k) i) := by
  rw [entered, Function.update_of_ne (by simp [pub, native]), Function.update_of_ne (by simpa [pub] using hb),
    guarded_public r x args i hi]

theorem entered_guard (bits : List Bool) (i : Successors.Port) :
    entered r x args bits (guardPort r k i) = finished r x args i := by
  have hn : guardPort r k i ≠ native r (expr k) (.test .choices) :=
    (native_ne_cut r (expr k) (.test .choices) (SiteCutBank.ports i)).symm
  have hb : guardPort r k i ≠ pub r (expr k) ProcessorPublic.budgetPort := by
    intro h
    have he := cut_injective r (expr k) (show cut r _ (SiteCutBank.ports i) = cut r _ (.inl ProcessorPublic.budgetPort) from h)
    exact (by decide : ∀ j, SiteCutBank.ports j ≠ .inl ProcessorPublic.budgetPort) i he
  rw [entered, Function.update_of_ne hn, Function.update_of_ne hb, guarded_at]

theorem registers (hv : x.valid) :
    Successors.CutRegisters (bank r x args ∘ guardPort r k) (finished r x args) x.hw x.summary
      ((List.ofFn (RAMLayout.incidentBits x.sends x.v)).drop (16*w)) :=
  Successors.guarded_cutRegisters x.hw x.hc x.initialWord x.sends x.v _ rfl hv.1 hv.2

theorem cost_at (hv : x.valid) (side : Successors.Side) :
    finished r x args (.word side 1) = wordBits (x.sideWord side) := by
  obtain ⟨z,hz,he⟩ := (registers r x args hv).cost side
  exact hz.trans (congrArg wordBits (Fin.ext (he.trans (x.sideWord_val side).symm)))

/-- The interpreter receives every decoded cut, all public words, and the
generated bit string on the same ports used by its actual graph. -/
theorem entered_call (T : Template p r k) (hv : x.valid) (bits : List Bool) :
    entered r x args bits ∘ callPorts r (expr k) = (x.bare T args bits).bare := by
  have hn := entered_native r x args bits
  have hp := entered_public r x args bits
  have ha := entered_guard r x args bits
  have regs := registers r x args hv
  funext i
  change entered r x args bits (callPorts r (expr k) i) = _
  cases i with
  | isa i =>
    cases i with
    | persistent => exact (ha _).trans (regs.state .receive)
    | logPort q => cases q <;> exact hn _
    | reg | pub | work => exact hn _
  | credit i =>
    cases i with
    | publicH | publicFuel | globalCap => exact hp _ (by decide) (by decide)
    | budget j =>
      cases j with
      | site => exact hp _ (by decide) (by decide)
      | cost => exact (ha _).trans (cost_at r x args hv .receive)
      | fuel | call | globalLeft | tmp => exact hn _
    | savedStart | ordinal | copyA | copyB | arithA | arithB => exact hn _
  | test i =>
    cases i with
    | word j =>
      cases j with
      | lower | boundary => exact hp _ (by decide) (by decide)
      | targetCost => exact (ha _).trans (cost_at r x args hv .send)
      | targetState => exact (ha _).trans (regs.state .send)
      | cost | cap | state => exact hn _
    | bit j =>
      cases j with
      | running => exact (ha _).trans (regs.running .receive)
      | hasTarget => exact (ha _).trans regs.outPresent
      | targetRunning => exact (ha _).trans (regs.running .send)
    | choices | verdict | left | right | tmp | out | sourceTmp | copyTmp => exact hn _
  | record i =>
    cases i with
    | field j =>
      fin_cases j
      · exact hn _
      · exact hp _ (by decide) (by decide)
      · exact hp _ (by decide) (by decide)
      · exact hn _
      · exact hn _
    | zeros => exact (hp _ (by decide) (by decide)).trans (UnaryWord.zeros_wordBits w).symm
    | remaining => exact hp _ (by decide) (by decide)
    | temp | reverseBuffer | output => exact hn _
  | scratch j => exact hn _

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
