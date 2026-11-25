import OAI.Computability.BorderVNP.TeamSiteTimedRegular
import OAI.Computability.BorderVNP.TeamSiteTimedBoundary

/-! # Framing the repeated timed callback in the physical site bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape TeamPrivateFragment
variable {r k m g : ℕ}
private abbrev Full := Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- Every stack outside the RAM work ports agrees after a complete callback. -/
def Framed (a b : Full (r:=r) (k:=k) (m:=m) (g:=g)) : Prop :=
  ∀ p, (∀ j, loopPort (m:=m) (g:=g) j ≠ p) → b p = a p

theorem Framed.refl (b : Full (r:=r) (k:=k) (m:=m) (g:=g)) : Framed b b := fun _ _ => rfl

theorem Framed.trans {x y z : Full (r:=r) (k:=k) (m:=m) (g:=g)} (h : Framed x y) (j : Framed y z) :
    Framed x z := fun p outside => (j p outside).trans (h p outside)

theorem Framed.meter {x y : Full (r:=r) (k:=k) (m:=m) (g:=g)} {N : ℕ} (h : Framed x y)
    (meter : MeterReady x N) : MeterReady y N :=
  ⟨(h _ (by simp [loopPort])).trans meter.1, (h _ (by simp [loopPort])).trans meter.2.1,
    (h _ (by simp [loopPort])).trans meter.2.2.1, (h _ (by simp [loopPort])).trans meter.2.2.2⟩

/-- Every deterministic phase that touches only RAM ports preserves the same frame. -/
theorem framed_install (b : Full (r:=r) (k:=k) (m:=m) (g:=g)) (s : Stacks (Port r k ((m+1)*g))) :
    Framed b (installStacks loopPort b s) := fun _ absent => installStacks_outside b s absent

/-- Read back the exact RAM work bank at the end of an ordinary installed phase. -/
theorem loop_install (b : Full (r:=r) (k:=k) (m:=m) (g:=g)) (s : Stacks (Port r k ((m+1)*g))) :
    installStacks loopPort b s ∘ loopPort = s := funext (installStacks_at loopPort_injective b s)

/-- The timed native cleanup erases the private burst and all tracks of the RAM work
bank, retaining its previously constructed records and all remaining registers. -/
theorem returned_loop (b : Full (r:=r) (k:=k) (m:=m) (g:=g)) (N : ℕ) :
    installStacks (TeamPrivateMeterCall.wired r k m g) b (TeamPrivateMeterCall.finished N) ∘ loopPort =
      Work.clearPrivate (b ∘ loopPort) := by
  rw [← Work.installPrivate (m:=m+1) (g:=g)]
  funext p
  by_cases present : ∃ j : TeamPrivateInput.NativePort (m+1) g, privateTape j = p
  · obtain ⟨j,rfl⟩ := present
    exact (installStacks_at (TeamPrivateMeterCall.wired_injective r k m g) b
      (TeamPrivateMeterCall.finished N) (.native j)).trans
      (installStacks_at privateTape_injective (b ∘ loopPort) (fun _ => []) j).symm
  · have absent : ∀ j, TeamPrivateMeterCall.wired r k m g j ≠ loopPort p := by
      rintro (_ | _ | _ | _ | j) eq <;> first | cases eq |
        exact present ⟨j,loopPort_injective eq⟩
    exact (installStacks_outside _ _ absent).trans (installStacks_outside (b ∘ loopPort) (fun _ => []) (not_exists.mp present)).symm

/-- The physically restored unary template and empty reset scratch make the completed
native call preserve the entire external caller frame. -/
theorem returned_frame {b : Full (r:=r) (k:=k) (m:=m) (g:=g)} {N : ℕ} (h : MeterReady b N) :
    Framed b (installStacks (TeamPrivateMeterCall.wired r k m g) b (TeamPrivateMeterCall.finished N)) := by
  intro p outside
  by_cases seen : ∃ j, TeamPrivateMeterCall.wired r k m g j = p
  · obtain ⟨j,rfl⟩ := seen
    rw [installStacks_at (TeamPrivateMeterCall.wired_injective r k m g)]
    cases j with
    | template => exact h.1.symm
    | copyScratch => exact h.2.1.symm
    | meterRaw => exact h.2.2.1.symm
    | meterScratch => exact h.2.2.2.symm
    | native j => exact (outside (privateTape j) rfl).elim
  · exact installStacks_outside _ _ (not_exists.mp seen)

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
