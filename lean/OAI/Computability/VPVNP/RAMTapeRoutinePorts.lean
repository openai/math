import OAI.Computability.VPVNP.RAMTapeISAPorts

/-! # Preserving the caller's other stacks when running a finite routine -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

variable {K L Q : Type}

/-- Run an existing routine at the caller's physical port names. The control
states, including the normal return, are copied verbatim. -/
def FiniteRoutine.onPorts (r : FiniteRoutine K) (ports : K → L) : FiniteRoutine L :=
  .ofRoutine ⟨r.body.entry, fun q => (r.body.code q).rename ports id⟩

theorem FiniteRoutine.runs_onPorts [DecidableEq K] [DecidableEq L] (r : FiniteRoutine K)
    {ports : K → L} (hp : Function.Injective ports) (base : Stacks L) {t : ℕ} {s out : Stacks K}
    (h : r.Runs t s out) :
    (r.onPorts ports).Runs t (installStacks ports base s) (installStacks ports base out) := by
  have hh (q : Option r.State) (_ : (r.body.standalone q).returns = false) :
      (r.onPorts ports).body.standalone (id q) = (r.body.standalone q).rename ports id := by
    cases q <;> rfl
  exact h.lift ports hp id base hh

theorem installStacks_frame {ports : K → L} (hp : Function.Injective ports)
    {base target : Stacks L} {small : Stacks K} (hin : ∀ k, target (ports k) = small k)
    (hout : ∀ l, (∀ k, ports k ≠ l) → target l = base l) : installStacks ports base small = target := by
  funext l
  by_cases h : ∃ k, ports k = l
  · obtain ⟨k, rfl⟩ := h
    exact (installStacks_at hp base small k).trans (hin k).symm
  · exact (installStacks_outside base small (not_exists.mp h)).trans (hout l (not_exists.mp h)).symm

theorem FiniteRoutine.runs_onPorts_framed [DecidableEq K] [DecidableEq L] (r : FiniteRoutine K)
    {ports : K → L} (hp : Function.Injective ports) {s u : Stacks L} {small out : Stacks K}
    {t : ℕ} (h : r.Runs t small out) (hin : ∀ k, s (ports k) = small k)
    (hu : ∀ k, u (ports k) = out k) (hout : ∀ l, (∀ k, ports k ≠ l) → u l = s l) :
    (r.onPorts ports).Runs t s u := by
  have hrun := r.runs_onPorts hp s h
  rwa [installStacks_frame hp hin (fun _ _ => rfl), installStacks_frame hp hu hout] at hrun

theorem FiniteRoutine.runs_ofStackCode_framed [Fintype Q] [DecidableEq K] [DecidableEq L]
    {src : StackCode K Q} {ports : K → L} (hp : Function.Injective ports) {entry exit : Q}
    {normal : Q → Bool} (he : normal entry = false) (hx : normal exit = true)
    (hs : ∀ q, normal q = true → (src q).returns = true) {s u : Stacks L} {small out : Stacks K}
    {t : ℕ} (h : StackRuns src t entry small exit out) (hin : ∀ k, s (ports k) = small k)
    (hu : ∀ k, u (ports k) = out k) (hout : ∀ l, (∀ k, ports k ≠ l) → u l = s l) :
    (ofStackCode src ports entry normal).Runs t s u := by
  have hrun := runs_ofStackCode hp he hx hs s h
  rwa [installStacks_frame hp hin (fun _ _ => rfl), installStacks_frame hp hu hout] at hrun

end RAMTape

end VPVNP
end Computability
end OAI
