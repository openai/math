import OAI.Hierarchy.DescentChronologicalObservedInduction

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open DescentTerminalEpochDecoder Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (path : Path initial current) (state : ℕ→Memory w)
    (resident : ∀{W':MarkedWorld F d P bits} {a b c:ℕ} {r:Reached W' G q ε S k a b c wire hist},Path initial r→Memory w→Prop)
    (flags : ℕ→Bool) (saved count : ℕ→ℕ) (limit : ℕ) (valid : Prop)

/-- The local semantic obligation on the last dated instruction of a selected prefix. -/
def Path.lastObservation : Prop :=by
  cases path with
  | here=>exact resident (.here : Path initial initial) (state 0)
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst ticket=>
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact resident prev (state age) →
      (prev.selections.length< limit → state (age+1) (count age)=(selectionCount G ticket.selection:Computability.VPVNP.BurstRAM.Word w)) ∧
      (valid→flags age=false ∧ state (age+1) (saved age)=((matrixCode rot).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (prev.selections.length+1< limit ∨ valid → resident (prev.ordinary ticket) (state (age+1)))
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    exact resident prev (state age) →
      (valid→flags age=true ∧ state (age+1) (saved age)=((matrixCode closed.frame.basis).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (prev.selections.length< limit ∨ valid → resident (prev.reset closed) (state (age+1)))

omit [Fintype P] in
private theorem append_assoc' {W₃ W₄ : MarkedWorld F d P bits} {i₁ i₂ h₁ h₂ D₁ D₂:ℕ}
    {r:Reached W₃ G q ε S k i₁ h₁ D₁ wire hist} {u:Reached W₄ G q ε S k i₂ h₂ D₂ wire hist}
    (a : Path initial current) (b : Path current r) (c : Path r u) :
    a.append (b.append c)=(a.append b).append c :=by
  induction c with
  | here=>rfl
  | ordinary old t ih=>exact congrArg (fun p=>p.ordinary t) ih
  | reset old close_ ih=>exact congrArg (fun p=>p.reset close_) ih

omit [Fintype P] in
/-- Named stage constructors are specified on cuts of one and the same original
selected history. Their deposited native observations suffice on that history. -/
theorem Path.observations_of_cuts
    (onCut : ∀{U:MarkedWorld F d P bits} {a g δ:ℕ} {r:Reached U G q ε S k a g δ wire hist},
      ∀(«prefix» : Path initial r) (suffix : Path r current),«prefix».append suffix=path →
        «prefix».lastObservation state resident flags saved count limit valid) :
    path.dateReadbacks state flags saved count limit valid ∧
      (path.selections.length< limit ∨ valid → resident path (state i)) :=by
  apply path.observed_induction
  have build {U:MarkedWorld F d P bits} {a g δ:ℕ} {r:Reached U G q ε S k a g δ wire hist}
      («prefix» : Path initial r) (tail : Path r current) (cut : «prefix».append tail=path) :
      «prefix».observedSteps state resident flags saved count limit valid :=by
    induction «prefix» with
    | here=>exact onCut .here tail cut
    | ordinary prev t ih=>
      exact ⟨ih ((Path.here.ordinary t).append tail)
        ((append_assoc' prev (Path.here.ordinary t) tail).trans cut),onCut (prev.ordinary t) tail cut⟩
    | reset prev b ih=>
      exact ⟨ih ((Path.here.reset b).append tail)
        ((append_assoc' prev (Path.here.reset b) tail).trans cut),onCut (prev.reset b) tail cut⟩
  exact build path .here rfl

end
end Hierarchy.DescentSixParty.Chronology

end OAI
