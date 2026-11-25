import OAI.Hierarchy.DescentChronologicalWordReads

namespace OAI
/-! # Following the actual accepted prefix through its first failed ordinary ballot -/
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

/-- The state must continue past an ordinary instruction precisely when another
ballot will be inspected or the complete tape is accepted. A count on the first
invalid ballot therefore makes no use of its successor's data. -/
def Path.observedSteps : Prop :=by
  induction path with
  | here=>exact resident (.here : Path initial initial) (state 0)
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst ticket ih=>
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact ih ∧ (resident prev (state age) →
      (prev.selections.length< limit → state (age+1) (count age)=(selectionCount G ticket.selection:Computability.VPVNP.BurstRAM.Word w)) ∧
      (valid→flags age=false ∧ state (age+1) (saved age)=((matrixCode rot).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (prev.selections.length+1< limit ∨ valid → resident (prev.ordinary ticket) (state (age+1))))
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    exact ih ∧ (resident prev (state age) →
      (valid→flags age=true ∧ state (age+1) (saved age)=((matrixCode closed.frame.basis).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      (prev.selections.length< limit ∨ valid → resident (prev.reset closed) (state (age+1))))

omit [Fintype P] in
theorem Path.observed_induction (steps : path.observedSteps state resident flags saved count limit valid) :
    path.dateReadbacks state flags saved count limit valid ∧
      (path.selections.length< limit ∨ valid → resident path (state i)) :=by
  induction path with
  | here=>exact ⟨True.intro,fun _=>steps⟩
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst ticket ih=>
    obtain ⟨prior,active⟩:=ih steps.1
    refine ⟨⟨prior,fun seen=>(steps.2 (active (.inl seen))).1 seen,
      fun accepted=>(steps.2 (active (.inr accepted))).2.1 accepted⟩,?_⟩
    intro later
    have next : prev.selections.length+1< limit ∨ valid:=by
      simpa only [Path.selections,List.length_append,List.length_singleton] using later
    have now : prev.selections.length< limit ∨ valid :=
      next.imp_left (fun h=>(Nat.lt_succ_self _).trans h)
    exact (steps.2 (active now)).2.2 next
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    obtain ⟨prior,active⟩:=ih steps.1
    exact ⟨⟨prior,fun accepted=>(steps.2 (active (.inr accepted))).1 accepted⟩,
      fun required=>(steps.2 (active required)).2 required⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
