import OAI.Computability.VPVNP.PairSelectedLevelChecks
import OAI.Computability.VPVNP.PairTraversalRoles

/-!
# Numerical layer bases in the selected worker contracts

The physical header of an output layer follows the preceding layer's rows.
Its count is the input size of the next selected pass. Thus local proofs can
use the two consecutive indices of the published directory directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory
open NodeArguments Compression TraversalRows
open TraversalRoles
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {W endAddr : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

private noncomputable def mark (v : SelectedLevel B f hf) : TaggedLayer :=
  ⟨levelLayer B f hf v, tagLevel B f hf v⟩

private theorem mark_count (v : SelectedLevel B f hf) :
    (mark B f hf v).layer.count = (siteOrder (v.pass.next v.term)).length := by
  rw [mark,levelLayer_count]
  change Fintype.card (v.pass.next v.term).network.Site = _
  simpa only [Fintype.card_fin] using
    (Fintype.card_congr (siteOrder (v.pass.next v.term)).entries).symm

private theorem indexed_bases {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (o : PassOrigins B f hf E)
    (z : E.Choices) (cap base : ℕ) (prev : TaggedLayer)
    (hprev : prev.layer.count = (siteOrder X).length) :
    let vs := collectLevels B f hf E K r o z
    let tags := prev :: vs.map (mark B f hf)
    ∀ i : Fin vs.length, layerBase cap base tags (i.val + 1) =
      address cap (layerBase cap base tags i.val) (siteOrder vs[i].input).length := by
  induction E generalizing base prev with
  | done => exact fun i => Fin.elim0 i
  | @more a g a' g' X p tail ih =>
    let current : SelectedLevel B f hf := ⟨a,g,a',g',X,p,o.1,z.1,r.1.select.encode z.1⟩
    let vs := collectLevels B f hf (tail z.1) (K.2 z.1) (r.2 z.1) (o.2 z.1) z.2
    let tags := mark B f hf current :: vs.map (mark B f hf)
    change ∀ i : Fin (current::vs).length, layerBase cap base (prev::tags) (i.val + 1) =
      address cap (layerBase cap base (prev::tags) i.val) (siteOrder (current::vs)[i].input).length
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero,Fin.getElem_fin,layerBase_cons,layerBase_zero]
      exact congrArg (address cap base) hprev
    | succ j =>
      simp only [Fin.val_succ,Fin.getElem_fin,List.getElem_cons_succ,layerBase_cons]
      exact ih z.1 (K.2 z.1) (r.2 z.1) (o.2 z.1) z.2 (endPos cap base prev.layer)
        (mark B f hf current) (mark_count B f hf current) j

variable (hook : HookParser W endAddr) (valid : List Packet → Scratch W endAddr → Prop)
    (hist : Scratch W endAddr → B.Entry → ℕ) (guard : VisitPath W endAddr → Prop)

attribute [local irreducible] LevelChecks

private theorem indexed_checks (cap : ℕ) (passes : List (SelectedLevel B f hf)) (pos : ℕ → ℕ)
    (baseStep : ∀ i : Fin passes.length, pos (i.val + 1) =
      address cap (pos i.val) (siteOrder passes[i].input).length)
    (row : ∀ i : Fin passes.length,
      LevelChecks B f hf hook valid hist guard cap (pos i.val) passes[i]) :
    AllLevelChecks B f hf hook valid hist guard cap (pos 0) passes := by
  induction passes generalizing pos with
  | nil => trivial
  | cons v vs ih =>
    constructor
    · exact row 0
    · have next : pos 1 = address cap (pos 0) (siteOrder v.input).length := baseStep 0
      rw [← next]
      exact ih (fun j => pos (j+1)) (fun i => baseStep i.succ) (fun i => row i.succ)

variable {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)

/-- The consecutive input and output bases are the actual two physical
positions of this indexed selected level in the frozen directory. -/
theorem selected_level_bases :
    let vs := executeLevels B f hf T hT X z
    let tags := selected B f hf T hT X z
    ∀ i : Fin vs.length, layerBase B.recordLimit base tags (i.val + 1) =
      address B.recordLimit (layerBase B.recordLimit base tags i.val)
        (siteOrder vs[i].input).length :=
  indexed_bases B f hf _ _ _ _ z B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩ rfl

/-- A check for every physical level index supplies the recursive row
checks used by the accepting-path and malformed-tape inductions. -/
theorem selected_indexed
    (check : let vs := executeLevels B f hf T hT X z
      let tags := selected B f hf T hT X z
      ∀ i : Fin vs.length, LevelChecks B f hf hook valid hist guard B.recordLimit
        (layerBase B.recordLimit base tags i.val) vs[i]) :
    AllLevelChecks B f hf hook valid hist guard B.recordLimit base
      (executeLevels B f hf T hT X z) :=
  by
  let tags := selected B f hf T hT X z
  rw [← layerBase_zero B.recordLimit base tags]
  exact indexed_checks B f hf hook valid hist guard B.recordLimit (executeLevels B f hf T hT X z)
    (layerBase B.recordLimit base tags) (selected_level_bases B f hf T hT X z base) check

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
