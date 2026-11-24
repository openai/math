import OAI.Computability.VPVNP.PairSelectedRowChecks
import OAI.Computability.VPVNP.PairSelectedKernelReaders

/-!
# Checking native row roles at their chronological physical level

The selected-level list stores exactly the origins and profiles used by
the term chain. Its running row base advances by the size of each real
input layer. Checking the two native row contracts at these concrete levels
therefore supplies the whole worker with the corresponding packed records.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments Compression TraversalRows
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open scoped Fin.CommRing

variable {W endAddr : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    (hook : HookParser W endAddr) (valid : List Packet → Scratch W endAddr → Prop)
    (hist : Scratch W endAddr → B.Entry → ℕ) (guard : VisitPath W endAddr → Prop)

/-- The true outgoing state of this level determines the next numerical
header row. The kernel is the concrete shrink or refresh reader named by
the physical origin. -/
def LevelChecks (cap base : ℕ) (v : SelectedLevel B f hf) : Prop :=
  let ptr := sitePointers cap (address cap base (siteOrder v.input).length)
    ((v.pass.output_eq v.term).symm ▸ siteOrder (v.pass.next v.term))
  let source := fun u z => Packet.mk (sitePointers cap base (siteOrder v.input) u).1 (packed v.input u z)
  let target := fun u z => Packet.mk (ptr u).1 (pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z)
  let r := originReader B f hf v.origin v.term
  NodeStep hook valid r ptr source target ∧ EmitsNode valid hist guard r ptr source target

/-- Require both the node-step and emission contracts at each selected level in order,
advancing the row base past that level's input sites before checking the next level. -/
def AllLevelChecks (cap : ℕ) : ℕ → List (SelectedLevel B f hf) → Prop
  | _, [] => True
  | base, v::vs => LevelChecks B f hf hook valid hist guard cap base v ∧
      AllLevelChecks cap (address cap base (siteOrder v.input).length) vs

private theorem pushRowAddress {N Z : Network} (e : N = Z) (o : Order Z.Site) (cap base : ℕ) :
    pushAddress e (fun u => (sitePointers cap base (e.symm ▸ o) u).1) =
      fun u => (sitePointers cap base o u).1 := by cases e; rfl

omit [CommRing R] in
private theorem uncastRows {N Z Y : Network} (e : N = Z) (c : TermChain R Z Y) (o : ChainOrders c) (cap base : ℕ) :
    uncastPointers e c (chainPointers cap (e.symm ▸ c : TermChain R N Y)
      (show ChainOrders (e.symm ▸ c : TermChain R N Y) from by cases e; exact o) base) =
      chainPointers cap c o base := by cases e; rfl

private theorem order_length {N Z : Network} (e : N = Z) (o : Order Z.Site) :
    ((e.symm ▸ o : Order N.Site)).length = o.length := by cases e; rfl

private theorem collected_checks {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (o : PassOrigins B f hf E)
    (records : E.Records) (z : E.Choices) (cap base : ℕ) (origins : ReaderOrigins B f hf E K r o)
    (checked : AllLevelChecks B f hf hook valid hist guard cap base (collectLevels B f hf E K r o z)) :
    let c := E.termChain records z
    let ptr := chainPointers cap c (branchOrders E records z) (address cap base (siteOrder X).length)
    ExecutionChecks hook valid hist guard E K r records z ptr (fun u => (sitePointers cap base (siteOrder X) u).1) := by
  induction E generalizing base with
  | done => trivial
  | @more a g a' g' X p tail ih =>
    let e := p.output_eq z.1
    let nextBase := address cap base (siteOrder X).length
    let ord := siteOrder (p.next z.1)
    let d := (tail z.1).termChain (records.2 z.1) z.2
    let ords := branchOrders (tail z.1) (records.2 z.1) z.2
    let idx := z.1
    let current : SelectedLevel B f hf := ⟨a,g,a',g',X,p,o.1,idx,r.1.select.encode idx⟩
    have first : LevelChecks B f hf hook valid hist guard cap base current := checked.1
    have next := ih idx (K.2 idx) (r.2 idx) (o.2 idx) (records.2 idx) z.2 nextBase (origins.2 idx) checked.2
    constructor
    · unfold PassChecks
      rw [origins.1 idx]
      exact first
    · have casted : uncastPointers e d
          (chainPointers cap (e.symm ▸ d : TermChain R (p.step.term idx).output _)
            (show ChainOrders (e.symm ▸ d : TermChain R (p.step.term idx).output _) from by
              exact (branchOrders (.more p tail) records z).2)
            (address cap nextBase ((e.symm ▸ ord : Order (p.step.term idx).output.Site)).length)) =
          chainPointers cap d ords (address cap nextBase ord.length) := by
        rw [order_length e ord]
        exact uncastRows e d ords cap _
      exact Eq.mpr (congrArg₂ (fun pp aa => ExecutionChecks hook valid hist guard (tail idx) (K.2 idx)
        (r.2 idx) (records.2 idx) z.2 pp aa) casted (pushRowAddress e ord cap nextBase)) next

/-- Each row proof now ranges over the concrete chronological level list,
with its published profile and genuine source/target numerical row bases. -/
theorem selected_checks {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)
    (check : AllLevelChecks B f hf hook valid hist guard B.recordLimit base (executeLevels B f hf T hT X z)) :
    let E := B.execute f hf T hT X
    let records := B.records f hf T hT X
    let c := E.termChain records z
    let r := selectedParsers B f hf T hT X z
    let ptr := chainPointers B.recordLimit c (branchOrders E records z)
      (address B.recordLimit base (siteOrder X).length)
    let addr := fun u => (sitePointers B.recordLimit base (siteOrder X) u).1
    let frames := fromRows c r ptr addr (packed (E.finalState z))
    StepLayers hook valid c r ptr frames.2 frames.1 ∧ EmissionLayers valid hist guard c r ptr frames.2 frames.1 := by
  intro E records c r ptr addr frames
  let readers := repeatReaders (blockReaders B f hf) _ T n (Nat.add_sub_of_le hT).symm X
  let origins := executeOrigins B f hf T hT X
  exact execution_checks hook valid hist guard E _ readers records z ptr addr (execute_readerOrders B f hf T hT X)
    (collected_checks B f hf hook valid hist guard E _ readers origins records z B.recordLimit base
      (execute_originReaders B f hf T hT X) check)

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
