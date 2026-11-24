import OAI.Computability.VPVNP.PairTreeSelectedFrontier
import OAI.Computability.VPVNP.PairIndexedLevelChecks
import OAI.Computability.VPVNP.PairShrinkRoleDirectory

/-!
# Subtree headroom at each physical shrink and refresh row

The descendant list supplied by the selected traversal agrees at each
chronological output row with the actual child packet order. Replacing
that row by the child packets therefore consumes exactly one unit of
the remaining-vertex allowance.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open NetworkKernel CompressorRecords LocalHistory NodeArguments
open Compression TraversalRows TraversalRoles
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds
open private pushRowAddress uncastRows order_length from OAI.Computability.VPVNP.PairSelectedLevelChecks

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (desc : ℕ → List ℕ)

/-- At every selected output site, the descriptor's descendant list is the concatenation, in
reader order, of each input child's row address followed by that child's descendants. -/
def LevelShape (cap before after : ℕ) (v : SelectedLevel B f hf) : Prop :=
  ∀ u, desc (sitePointers cap after (ShrinkRoleDirectory.outputOrder v) u).1 =
    childAddresses (originReader B f hf v.origin v.term)
      (fun t => (sitePointers cap before (siteOrder v.input) t).1) desc u

private def Shapes (cap : ℕ) : ℕ → List (SelectedLevel B f hf) → Prop
  | _, [] => True
  | base, v::vs => let next := address cap base (siteOrder v.input).length
    LevelShape B f hf desc cap base next v ∧ Shapes cap next vs

private theorem uncastDesc {N Z Y : Network} (e : N = Z) (c : TermChain R Z Y)
    (r : ChainParsers f c) (ptr : RowPointers (e.symm ▸ c : TermChain R N Y)) (addr : N.Site → ℕ)
    (h : DescLayers (e.symm ▸ c : TermChain R N Y) (castParsers e.symm c r) ptr addr desc) :
    DescLayers c r (uncastPointers e c ptr) (pushAddress e addr) desc := by cases e; exact h

private theorem collected_shape {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (K : E.MapWitnesses f) (r : ExecutionReaders E K) (o : PassOrigins B f hf E)
    (records : E.Records) (z : E.Choices) (cap base : ℕ) (origins : ReaderOrigins B f hf E K r o)
    (rows : let c := E.termChain records z
      DescLayers c (branchParsers E K r records z)
        (chainPointers cap c (branchOrders E records z) (address cap base (siteOrder X).length))
        (fun u => (sitePointers cap base (siteOrder X) u).1) desc) :
    Shapes B f hf desc cap base (collectLevels B f hf E K r o z) := by
  induction E generalizing base with
  | done => trivial
  | @more a g a' g' X p tail ih =>
    let e := p.output_eq z.1
    let nextBase := address cap base (siteOrder X).length
    let ord := siteOrder (p.next z.1)
    let d := (tail z.1).termChain (records.2 z.1) z.2
    let ords := branchOrders (tail z.1) (records.2 z.1) z.2
    let rr := branchParsers (tail z.1) (K.2 z.1) (r.2 z.1) (records.2 z.1) z.2
    let idx := z.1
    let current : SelectedLevel B f hf := ⟨a,g,a',g',X,p,o.1,idx,r.1.select.encode idx⟩
    constructor
    · change LevelShape B f hf desc cap base nextBase current
      unfold LevelShape
      rw [← origins.1 idx]
      exact rows.1
    · apply ih idx (K.2 idx) (r.2 idx) (o.2 idx) (records.2 idx) z.2 nextBase (origins.2 idx)
      have tailDesc := uncastDesc B f desc e d rr _ (fun v => (sitePointers cap nextBase
        (e.symm ▸ ord : Order (p.step.term idx).output.Site) v).1) rows.2
      have ptrEq : uncastPointers e d
          (chainPointers cap (e.symm ▸ d : TermChain R (p.step.term idx).output _)
            (show ChainOrders (e.symm ▸ d : TermChain R (p.step.term idx).output _) from by
              exact (branchOrders (.more p tail) records z).2)
            (address cap nextBase ((e.symm ▸ ord : Order (p.step.term idx).output.Site)).length)) =
          chainPointers cap d ords (address cap nextBase ord.length) := by
        rw [order_length e ord]
        exact uncastRows e d ords cap _
      exact Eq.mp (congrArg₂ (fun pp aa => DescLayers d rr pp aa desc) ptrEq
        (pushRowAddress e ord cap nextBase)) tailDesc

private theorem indexShape (cap : ℕ) (vs : List (SelectedLevel B f hf)) (pos : ℕ → ℕ)
    (step : ∀ i : Fin vs.length, pos (i.val + 1) =
      address cap (pos i.val) (siteOrder vs[i].input).length)
    (h : Shapes B f hf desc cap (pos 0) vs) (i : Fin vs.length) :
    LevelShape B f hf desc cap (pos i.val) (pos (i.val + 1)) vs[i] := by
  induction vs generalizing pos with
  | nil => exact Fin.elim0 i
  | cons v vs ih =>
    cases i using Fin.cases with
    | zero => rw [step 0]; exact h.1
    | succ i =>
      apply ih (fun j => pos (j+1)) (fun j => step j.succ) _ i
      have first : pos (0+1) = address cap (pos 0) (siteOrder v.input).length := step 0
      rw [first]
      exact h.2

/-- The full headroom transition at the genuinely indexed native row,
independently of the selected or malformed private suffix. -/
theorem selected_rowShape {n : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T hT X).Choices) (base : ℕ)
    (rows : let E := B.execute f hf T hT X
      let records := B.records f hf T hT X
      let c := E.termChain records z
      DescLayers c (selectedParsers B f hf T hT X z)
        (chainPointers B.recordLimit c (branchOrders E records z)
          (address B.recordLimit base (siteOrder X).length))
        (fun u => (sitePointers B.recordLimit base (siteOrder X) u).1) desc) :
    let passes := executeLevels B f hf T hT X z
    let pos := layerBase B.recordLimit base (selected B f hf T hT X z)
    ∀ i : Fin passes.length, LevelShape B f hf desc B.recordLimit
      (pos i.val) (pos (i.val + 1)) passes[i] := by
  intro passes pos
  apply indexShape B f hf desc B.recordLimit passes pos (selected_level_bases B f hf T hT X z base)
  change Shapes B f hf desc B.recordLimit
    (layerBase B.recordLimit base (selected B f hf T hT X z) 0) passes
  rw [layerBase_zero]
  exact collected_shape B f hf desc _ _ _ _ _ z B.recordLimit base
    (execute_originReaders B f hf T hT X) rows

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
