import OAI.Computability.NearSquareRoot.PhysicalWalshCompileLaneTools
import OAI.Computability.NearSquareRoot.KernelEffectiveTranspose

/-! # Effective compilation of the child bank split and merge operations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Lanes

open IntegerMultiplication Code KernelEffectiveFamily Filter RegisterSelect

variable {A : Type} [Codec A]

private def segment (x : List Tally × List A) := (Piecework.segment x.1 x.2).1

private theorem segment_easy : Code.Easy (segment (A := A)) :=
  (Piecework.easySegment Easy.fst Easy.snd).fstCompose

/-- All recursive bank-split arities use one register cutoff. The command
family includes a certificate of computation of every emitted program file. -/
theorem split_family : ∀ᶠ R in atTop, Family R (PhysicalWalsh.ChildLanes.split (A := A)) := by
  filter_upwards [eventually_ge_atTop 4, easy_eventually (segment_easy (A := A)),
      easy_eventually (segment_easy (A := List A)),
      easy_eventually (Easy.flatten : Code.Easy (List.flatten (α := Tally))),
      easy_eventually (Easy.flatten.mapping : Code.Easy (List.map (List.flatten (α := A)))),
      KernelEffectiveTranspose.scatter_family ([] : List A)] with R hR cut group flat squash scatter
  have fst' := Family.fixed (P := ℕ) (RegisterWitness.Easy.fst (X := List Tally) (Y := List A) hR)
  have r := Family.mapping hR (repeat_family (X := Tally) hR)
  have widths := (fst'.comp r).comp (Family.fixed flat)
  have t := Family.tally (X := Tally) (by omega : 1 ≤ R) id Computable.id
  have phases := fst'.comp (Family.mapping hR t)
  have blocks := (Family.pair (by omega) widths (Family.fixed (RegisterWitness.Easy.snd (by omega)))).comp
    (Family.fixed cut)
  exact (((Family.pair (by omega) phases blocks).comp (Family.fixed group)).comp scatter).comp (Family.fixed squash)

open private cutRows from OAI.Computability.NearSquareRoot.PhysicalWalshChildLanes

/-- The reverse program is correct on arbitrary ruler packets, including
empty groups or records and zero lanes. -/
theorem merge_family : ∀ᶠ R in atTop, Family R (PhysicalWalsh.ChildLanes.merge (A := A)) := by
  filter_upwards [eventually_ge_atTop 4, easy_eventually (segment_easy (A := A)),
      easy_eventually (Iter.facile ([] : List A)),
      easy_eventually (Easy.ruler (Easy.fst : Code.Easy (Prod.fst (α := List Tally) (β := List (List A))))),
      easy_eventually (Easy.flatten : Code.Easy (List.flatten (α := List A))),
      easy_eventually (Easy.flatten : Code.Easy (List.flatten (α := A))),
      KernelEffectiveTranspose.collect_family ([] : List A)] with R hR sg pick lengths flattenBlocks flat collect
  let S := List Tally × List (List A)
  have j := Family.tally (X := S) (by omega : 1 ≤ R) (Prod.snd (α := ℕ) (β := ℕ)) Computable.snd
  have row := (Family.pair (by omega) (Family.fixed (RegisterWitness.Easy.snd (by omega))) j).comp (Family.fixed pick)
  have v := (Family.pair (by omega) (Family.fixed (RegisterWitness.Easy.fst hR)) row).comp (Family.fixed sg)
  have cuts : Family R (cutRows (A := A)) := listOfFn hR id Computable.id v
  have result := (((Family.pair (by omega) (Family.fixed lengths) cuts).comp collect).comp (Family.fixed flattenBlocks)).comp
    (Family.fixed flat)
  apply result.congr
  intro W x
  have hlen : (cutRows W x).length = W := List.length_ofFn
  have h := KernelEffectiveTranspose.collect_exact ([] : List A) (ruler x.1) (cutRows W x)
  rw [hlen] at h
  exact congrArg (fun m : List (List (List A)) => m.flatten.flatten) h

end PhysicalWalshCompile.Lanes

end NearSquareRoot
end Computability
end OAI
