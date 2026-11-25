import OAI.Optimization.LinearProgramming.PriceGame.LearningRawMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedNormalize
import OAI.Optimization.LinearProgramming.PriceGame.LearningGeneratorWire
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingRows
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSupport
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostSource
import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdSkeletons
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignData

/-! # Compiling the complete historical expert batch of the public price-game campaign

The binary program reads the unary dimension supplied by the campaign prelude, the
binary radius and the packed probe history. It constructs each skeleton, extracts all
historical comparisons, computes one centered representative per feasible comparison
cell, and writes the complete ordered list of packed experts. The order agreement makes
the entry offsets used by the source fixed-share updates available without relabeling.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram Control Control.Wire

abbrev BatchInput := ℕ × (ℕ × List PackedProbe)

def batchInputCode : BatchInput → List Bool := prodCode unaryCode (prodCode Nat.bits (listCode packedProbeCode))

private abbrev oneCode := prodCode packedExpertCode batchInputCode

/-- All assignments for one packed public skeleton in this trial. -/
def localBatch (N R : ℕ) (ps : List PackedProbe) (s : PackedExpert) : List PackedExpert :=
  let roots := packedSupport s
  let rows := groupRows roots (packedHistoryTests s ps)
  let values := GenerationCost.generatorAnswer (generatorParameters (roots,R,rows))
  values.map fun v => withRaw s (expandRaw N roots v)

noncomputable def localBatchP : Procedure oneCode (listCode packedExpertCode)
    (fun x => localBatch x.2.1 x.2.2.1 x.2.2.2 x.1) := by
  let s := Procedure.first packedExpertCode batchInputCode
  let rem := Procedure.second packedExpertCode batchInputCode
  let data := prodCode Nat.bits (listCode packedProbeCode)
  let n := (Procedure.first unaryCode data).comp rem
  let tail := (Procedure.second unaryCode data).comp rem
  let r := (Procedure.first Nat.bits (listCode packedProbeCode)).comp tail
  let probes := (Procedure.second Nat.bits (listCode packedProbeCode)).comp tail
  let roots := packedSupportP.comp s
  let tests := packedHistoryTestsP.comp (s.pair probes)
  let rows := groupRowsP.comp (roots.pair tests)
  let compact := generatorFromRootsP.comp (roots.pair (r.pair rows))
  let contextCode := prodCode unaryCode (prodCode packedExpertCode (listCode Nat.bits))
  let context := n.pair (s.pair roots)
  let item := Procedure.first (listCode ratCode) contextCode
  let ctx := Procedure.second (listCode ratCode) contextCode
  let rest := (Procedure.second unaryCode (prodCode packedExpertCode (listCode Nat.bits))).comp ctx
  let fullN := (Procedure.first unaryCode (prodCode packedExpertCode (listCode Nat.bits))).comp ctx
  let base := (Procedure.first packedExpertCode (listCode Nat.bits)).comp rest
  let names := (Procedure.second packedExpertCode (listCode Nat.bits)).comp rest
  let raw := expandRawP.comp (fullN.pair (names.pair item))
  let annotate := withRawP.comp (base.pair raw)
  exact (GenerationCost.mapContextP ([] : List ℚ) (default : PackedExpert) annotate).comp (compact.pair context)

private theorem history_for_shape {N} (s : Skeleton N) (ps : List PackedProbe) :
    packedHistoryTests (Cold.packShape s) ps = (((ps.map (unpackProbe N)).flatMap s.testsAt).map packTest) := by
  let e : Expert N := ⟨s,fun _ => 0⟩
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change packedTests (packExpert e) p ++ packedHistoryTests (Cold.packShape s) ps = _
    rw [packedTests_correct_unpacked e p,ih]
    simp [e,List.map_append]

private theorem canonical_generator {N} (s : Skeleton N) (R : ℕ)
    (f : Experts.Feature (s.sources.card+1) → Finset ℚ) :
    GenerationCost.generatorAnswer (generatorParameters (canonicalSupport s,R,GenerationCost.historyRows f)) =
      (Experts.generate R 0 f).map List.ofFn := by
  let p : Fin 66 := ⟨s.sources.card,by have := Skeleton.card_sources_le s; omega⟩
  have h : arityOfRoots (canonicalSupport s) = p := by
    apply Fin.ext
    simp [arityOfRoots,canonicalSupport,p,Nat.min_eq_left (Skeleton.card_sources_le s)]
  change GenerationCost.generatorAnswer ⟨arityOfRoots (canonicalSupport s), R, GenerationCost.historyRows f⟩ = _
  rw [h]
  exact congrArg (List.map List.ofFn) (GenerationCost.generateWire_eq_generate (R := R) 0 (Skeleton.card_sources_le s) f)

/-- The local typed batch and the physical batch agree including entry order and all
coordinates of every saved raw assignment. -/
theorem localBatch_correct {N} (R : ℕ) (s : Skeleton N) (ps : List PackedProbe) :
    localBatch N R ps (Cold.packShape s) = (Pool.forSkeleton R s (ps.map (unpackProbe N))).map packExpert := by
  have hs : packedSupport (Cold.packShape s) = canonicalSupport s :=
    packedSupport_pack (⟨s,fun _ => 0⟩ : Expert N)
  simp only [localBatch,hs,history_for_shape,groupRows_correct,canonical_generator,Pool.forSkeleton,List.map_map]
  apply List.map_congr_left
  intro v _
  change withRaw (Cold.packShape s) (expandRaw N (canonicalSupport s) (List.ofFn v)) = _
  rw [expandRaw_correct,Cold.packShape_eq s (fun _ => 0)]
  rfl

/-- The bit program used by the campaign; its blank raw fields in the cold-start templates
are replaced with actual full arrays at every generation. -/
noncomputable def batchP : Procedure batchInputCode (listCode packedExpertCode)
    (fun x => packedBatch x.1 x.2.1 x.2.2) := by
  let n := Procedure.first unaryCode (prodCode Nat.bits (listCode packedProbeCode))
  let skeletons := Cold.coldSkeletonsP.comp n
  let grouped := (GenerationCost.mapContextP (default : PackedExpert) ([] : List PackedExpert) localBatchP).comp
    (skeletons.pair (Procedure.identity batchInputCode))
  apply ((GenerationCost.flattenP packedExpertCode (default : PackedExpert)).comp grouped).congrFun
  rintro ⟨N,R,ps⟩
  change ((Cold.coldSkeletons N).map (localBatch N R ps)).flatten = packedBatch N R ps
  simp only [Cold.coldSkeletons,packedBatch,Pool.batch,List.map_map,List.map_flatMap]
  change (Skeleton.enumerate N).flatMap (fun s => localBatch N R ps (Cold.packShape s)) = _
  apply List.flatMap_congr
  intro s _; exact localBatch_correct R s ps

/-- Direct comparator-machine trace for the complete batch operation. -/
theorem batch_computesWithin (o : OracleSpec.WordOracle) (x : BatchInput) :
    (OracleSpec.BitCode.deploy batchP).ComputesWithin o (batchInputCode x)
      (3 * batchP.bound.eval (batchInputCode x).length + 2 * (batchInputCode x).length + 2)
      (fun history bits => history = [] ∧ bits = listCode packedExpertCode (packedBatch x.1 x.2.1 x.2.2)) :=
  OracleSpec.BitCode.deploy_correct batchP o x

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
