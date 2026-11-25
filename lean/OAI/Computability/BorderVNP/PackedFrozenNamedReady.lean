import OAI.Computability.BorderVNP.PackedFrozenNamedInstall
import OAI.Computability.BorderVNP.PackedFrozenOperands

/-! # The actual selected population rows at the common static seed and old-slot types -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Shortening Shortening.StaticRows DirectoryCircuit

variable {D m rows V seeds n' b w : ℕ} {K : Type*} [Field K] {P A σ : Type} {bits : P → ℕ}
    (e : PaidIdentity K D m) (pop : PublicPopulation.Pins (Fin rows) σ b w) (col : Columns σ rows D w)
    (code : A ↪ Fin (2^b)) (seed : A ≃ Fin seeds) (p : Pack D P bits K)
    (bin : p.layout.Edge → Option A) (orient : p.layout.Edge → Bool)
    (sites : p.layout.Site ↪ Fin V) (slot : p.layout.Edge ↪ Fin rows) (x : σ → Bool)

/-- Changing only the type-level seed count keeps all actual measured fields,
including the pointer to the chosen dummy site at every vacant candidate. -/
theorem ready_reseed (h : seeds = n')
    (source : ∃ dummy, Ready e pop col code seed p bin orient sites slot dummy x) :
    ∃ dummy, Ready e pop col code (seed.trans (finCongr h)) p bin orient sites slot dummy x := by
  cases h
  exact source

end Packing.Inherited.FrozenTape

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.StaticRows Shortening.PublicDenseReceipt
open Epoch Epoch.Round Packing.DirectoryCircuit Packing Packing.Inherited Packing.Inherited.FrozenTape
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1200000

variable {D m b k last high w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    {σ : Type} (select : (r.operands i).Pin → σ) (x : σ → Bool)

local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "O" => r.operands i
local notation3 (prettyPrint := false) "source" => raw (fun j => (c j).val.placed)
local notation3 (prettyPrint := false) "site" => parallelName (fun j => (c j).val.names.sites)
local notation3 (prettyPrint := false) "slot" => (st).slot.trans (finCongr (r.installed i c).capacity).toEmbedding
local notation3 (prettyPrint := false) "words" => (fun z : Fin k × path.StatePins last high V E w i.val => (c z.1).val.words z.2)

set_option backward.isDefEq.respectTransparency false in
/-- The retained selected rows are ready for the literal shared source, using
the same stage-wide seed ordering as the public work and tape circuits. -/
theorem frozen_ready (read : x ∘ select = (O).frame.eval words) :
    (st).perm = (O).perm ∧ ∃ dummy,
      Ready e (mapPins select (O).pop) (mapColumns select (O).col) (O).code (r.directorySeed i)
        source (st).bin (st).positive site slot dummy x := by
  have stage := r.operand_read i c
  refine ⟨stage.1,?_⟩
  have sizes : r.seedCount i = Fintype.card (Shortening.PublicDenseReceipt.Seed (path.pattern i).bins
      (path.asPath.depth last high (i.val+1))) := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (r.seedCode i)).symm
  have sr := ready_reseed e (O).pop (O).col (O).code (r.seedCode i) source (st).bin (st).positive
    site (parallelName fun j => (c j).val.names.cables) ((O).frame.eval words) sizes stage.2
  have ids : parallelName (fun j => (c j).val.names.cables) = slot :=
    DFunLike.ext _ _ fun z => Fin.ext ((r.installed i c).slots z).symm
  rw [ids,← read] at sr
  obtain ⟨dummy,ready⟩ := sr
  exact ⟨dummy,ready_map e select (O).pop (O).col (O).code (r.directorySeed i) source (st).bin (st).positive
    site slot dummy x ready⟩

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
