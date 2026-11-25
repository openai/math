import OAI.Computability.BorderVNP.PackedNamedPortSave
import OAI.Computability.BorderVNP.PackedInheritedWorkReceipt
import OAI.Computability.BorderVNP.DiagonalExternalSewFields

/-! # Occupied cable selectors of the actual named successor

A real zero-width cable still appears in the successor directory. Its
public presence bit is independent of every field-width selector.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicRelative Shortening.PublicParallel
open Shortening.StaticRows Shortening.CombiningStep Shortening.PublicEndpoints Packing Inherited CellAddressCircuit
open DirectoryCircuit Diagonal.ExternalSew.FieldExport
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

variable {D m b k np last high w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e)
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "dir" => r.directory i c q
local notation3 (prettyPrint := false) "child" => fun z : Fin k × path.StatePins last high V E w i.val => (c z.1).val.words z.2
local notation3 (prettyPrint := false) "geom" => (nodes i).eval (Sum.elim child (NamedReceipt.word st (r.fits i c) q)) ∘ Sum.inl

local notation3 (prettyPrint := false) "seedN" => Fintype.card (Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1)))

private theorem original_range {D s a lev : ℕ} {P K : Type} {bits : P → ℕ}
    (p saved : PlacedPack D P bits K (Cube D) lev) (rows : Directory p s a) (names : Directory saved s a)
    (stored : saved = p.dense rows.cables) (hn : HEq names rows.dense) :
    Set.range names.cables = Set.range rows.cables := by
  subst saved
  cases eq_of_heq hn
  exact densePublicRows_range p.pack.layout rows.cables

/-- The real presence output of the physical serializer distinguishes every
occupied arithmetic row, including live cables of width zero. -/
theorem resultOccupied (se : E (i.val+1) = edgeCapacity e (k*E i.val) seedN) (a : Fin (edgeCapacity e (k*E i.val) seedN)) :
    (geom) (Sum.inl (Fin.cast se.symm a) : path.StatePins last high V E w (i.val+1)) = true ↔ a ∈ Set.range (r.resultCableRows i c q) := by
  let row := Fin.cast se.symm a
  let saved := r.program.advance i c q
  let pin : path.StatePins last high V E w (i.val+1) := Sum.inl row
  have hw : (geom) pin = saved.val.words pin := congrFun (r.geometry_words i c q) pin
  have oldRange := original_range ((st).result e q) saved.val.placed dir saved.val.names
    (r.stored i c q) (r.saved_names i c q)
  change (geom) pin = true ↔ _
  rw [hw,saved.property.reads.present row,oldRange]
  have ids := (r.directorySeed_spec i c q).2
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,Fin.ext ((ids z).symm.trans (congrArg Fin.val hz))⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z,Fin.ext (ids z)⟩

/-- The public occupancy selector in the same common frame names the exact
image of the unsorted successor cables. -/
theorem sharedResultOccupied (se : E (i.val+1) = edgeCapacity e (k*E i.val) seedN) {τ : Type}
    (select : (path.StatePins last high V E w (i.val+1) ⊕ Bool) → τ) (y : τ → Bool) (wires : y ∘ select = (constants _).eval geom)
    (a : Fin (edgeCapacity e (k*E i.val) seedN)) :
    y (select (.inl (Sum.inl (Fin.cast se.symm a) : path.StatePins last high V E w (i.val+1)))) = true ↔ a ∈ Set.range (r.resultCableRows i c q) := by
  let pin : path.StatePins last high V E w (i.val+1) := Sum.inl (Fin.cast se.symm a)
  have val := congrFun wires (Sum.inl pin)
  change y (select (Sum.inl pin)) = true ↔ _
  simp only [Function.comp_apply,constants_eval,Sum.elim_inl] at val
  exact (congrArg (· = true) val).to_iff.trans (r.resultOccupied i c q se a)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
