import OAI.Computability.VPVNP.PairShrinkRoleMapWitness
import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.CompressorSlotState

/-!
# Histogram exponents of a scheduled shrinking kernel

Every resident occurrence contributes its whole sequence of returned labels,
including repetitions. Counting these sequences in physical row order gives
the exponent of the corresponding entry in the common parameter alphabet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel LocalHistory
open MotifGrid MotifBlocks MotifConversion CompressorRecords
open CompressorRecords.ShrinkSlots MapResidentRows
open private names_eq from OAI.Computability.VPVNP.PairShrinkRoleMapWitness

variable {a g : ℕ} in
/-- The physical directory order and the resident subtype use opposite
orientations of the same site equality. -/
noncomputable def rowEquiv (Z : State a (packingLaneBits a g)) (side : Bool) (site : Site Z) :
    Fin (order Z side site).length ≃ Z.packingData.ResidentMap side site :=
  (order Z side site).entries.trans (Equiv.subtypeEquivRight fun _ => eq_comm)

variable {R : Type*} [CommRing R]

private theorem entry_count {L : Type} [Fintype L] [DecidableEq L] {n : ℕ} (κ : L → R)
    (idx : Option (Fin n → L)) (x : (entryWitness κ idx).Choice) (l : L) :
    (entryWitness κ idx).exponents x l = ((idx.map List.ofFn).getD []).count l := by
  cases idx with
  | none => exact x.elim
  | some seq =>
    have count := PrivateLabels.count_entry seq (Fintype.equivFin L) l
    rw [List.count_map_of_injective _ _ (Fintype.equivFin L).injective] at count
    exact count.symm

variable {K : Type*} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}
  (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)

private noncomputable local instance countsBase : DecidableEq X.Base := Classical.decEq _

variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)

local notation "W" => B.shrinkPassWitnesses f hf i rfl X sel v old parent
local notation "side" => selectedLayout X B.shrink sel
local notation "call" => input B i X sel v old parent

set_option maxHeartbeats 2000000 in
-- The sum uses the dependent product in the scheduled reindexed witness.
/-- The exponent of one shrinking label is the sum of its multiplicities
over all resident occurrences of the kernel. -/
theorem exponent_count [DecidableEq (parameterData B.shrink).Entry]
    (x : (W).Choice) (label : (parameterData B.shrink).Entry) :
    (W).exponents x (.inl label) = ∑ q : X.packingData.ResidentMap side v,
      ((names B (call x.1 q)).getD []).count label := by
  let κ := f ∘ Sum.inl
  let ix (q : X.packingData.ResidentMap side v) :=
    let arg := call x.1 q
    entry B.shrink demandMass_pos arg.demand arg.payload arg.party arg.demandBits arg.supplyBits
  change (∑ q, (entryWitness κ (ix q)).exponents (x.2 q) label) = _
  apply Finset.sum_congr rfl
  intro q _
  rw [names_eq]
  exact entry_count κ (ix q) (x.2 q) label

/-- The other template's labels have zero exponent in a shrinking witness. -/
theorem refresh_exponent (x : (W).Choice) (label : (parameterData B.refresh).Entry) :
    (W).exponents x (.inr label) = 0 := rfl

/-- Flatten the map-entry label lists in resident directory order for the given choice of
shrinking map calls. -/
noncomputable def emitted (x : (W).Choice) : List (parameterData B.shrink).Entry :=
  (List.ofFn fun j => (names B (call x.1 (rowEquiv X side v j))).getD []).flatten

private theorem count_flatten {L : Type} [DecidableEq L] (rows : List (List L)) (l : L) :
    rows.flatten.count l = (rows.map fun r => r.count l).sum := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatten_cons, List.count_append, ih, List.map_cons, List.sum_cons]

set_option maxHeartbeats 2000000 in
-- Match the physical resident enumeration to the dependent witness product.
/-- The native label stream contributes the exact exponent, with all duplicate
labels from repeated base copies retained. -/
theorem emitted_count [DecidableEq (parameterData B.shrink).Entry]
    (x : (W).Choice) (label : (parameterData B.shrink).Entry) :
    (emitted B f hf i X sel v old parent x).count label = (W).exponents x (.inl label) := by
  rw [emitted, count_flatten, List.map_ofFn, List.sum_ofFn,
    exponent_count B f hf i X sel v old parent]
  exact Fintype.sum_equiv (rowEquiv X side v) _ _ (fun _ => rfl)

set_option maxHeartbeats 2500000 in
-- Summing along the actual row pulls the reindexed witness through the common alphabet.
/-- Counting the fixed finite machine ordinals gives the full scheduled exponent vector. -/
theorem ordinal_sum {t : ℕ} (ord : B.Entry ≃ Fin t) (x : (W).Choice) (label : B.Entry) :
    (∑ j : Fin (order X side v).length,
      (((names B (call x.1 (rowEquiv X side v j))).map (List.map (ord ∘ Sum.inl))).getD []).count
        (ord label)) = (W).exponents x label := by
  classical
  cases label with
  | inl l =>
    rw [exponent_count B f hf i X sel v old parent]
    apply Fintype.sum_equiv (rowEquiv X side v)
    intro j
    cases h : names B (call x.1 (rowEquiv X side v j)) with
    | none => rfl
    | some seq =>
      exact List.count_map_of_injective seq (ord ∘ Sum.inl)
        (ord.injective.comp Sum.inl_injective) l
  | inr l =>
    rw [refresh_exponent B f hf i X sel v old parent]
    apply Finset.sum_eq_zero
    intro j _
    cases h : names B (call x.1 (rowEquiv X side v j)) with
    | none => rfl
    | some seq =>
      apply List.count_eq_zero.mpr
      intro mem
      obtain ⟨a, _, he⟩ := List.mem_map.mp mem
      exact Sum.inl_ne_inr (ord.injective he)

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
