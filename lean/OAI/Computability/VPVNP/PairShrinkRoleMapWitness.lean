import OAI.Computability.VPVNP.PairShrinkHiddenParser
import OAI.Computability.VPVNP.PairSimulationRecordedMapCalls

/-!
# Syntactic acceptance at the resident shrinking maps

Once a parent has chosen its placed old halves and its owned hidden fields,
the remaining kernel choices are exactly the local entry witnesses at its
resident motif parties. Each passing entry has one choice and each failing
entry has none, regardless of the specialized values of the parameters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel LocalHistory
open MotifBlocks MotifConversion MotifGrid MotifDemandPadding MotifSelector
open CompressorRecords

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}

local notation "a" => S.degreeExponent i.castSucc
local notation "b" => S.degreeExponent i.succ
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink)
/-- Classical equality on base vertices for enumerating the resident shrinking maps at a chosen
site. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

private noncomputable abbrev layout :=
  X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth sel

private noncomputable abbrev supplyWidth (motif : X.packingData.Motif) :=
  X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B.shrink motif (sel motif)

private noncomputable abbrev output :=
  let d := 2 ^ S.degreeExponent i.castSucc
  let l := layout B i X sel
  X.packingData.shrinkOutput l (subdivisions d (2 * d + 1) (2 ^ S.degreeExponent i.succ))
    (fun m t => supplyWidth B i X sel m (l, t)) (X.shrinkStateIndex (S.shrink i) l)

local notation "P" => X.packingData
local notation "lay" => layout B i X sel
local notation "width" => supplyWidth B i X sel
local notation "subd" => subdivisions (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b)

variable (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
variable (old : Placed (X.packingData.shrinkPlace (layout B i X sel) ∘ X.packingInputIso.site.symm)
  X.network.Half v)
variable (new : (output B i X sel).Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (layout B i X sel))
  (internalLabel (supplyWidth B i X sel) (layout B i X sel)) v)

private def pullPlaced {N Y : Network} {U : Type} (iso : N.Iso Y) (place : N.Site → U)
    (site : U) (h : Placed (place ∘ iso.site.symm) Y.Half site) : Placed place N.Half site :=
  fun u hu => iso.pullHalf u (h (iso.site u) (by simpa only [Function.comp_apply,
    Equiv.symm_apply_apply] using hu))

/-- Pull the placed old halves back to the coordinates used in the actual motif calls. -/
noncomputable def placedOld :
    Placed ((P).shrinkPlace lay) ((P).oldWireNetwork X.packingWidth).Half v :=
  pullPlaced X.packingInputIso ((P).shrinkPlace lay) v old

set_option maxHeartbeats 2000000 in
-- The six-party coordinates unfold the selected term layout.
/-- The real local demand and supply coordinates, in the selected row's six-party layout. -/
noncomputable def input (q : (P).ResidentMap lay v) : EntryInput B.shrink :=
  ⟨(P).shrinkDemandWidths X.shrinkNumber X.packingWidth q.1.1, (sel q.1.1).val, q.1.2,
    (P).shrinkLocalDemandArg (State.two_le_packingColors a) (Nat.two_pow_pos a)
      X.shrinkNumber X.shrinkOrder X.packingWidth lay q.1.1 q.1.2
      (q.2.symm ▸ placedOld B i X sel v old),
    (P).shrinkLocalSupplyArg lay subd width (X.shrinkStateIndex (S.shrink i) lay)
      (S.shrink i).count_pos q.1.1 q.1.2 (q.2.symm ▸ hidden) (q.2.symm ▸ new)⟩

/-- The label sequence returned by the metered entry interpreter, including repetitions. -/
noncomputable def names (arg : EntryInput B.shrink) :
    Option (List (parameterData B.shrink).Entry) :=
  (runEntry B.shrink demandMass_pos arg.demand arg.payload arg.party
    (MotifEntry.demandBits demandSource demandTarget arg.party arg.demandBits)
    (mapHalf supply (fun _ => MotifEntry.inputBits) arg.supplyBits)).1

private theorem choice_iff {L : Type} [Fintype L] {n : ℕ} (κ : L → R)
    (idx : Option (Fin n → L)) :
    Nonempty (entryWitness κ idx).Choice ↔ (idx.map List.ofFn).isSome = true := by
  cases idx with
  | none => exact ⟨fun ⟨c⟩ => c.elim, by simp⟩
  | some t => exact ⟨fun _ => rfl, fun _ => ⟨()⟩⟩

private theorem choice_subsingleton {L : Type} [Fintype L] {n : ℕ} (κ : L → R)
    (idx : Option (Fin n → L)) : Subsingleton (entryWitness κ idx).Choice := by
  cases idx with
  | none => exact inferInstanceAs (Subsingleton Empty)
  | some t => exact inferInstanceAs (Subsingleton Unit)

local notation "calls" => input B i X sel v old new
local notation "witness" => B.shrinkPassWitnesses f hf i rfl X sel v old new
private noncomputable abbrev index (arg : EntryInput B.shrink) :=
  entry B.shrink demandMass_pos arg.demand arg.payload arg.party arg.demandBits arg.supplyBits
local notation "entries" => fun h q => index B (calls h q)

private theorem names_eq (arg : EntryInput B.shrink) :
    names B arg =
      (entry B.shrink demandMass_pos arg.demand arg.payload arg.party
        arg.demandBits arg.supplyBits).map List.ofFn :=
  runEntry_list B.shrink demandMass_pos arg.demand arg.payload arg.party
    arg.demandBits arg.supplyBits

set_option maxHeartbeats 2500000 in
-- The witness type unfolds the scheduled state reindexing and product of the resident entries.
/-- A fixed hidden assignment extends to exactly one scheduled kernel choice
if and only if all its resident interpreter calls succeed. -/
theorem unique_iff :
    (∃! x : (witness).Choice, x.1 = hidden) ↔
      ∀ q : (P).ResidentMap lay v, (names B (calls hidden q)).isSome = true := by
  let κ := f ∘ Sum.inl
  let idx := entries
  change (∃! x : (h : _) × ((q : (P).ResidentMap lay v) → (entryWitness κ (idx h q)).Choice),
    x.1 = hidden) ↔ _
  constructor
  · rintro ⟨⟨h, maps⟩, rfl, _⟩ q
    rw [names_eq]
    exact (choice_iff κ (idx h q)).mp ⟨maps q⟩
  · intro all
    have exist (q) : Nonempty (entryWitness κ (idx hidden q)).Choice :=
      (choice_iff κ _).mpr (names_eq B (calls hidden q) ▸ all q)
    refine ⟨⟨hidden, fun q => (exist q).some⟩, rfl, ?_⟩
    rintro ⟨h, maps⟩ rfl
    congr 1
    funext q
    exact (choice_subsingleton κ _).allEq ..

set_option maxHeartbeats 2500000 in
-- The chosen kernel is elaborated in the common parameter alphabet.
theorem exists_iff :
    (∃ x : (witness).Choice, x.1 = hidden) ↔
      ∀ q : (P).ResidentMap lay v, (names B (calls hidden q)).isSome = true := by
  constructor
  · rintro ⟨⟨h, maps⟩, rfl⟩ q
    rw [names_eq]
    exact (choice_iff (f ∘ Sum.inl) ((entries) h q)).mp ⟨maps q⟩
  · intro pass
    exact ((unique_iff B f hf i X sel v old new hidden).mpr pass).exists

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
