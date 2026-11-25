import OAI.Computability.BorderVNP.PackedFrozenHookSection
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.PackedBankInheritedCharges

/-! # Immutable seed and hook source with literal singleton-cell metadata

Two shared Boolean literal pins name each virtual cell by its stable site
ordinal and give every auxiliary region width zero. The physical endpoint
columns and actual expanded tile records alone supply the entire virtual
owner/width input required by the seed and hook section compilers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Views

open Crossing CellAddressCircuit CellAddressPhysical ParseBatchCounts ParseBatchSort VPVNP.VerifierNetwork
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open scoped Classical

variable {D s ne np C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s ne np C d k w σ) (literal : Bool → σ)

/-- The virtual fields use only the successor's actual endpoint pins and two shared literal pins. -/
noncomputable def literalFields : Fields s ne np s d d w σ where
  sites := F.sites
  cells := F.sites
  owner r j := literal ((numberWords d).symm (F.sites r) j)
  ptr := F.ptr
  edgeWidth := F.edgeWidth
  auxWidth _ _ := literal false
  portWidth := F.portWidth

variable {P : Type*} {bits : P → ℕ} (N : Network D P bits) (siteID : N.Site ↪ Fin s)
  (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)

omit [Fintype σ] in
/-- A real represented endpoint directory supplies all the virtual-cell fields in the
same Boolean assignment, even for unoccupied sparse site, wire, and exterior slots. -/
theorem literal_represents (x : σ → Bool) (hl : ∀ b,x (literal b) = b)
    (h : EndpointData N F siteID edgeID portID x) :
    Represents N siteID (fun _ => 0) siteID edgeID portID (literalFields F literal) x := by
  constructor
  · intro v
    simpa only [literalFields,Function.comp_def,hl] using value_encode (F.sites (siteID v))
  · exact h.src
  · exact h.dst
  · exact h.attach
  · exact h.edge
  · intro _; simpa only [literalFields,Function.comp_def,hl] using zero_value w
  · exact h.port
  · exact h.edgeHole
  · intro _ _; simpa only [literalFields,Function.comp_def,hl] using zero_value w
  · exact h.portHole

end Packing.Inherited.Views

namespace Packing.Inherited.HookTape

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile InheritedHook FrozenTape BankSite BankJoint BankPacket CellSparse DirectoryCircuit InheritedBank
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {ns : ℕ} (siteID : N.Site ↪ Fin ns)

/-- Increasing the per-site program metadata only increases the total expanded
records on any tested physical region. -/
private theorem fields_mono (prior payload prior' payload' : N.Site → ℕ)
    (hp : ∀ v, prior v ≤ prior' v) (hw : ∀ v, payload v ≤ payload' v) (test : N.Site → Prop) :
    localRecords N true prior payload test ≤ localRecords N true prior' payload' test := by
  unfold localRecords
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro v _
  by_cases h : test v
  · simp only [h,ite_true,boxCost,recordCost]
    exact Nat.add_le_add (hp _) (Nat.add_le_add_left (hw _) 1)
  · simp [h]

/-- Every singleton virtual cell is contained in its actual owner's tile; a reserved
hole has no records. This applies even when many other sites share the true tile. -/
theorem virtual_capacity {T : Type*} (tile : N.Site → T) (M : ℕ) (prior payload : N.Site → ℕ)
    (cap : ∀ t,localRecords N true prior payload (fun v => tile v = t) ≤ M) (r : Fin ns) :
    localRecords N true prior payload (fun v => siteID v = r) ≤ M := by
  by_cases hr : r ∈ Set.range siteID
  · obtain ⟨v,rfl⟩ := hr
    exact (localRecords_mono N true prior payload (fun u hu => congrArg tile (siteID.injective hu))).trans (cap (tile v))
  · have empty (v : N.Site) : siteID v ≠ r := fun h => hr ⟨v,h⟩
    simp [localRecords,testedWidth,empty]

variable {m old binBits w : ℕ} [NeZero D] {S : Type} [Fintype S] {σ : Type*} [Fintype σ]
variable (pop : PublicPopulation.Pins (Fin old) σ binBits w) (binCode : S ↪ Fin (2^binBits)) (perm : Fin D → Equiv.Perm S)
variable {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {n sites np C d h : ℕ} (seed : S ↪ Fin n)
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ) (literal : Bool → σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w)) (occupied : Fin (edgeCapacity e old n) → σ)
variable (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin old) (bin : p.layout.Edge → Option S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
private noncomputable abbrev dense := densePack p slot
private noncomputable abbrev which := CutCircuit.denseBin p.layout slot bin
private noncomputable abbrev priorID := CutCircuit.denseRows p.layout slot
private noncomputable abbrev orient := positive ∘ (Names.denseSlot p.layout slot).symm
variable (q : Counts e (dense p slot) (which p slot bin) perm)
private noncomputable abbrev G := (output e (dense p slot) (which p slot bin) perm (orient p slot positive) first q).layout
variable (oldSite : (dense p slot).layout.Site ↪ Fin sites) (portID : P ↪ Fin np)
local notation3 "p₀" => dense p slot
local notation3 "b₀" => which p slot bin
local notation3 "old₀" => priorID p slot
local notation3 "or₀" => orient p slot positive
local notation3 "G₀" => G perm e p slot bin positive first q
local notation3 "sID" => siteRows e p₀ oldSite seed
local notation3 "eID" => outputRows e p₀ b₀ perm or₀ first q old₀ seed

/-- The per-site fields used by the seed packet compiler are covered by the
genuine inherited and newly paid record fields of the geometric successor. -/
theorem successor_capacity {T : Type*} (tile : (G₀).Site → T) (prior payload : (p₀).layout.Site → ℕ) (M : ℕ)
    (cap : ∀ t, localRecords G₀ true (nextPrior e p₀ b₀ perm or₀ first q prior)
      (nextPayload e p₀ b₀ perm or₀ first q payload) (fun v => tile v = t) ≤ M) :
    ∀ r,localRecords G₀ true (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun z => bankUses e (blocks (p₀).layout b₀ perm m z.1) (q z.1).val z.2))
      (fun v => sID v = r) ≤ M := by
  apply virtual_capacity G₀ sID tile M
  intro t
  apply (fields_mono G₀ _ _ _ _ ?_ ?_ _).trans (cap t)
  · rintro (oldV | ⟨a,v⟩)
    · exact Nat.le_add_right _ _
    · exact Nat.zero_le _
  · rintro (oldV | ⟨a,(_ | t | ⟨i,v⟩)⟩)
    · exact Nat.le_add_right _ _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.le_mul_of_pos_right _ (by omega)

/-- The actual endpoint directory and true expanded physical tile cap give
the complete seed/hook receipt using only shared literal pins for virtual
ownership and auxiliary widths. -/
theorem virtualSourceData {T : Type*} (tile : (G₀).Site → T) (x : σ → Bool) (lit : ∀ b,x (literal b) = b)
    (prior payload : (p₀).layout.Site → ℕ) (M B : ℕ)
    (hpop : PublicPopulation.Represents pop p.layout bin slot binCode x) (widths : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z)
    (bins : ∀ a,count p.layout bin a ≤ B) (ends : Views.EndpointData G₀ F sID eID portID x)
    (enabled : ∀ r,x (occupied r) = true ↔ r ∈ Set.range eID)
    (hist : ∀ a i,value (fun j => counts.eval x (a,i,j)) = i.elim (blocks (p₀).layout b₀ perm m a) (q a).val)
    (cap : ∀ t,localRecords G₀ true (nextPrior e p₀ b₀ perm or₀ first q prior)
      (nextPayload e p₀ b₀ perm or₀ first q payload) (fun v => tile v = t) ≤ M)
    (room : sourceRoom e first M B < 2^w) :
    SourceData pop binCode perm e seed (Views.literalFields F literal) counts occupied p slot bin positive first q
      oldSite portID sID (fun _ => 0) x prior payload M B :=
  ⟨hpop,widths,bins,Views.literal_represents F literal G₀ sID eID portID x lit ends,enabled,hist,
    successor_capacity perm e seed p slot bin positive first q oldSite tile prior payload M cap,room⟩

end Packing.Inherited.HookTape

end BorderVNP
end Computability
end OAI
