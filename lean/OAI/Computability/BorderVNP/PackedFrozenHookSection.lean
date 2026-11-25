import OAI.Computability.BorderVNP.PackedFrozenHookSaved
import OAI.Computability.BorderVNP.PackedFrozenTapeSections
import OAI.Computability.BorderVNP.PackedInheritedSeedPacket

/-! # Executable terminal-hook section on a sewn successor

A single physical tile capacity and a bound on the predecessor's bin populations
cover every immutable profile prefix and clipped hook address, even for empty
clipped bands. The compiled tape contributes its exact hook suffix at terminals
and the empty list at all other successor sites.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.HookTape

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile InheritedHook FrozenTape BankSite BankJoint BankPacket CellSparse DirectoryCircuit
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m old binBits w : ℕ} [NeZero D] {S : Type} [Fintype S] {σ : Type*} [Fintype σ]
variable (pop : PublicPopulation.Pins (Fin old) σ binBits w) (binCode : S ↪ Fin (2^binBits))
variable (perm : Fin D → Equiv.Perm S)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))

variable {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {n sites np C d h : ℕ} (seed : S ↪ Fin n)
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (occupied : Fin (edgeCapacity e old n) → σ)
variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin old)
variable (bin : p.layout.Edge → Option S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)

private noncomputable abbrev dense := densePack p slot
private noncomputable abbrev which := CutCircuit.denseBin p.layout slot bin
private noncomputable abbrev priorID := CutCircuit.denseRows p.layout slot
private noncomputable abbrev orient := positive ∘ (Names.denseSlot p.layout slot).symm
variable (q : Counts e (dense p slot) (which p slot bin) perm)
private noncomputable abbrev G := (output e (dense p slot) (which p slot bin) perm (orient p slot positive) first q).layout
variable (oldSite : (dense p slot).layout.Site ↪ Fin sites) (portID : P ↪ Fin np)
variable (cell : (G perm e p slot bin positive first q).Site → Fin C)
variable (aux : (G perm e p slot bin positive first q).Site → ℕ)

local notation3 "p₀" => dense p slot
local notation3 "b₀" => which p slot bin
local notation3 "old₀" => priorID p slot
local notation3 "or₀" => orient p slot positive
local notation3 "G₀" => G perm e p slot bin positive first q
local notation3 "sID" => siteRows e p₀ oldSite seed
local notation3 "eID" => outputRows e p₀ b₀ perm or₀ first q old₀ seed

/-- Actual terminal hook suffix of a sewn site, empty at each other site kind. -/
noncomputable def records (v : (G₀).Site) : List Record :=
  match v with
  | .inr ⟨a,.inr (.inl t)⟩ => InheritedProfile.hookRows e p₀ b₀ perm or₀ first q a sID eID portID
      (fun a => (binCode a).val) t
  | _ => []

/-- The numerical room shared by the main seed packet emitter and the independent
hook suffix. The latter's clipped ordinal can reach the entire original bin count. -/
noncomputable def sourceRoom (e : PaidIdentity K D m) (first : Fin D × Bool) (M B : ℕ) : ℕ :=
  BankJoint.addressCoefficient e first*(BankCharges.bound e*M+M+1)+B

omit [NeZero D] in
/-- The one public numerical bound supplies both emitter fits and unit-tag room. -/
theorem sourceRoom_fits (M B : ℕ) (hf : sourceRoom e first M B < 2^w) :
    BankJoint.addressCoefficient e first*(BankCharges.bound e*M+M+1) < 2^w ∧
      BankCharges.bound e*M+M+B < 2^w ∧ 1 < 2^w := by
  have hpos : 0 < BankJoint.addressCoefficient e first := by unfold BankJoint.addressCoefficient; omega
  have hle := Nat.le_mul_of_pos_left (BankCharges.bound e*M+M+1) hpos
  unfold sourceRoom at hf
  omega

/-- One physical receipt on the genuine saved precursor and sewn successor.
Population widths, profile histogram entries, edge occupancy and stable
addresses are all observations of the concrete input assignment. -/
structure SourceData (x : σ → Bool) (prior payload : (p₀).layout.Site → ℕ) (M B : ℕ) : Prop where
  /-- Real predecessor bin labels, occupied slots and their widths. -/
  population : PublicPopulation.Represents pop p.layout bin slot binCode x
  /-- Width of each actual old cable. -/
  widths : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z
  /-- Simultaneous upper bound on actual old bin populations. -/
  bins : ∀ a,count p.layout bin a ≤ B
  /-- Actual successor owner, incidence and width columns. -/
  geometry : Represents G₀ cell aux sID eID portID F x
  /-- Every successor edge and only a true successor edge is enabled. -/
  enabled : ∀ k,x (occupied k) = true ↔ k ∈ Set.range eID
  /-- Both the per-seed multiplicity and each accepted histogram component. -/
  histogram : ∀ a i,value (fun k => counts.eval x (a,i,k)) = i.elim (blocks (p₀).layout b₀ perm m a) (q a).val
  /-- Expanded record capacity on each actual successor tile. -/
  capacity : ∀ c,localRecords G₀ true (Sum.elim prior (fun _ => 0))
    (Sum.elim payload (fun z => bankUses e (blocks (p₀).layout b₀ perm m z.1) (q z.1).val z.2))
    (fun v => cell v = c) ≤ M
  /-- The fixed word width covers the intrinsic profile fields and the old clipped ordinal. -/
  room : sourceRoom e first M B < 2^w

/-- The native frozen hook program defines a physical section of the whole successor
under its actual named site embedding. -/
theorem successor_section (hc : ComputesCuts (m := m) pop binCode perm cut) (x : σ → Bool)
    (prior payload : (p₀).layout.Site → ℕ) (M B : ℕ)
    (data : SourceData pop binCode perm e seed F counts occupied p slot bin positive first q oldSite portID cell aux
      x prior payload M B) :
    (schema old D w).Section ((asTape (native e seed F counts cut occupied)).eval x)
      ((sID).trans (F.sites.trans Fin.valEmbedding))
      (records binCode perm e seed p slot bin positive first q oldSite portID) := by
  obtain ⟨_,room,hone⟩ := sourceRoom_fits e first M B data.room
  have hin (v : (G₀).Site) : incoming G₀ v < 2^w := by
    have h := incoming_le_cap e p₀ b₀ perm or₀ first q cell prior payload M data.capacity v
    exact h.trans_lt (by omega)
  constructor
  · intro r _ active
    exact owners e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux
      data.geometry data.enabled r active
  · intro v
    change SiteShape e p₀ S at v
    rcases v with oldV | ⟨a,(_ | t | ⟨i,v⟩)⟩
    · exact at_other e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux
        data.geometry data.enabled (.inl oldV) (by intro _ _ h; cases h)
    · apply at_other e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux
        data.geometry data.enabled (.inr ⟨a,.inl ()⟩)
      intro b t h
      have he := congrArg (fun x : Σ _ : S, TemplateSite e => x.2) (Sum.inr.inj h)
      cases he
    · apply saved_at_terminal pop binCode perm cut e seed F counts occupied p slot bin positive first q oldSite portID cell aux
        hc x data.population (fun b => (data.bins b).trans_lt (by omega)) data.widths data.geometry hin data.enabled
        a t hone (data.histogram a none)
      intro z
      let src := decide (or₀ z.val = t.2)
      let side := if src then or₀ z.val else !(or₀ z.val)
      have hd := (hook_fields e p₀ b₀ perm or₀ first q (fun a => (binCode a).val) a t.1 z src).2.1
      have hi := seed_slab_le e p₀ b₀ perm or₀ first q cell prior payload M data.capacity a (.inr (.inl (t.1,side)))
      have hc' : count (p₀).layout b₀ (perm t.1 a) ≤ B :=
        (CutCircuit.dense_count p.layout slot bin (perm t.1 a)).le.trans (data.bins _)
      rw [hd]
      exact (Nat.add_le_add hi hc').trans_lt room
    · apply at_other e seed F counts cut occupied p₀ b₀ perm or₀ first q oldSite old₀ portID cell aux
        data.geometry data.enabled (.inr ⟨a,.inr (.inr ⟨i,v⟩)⟩)
      intro b t h
      have he := congrArg (fun x : Σ _ : S, TemplateSite e => x.2) (Sum.inr.inj h)
      cases Sum.inr.inj he

end Packing.Inherited.HookTape

end BorderVNP
end Computability
end OAI
