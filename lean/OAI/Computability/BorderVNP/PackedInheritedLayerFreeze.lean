import OAI.Computability.BorderVNP.PackedInheritedLayerPhysical
import OAI.Computability.BorderVNP.PackedInheritedLayerCuts
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds

/-! # Fixed circuit freezing every retained interval on a physical branch

Old interval spans and offsets come from the public cut circuit. The complete
emitted nine-word row reads the real old and successor singleton-cell starts.
A bound on the actual expanded load discharges every numerical field guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open InheritedBank CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

/-- Public output of one fixed-slot inherited row. -/
abbrev Output (d w : ℕ) := Unit ⊕ (Fin d ⊕ (Fin 9 × Fin w))

variable {D m s old np seeds C C' d d' k k' w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {σ : Type*} [Fintype σ]
variable (oldF : CellAddressCircuit.Fields s old np C d k w σ)
variable (newF : CellAddressCircuit.Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ)
variable (occupied : Fin old → σ) (portUsed : Fin np → Bool) (successor : Fin (edgeCapacity e old seeds) → σ)
local notation3 "src₀" => inputs e oldF newF cut work extent occupied portUsed successor

/-- The structural source assumptions name only upstream physical fields and local
size bounds. Site tables and branch profiles remain universally quantified. -/
structure RealInputs {P : Type*} {A : Type} [Fintype P] {bits : P → ℕ} [Fintype A] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (binName : A → ℕ)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (seed : A ↪ Fin seeds)
    (states : p.layout.Site → Site) (prior payload : p.layout.Site → ℕ) (x : σ → Bool) : Prop where
  /-- The old endpoint and width pins correspond to this sparse physical presentation. -/
  previous : Views.EndpointData p.layout oldF siteID oldID portID x
  /-- The successor endpoint and width pins name the actual chosen sewn branch. -/
  current : Views.EndpointData (output e p bin perm positive first q).layout newF (siteRows e p siteID seed)
    (outputRows e p bin perm positive first q oldID seed) portID x
  /-- No virtual old-site incidence array overflows the word field. -/
  oldFits : ∀ v, incoming p.layout v < 2^w
  /-- No virtual successor incidence array overflows the field. -/
  newFits : ∀ v, incoming (output e p bin perm positive first q).layout v < 2^w
  /-- The site-work directory stores the full persistent old work. -/
  workRead : ∀ v, value (x ∘ work (siteID v)) = (states v).work
  /-- The extent column stores the old site's work and current incidence. -/
  extentRead : ∀ v, value (x ∘ extent (siteID v)) = (states v).size
  /-- Values furnished by the actual clipped interval pass. -/
  cuts : ∀ z b a, value (fun j => cut.eval x ((oldID z,b),a,j)) =
    a.read (priorDescriptor (m := m) p bin perm binName z b)
  /-- Occupancy of the complete successor edge directory. -/
  success : ∀ i, x (successor i) = true ↔ i ∈ Set.range (outputRows e p bin perm positive first q oldID seed)
  /-- The old intrinsic program has the canonical incoming extent. -/
  incomingSize : ∀ v, (states v).incoming = incoming p.layout v
  /-- Cumulative payload accounts for the old work. -/
  oldWork : ∀ v, (states v).work ≤ payload v
  /-- Every retained site belongs to a true expanded tile within the word field. -/
  room : ∀ v : p.layout.Site, ∃ test : (output e p bin perm positive first q).layout.Site → Prop,
    test (.inl v) ∧ localRecords (output e p bin perm positive first q).layout true
      (nextPrior e p bin perm positive first q prior) (nextPayload e p bin perm positive first q payload) test < 2^w

/-- One gate list freezes all old interval commands for every accepted geometric
branch. The evaluator receives only current physical registers and the two
site-prefix lookups. Each active slot emits exactly nine tagged packet fields. -/
theorem exists_frozen :
    ∃ f : Frame σ (Row old D np × Output d w),
      f.size ≤ (table e oldF newF cut work extent).size +
        Fintype.card (Row old D np)*(1+d+6*w)*(30*d+16) + 1 +
        Fintype.card (Row old D np)*(4500*(w+1)^2) ∧
      (∀ x r, f.eval x (r,.inl ()) = (src₀).eval x (r,.inl ())) ∧
      (∀ x r j, f.eval x (r,.inr (.inl j)) = (src₀).eval x (r,.inr (.inl j))) ∧
      ∀ {P : Type*} [Fintype P] {bits : P → ℕ} {A : Type} [Fintype A] (p : Pack D P bits K)
        (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (binName : A → ℕ)
        (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
        (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (seed : A ↪ Fin seeds)
        (states : p.layout.Site → Site) (prior payload : p.layout.Site → ℕ) (x : σ → Bool),
        RealInputs e oldF newF cut work extent successor p bin perm binName positive first q
          siteID oldID portID seed states prior payload x →
        ∀ (v : p.layout.Site) (r : LayerRow p v),
          let row := name p oldID portID v r
          let newID := outputRows e p bin perm positive first q oldID seed
          let slice := layerSlice e p bin perm binName positive first q v oldID newID portID r
          List.ofFn (fun i => (kind i,value (fun j => f.eval x (row,.inr (.inr (i,j)))))) =
            marked (slice.record (states v)) := by
  obtain ⟨f,hf,hactive,howner,fields⟩ := emit d w (src₀)
  refine ⟨f,?_,hactive,howner,?_⟩
  · have hs := inputs_size e oldF newF cut work extent occupied portUsed successor
    omega
  · intro P _ bits A _ p bin perm binName positive first q siteID oldID portID seed states prior payload x h v r row newID slice
    have hr := input_command e oldF newF cut work extent occupied portUsed successor p bin perm binName positive first q
      siteID oldID portID seed h.previous h.current h.oldFits h.newFits states h.workRead h.extentRead h.cuts h.success v r
    obtain ⟨test,hv,cap⟩ := h.room v
    have fits := command_room e p bin perm binName positive first q v oldID newID portID r (states v)
      prior payload (h.incomingSize v) (h.oldWork v) test hv cap _ hr
    exact (fields x row fits.1 fits.2.1 fits.2.2).trans (congrArg marked hr)

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
