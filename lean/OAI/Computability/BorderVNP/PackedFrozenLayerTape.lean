import OAI.Computability.BorderVNP.PackedFrozenNineWords
import OAI.Computability.BorderVNP.PackedFrozenTapeSections
import OAI.Computability.BorderVNP.PackedInheritedLayerActive

/-! # Complete immutable tie records on a physical shortening branch

The source rectangle covers cable bands at their incident sites, including loop bands exactly
once, and attached ports. The emitter computes the nine scalars from the physical old and
successor addresses. The final site lookup names every surviving row in the successor directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.LayerRows

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open InheritedBank CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m s old np seeds C C' d d' k k' w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {σ : Type*} [Fintype σ]
variable (oldF : CellAddressCircuit.Fields s old np C d k w σ)
variable (newF : CellAddressCircuit.Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ)
variable (occupied : Fin old → σ) (portUsed : Fin np → Bool) (successor : Fin (edgeCapacity e old seeds) → σ)
local notation3 "rows" => Layer.Row old D np
local notation3 "src" => Layer.inputs e oldF newF cut work extent occupied portUsed successor

/-- All reserved endpoint-band and port slots, in the public rectangle order. -/
noncomputable def rectangle (old D np : ℕ) : List (Layer.Row old D np) :=
  (List.finRange (Fintype.card (Layer.Row old D np))).map Layer.order.symm

/-- The immutable schema of the new tie block, before splicing in previous layers. -/
noncomputable def schema (old D np w : ℕ) := NineWords.schema (rectangle old D np) w

private theorem active_owner {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (x : σ → Bool)
    (h : Views.EndpointData p.layout oldF siteID oldID portID x)
    (used : ∀ i, x (occupied i) = true ↔ i ∈ Set.range oldID)
    (ports : ∀ i, portUsed i = true ↔ i ∈ Set.range portID) (r : rows) (on : (src).eval x (r,.inl ()) = true) :
    ∃ v, value (fun j => (src).eval x (r,.inr (.inl j))) = (oldF.sites (siteID v)).val := by
  have ho : value (fun j => (src).eval x (r,.inr (.inl j))) = value (x ∘ oldF.ptr (Layer.endpoint r)) := by
    simp only [Layer.inputs,Frame.subst_eval,Layer.source_owner,Layer.tableFields,Layer.table,Frame.withInput_eval_inl,
      Function.comp_def]
  rw [ho]
  rcases r with ⟨⟨i,b⟩,side⟩ | i
  · simp only [Layer.inputs,Frame.subst_eval,Layer.source_live,Layer.tableFields,Layer.table,Frame.withInput_eval_inl]
      at on
    obtain ⟨z,rfl⟩ := (used _).mp on.1
    cases side
    · exact ⟨p.layout.dst z,h.dst z⟩
    · exact ⟨p.layout.src z,h.src z⟩
  · simp only [Layer.inputs,Frame.subst_eval,Layer.source_port_live,Layer.tableFields] at on
    obtain ⟨a,rfl⟩ := (ports _).mp on
    exact ⟨p.layout.attach a,h.attach a⟩

variable [NeZero D]

/-- Contract of the physical interval emitter for all real geometric inputs. Every enabled row
has an attained owner. Its per-site records include all nine tagged scalars in source order. -/
def Realizes {z : ℕ} (code : Fin s ↪ Fin (2^z)) (f : Frame σ (Pins rows (rows × Fin 9 × Fin w) z)) : Prop :=
  ∀ {P : Type*} [Fintype P] {bits : P → ℕ} {A : Type} [Fintype A] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (binName : A → ℕ)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (siteID : p.layout.Site ↪ Fin s) (oldID : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np) (seed : A ↪ Fin seeds)
    (states : p.layout.Site → Site) (prior payload : p.layout.Site → ℕ) (x : σ → Bool),
    Layer.RealInputs e oldF newF cut work extent successor p bin perm binName positive first q
      siteID oldID portID seed states prior payload x →
    (∀ i, x (occupied i) = true ↔ i ∈ Set.range oldID) →
    (∀ i, portUsed i = true ↔ i ∈ Set.range portID) →
    (schema old D np w).Block (f.eval x) (fun v => (code (siteID v)).val)
      (fun v => (Layer.orderedCuts p oldID portID v e bin perm binName positive first q
        (outputRows e p bin perm positive first q oldID seed)).map (fun sl => marked (sl.record (states v))))

/-- Total gate bound for the two site tables, branch cut lookups and the nine scalar emitters. -/
noncomputable def budget := (Layer.table e oldF newF cut work extent).size +
    Fintype.card rows*(1+d+6*w)*(30*d+16) + 1 + Fintype.card rows*(4500*(w+1)^2)

/-- One fixed physical frame freezes all inherited commands under the old site keys. -/
theorem exists_layer :
    ∃ f, f.size ≤ budget e oldF newF cut work extent ∧
      Realizes e oldF newF cut work extent occupied portUsed successor oldF.sites f := by
  obtain ⟨f,size,active,ownerBit,words⟩ := Layer.exists_frozen e oldF newF cut work extent occupied portUsed successor
  refine ⟨NineWords.adapt f,by simpa only [budget,NineWords.adapt_size] using size,?_⟩
  intro P _ bits A _ p bin perm binName positive first q siteID oldID portID seed states prior payload x h used ports
  constructor
  · intro r _ en
    simp only [NineWords.adapt,Frame.select_eval,NineWords.pin,active] at en
    simpa only [owner,NineWords.adapt,Frame.select_eval,NineWords.pin,ownerBit] using
      active_owner e oldF newF cut work extent occupied portUsed successor p siteID oldID portID x
        h.previous used ports r en
  · intro v
    rw [schema,NineWords.atSite]
    have orderEq := Layer.selectedAt_names e oldF newF cut work extent occupied portUsed successor
      p siteID oldID portID h.previous used ports v
    simp only [rectangle,List.filter_map,Function.comp_def,active,ownerBit]
    simp only [Layer.selectedAt] at orderEq
    rw [orderEq,Layer.orderedCuts,List.map_ofFn,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact words p bin perm binName positive first q siteID oldID portID seed states prior payload x h v
      (Layer.index p oldID portID v i)

/-- The successor's actual code on the prefix occupied by retained sites. -/
noncomputable def retainedCode : Fin s ↪ Fin (2^d') :=
  (Fin.castAddEmb (seeds * Fintype.card (TemplateSite e))).trans newF.sites

/-- One fixed frozen-tape frame names its nine-word records directly in the successor site
directory. The extra batch translates only owner keys and leaves the immutable fields in place. -/
theorem exists_successor_layer :
    ∃ f, f.size ≤ budget e oldF newF cut work extent + lookupCost s (Fintype.card rows) d d' ∧
      Realizes e oldF newF cut work extent occupied portUsed successor (retainedCode e newF) f := by
  obtain ⟨f,hf,real⟩ := exists_layer e oldF newF cut work extent occupied portUsed successor
  let next := retainedCode e newF
  refine ⟨(rekey oldF.sites next).subst f,?_,?_⟩
  · rw [Frame.subst_size]
    exact Nat.add_le_add hf (rekey_size _ _)
  · intro P _ bits A _ p bin perm binName positive first q siteID oldID portID seed states prior payload x h used ports
    have he : ((rekey oldF.sites next).subst f).eval x = (rekey oldF.sites next).eval (f.eval x) := by
      funext z; rw [Frame.subst_eval]
    rw [he]
    exact (real p bin perm binName positive first q siteID oldID portID seed states
      prior payload x h used ports).rekey _ oldF.sites next

omit [Fintype σ] [NeZero D] in
/-- A new seed-bank site has no inherited interval records in the successor tape. -/
theorem freshSeed {P : Type*} {bits : P → ℕ} {A : Type} (p : Pack D P bits K)
    (siteID : p.layout.Site ↪ Fin s) (seed : A ↪ Fin seeds) (a : A) (u : TemplateSite e)
    (x : Pins rows (rows × Fin 9 × Fin w) d' → Bool) (records : p.layout.Site → List (List (Kind × ℕ)))
    (h : (schema old D np w).Block x (fun v => (retainedCode e newF (siteID v)).val) records) :
    (schema old D np w).atSite x (newF.sites (siteRows e p siteID seed (.inr ⟨a,u⟩))).val = [] := by
  apply h.fresh
  intro v eqn
  have same : siteRows e p siteID seed (.inl v) = siteRows e p siteID seed (.inr ⟨a,u⟩) :=
    newF.sites.injective (Fin.ext eqn)
  cases (siteRows e p siteID seed).injective same

omit [Fintype σ] [NeZero D] in
/-- A layer block gives a whole-successor section, retaining the actual old row lists and
contributing the empty list at every newly inserted site. This section appends directly to
the prior chronological tape and to the new seed sections. -/
theorem successor_section {P : Type*} {bits : P → ℕ} {A : Type} (p : Pack D P bits K)
    (siteID : p.layout.Site ↪ Fin s) (seed : A ↪ Fin seeds)
    (x : Pins rows (rows × Fin 9 × Fin w) d' → Bool) (records : p.layout.Site → List CellSparse.Record)
    (h : (schema old D np w).Block x (fun v => (retainedCode e newF (siteID v)).val)
      (fun v => (records v).map marked)) :
    (schema old D np w).Section x ((siteRows e p siteID seed).trans (newF.sites.trans Fin.valEmbedding))
      (Sum.elim records (fun _ => [])) := by
  constructor
  · intro r hr live
    obtain ⟨v,hv⟩ := h.owners r hr live
    exact ⟨.inl v,hv⟩
  · rintro (v|⟨a,u⟩)
    · exact h.atSite v
    · exact freshSeed e newF p siteID seed a u x _ h

end Packing.Inherited.FrozenTape.LayerRows

end BorderVNP
end Computability
end OAI
