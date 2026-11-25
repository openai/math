import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Immutable public row frames at the leaves of the pack history

At a bottom site the repeat record and its grouped incidence ties depend only
on the public grid, its numbering and the copy count. Two shared constant
gates emit their exact tagged words. Extra reserved row slots are disabled
and contribute no scalar payload. The stored order agrees with the original
site program at every genuine owner.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Bottom

open CellSparse ParseBatchCounts ParseBatchSort VPVNP.VerifierNetwork
open private flat_single from OAI.Computability.BorderVNP.PackedFrozenTapeRows
open scoped Classical

variable {V : Type} [Fintype V] (rows : V → List Record) (holes width : ℕ)

/-- Genuine record slots, indexed in their site's original order, plus unused reservations. -/
abbrev Row := (Σ v, Fin (rows v).length) ⊕ Fin holes

/-- The exact scalar tags and values of a live row; no fields are stored for a hole. -/
def fields : Row rows holes → List (Kind × ℕ)
  | .inl ⟨v,i⟩ => marked (rows v)[i.val]
  | .inr _ => []

/-- A scalar bit of an actual frozen row. -/
abbrev Payload := Σ r : Row rows holes, Fin (fields rows holes r).length × Fin width

private noncomputable def siteList := List.ofFn ((Fintype.equivFin V).symm)

private def siteRows (v : V) : List (Row rows holes) :=
  (List.finRange (rows v).length).map (fun i => .inl ⟨v,i⟩)

/-- Static relocation roles and bit locations of the original public record block. -/
noncomputable def schema : Schema (Row rows holes) (Payload rows holes width) where
  rows := (siteList (V := V)).flatMap (siteRows rows holes) ++ (List.finRange holes).map Sum.inr
  tags r := (fields rows holes r).map Prod.fst
  width _ := width
  pin r i j := ⟨r,⟨i.val,by simpa only [List.length_map] using i.isLt⟩,j⟩

variable {d : ℕ} (id : V ↪ Fin (2^d))

/-- Output assignment for the public schema. Unused row keys are encoded as zero. -/
noncomputable def assignment : Pins (Row rows holes) (Payload rows holes width) d → Bool
  | .inl (.inl _,.inl _) => true
  | .inl (.inr _,.inl _) => false
  | .inl (.inl ⟨v,_⟩,.inr j) => (numberWords d).symm (id v) j
  | .inl (.inr _,.inr _) => false
  | .inr ⟨r,i,j⟩ => (numberWords width).symm (Fin.ofNat (2^width) (fields rows holes r)[i.val].2) j

/-- The real two-gate nonuniform leaf frame with public output wiring. -/
noncomputable def frame {σ : Type*} [Fintype σ] :
    Frame σ (Pins (Row rows holes) (Payload rows holes width) d) :=
  ((Frame.initial (_root_.id : σ → σ)).step (fun b : Bool => .const b)).select (assignment rows holes width id)

/-- Gate count stays two; all published addresses are charged separately as pins. -/
theorem frame_size {σ : Type*} [Fintype σ] : (frame (σ := σ) rows holes width id).size ≤ 2 := by
  have h := Frame.step_size_le (Frame.initial (_root_.id : σ → σ)) (fun b : Bool => .const b) 1
    (fun _ => le_rfl)
  simpa only [frame,Frame.select_size,Frame.initial_size,Fintype.card_bool,Nat.zero_add,Nat.mul_one] using h

/-- Every physical pin has exactly its frozen value on every input to this leaf frame. -/
theorem frame_eval {σ : Type*} [Fintype σ] (x : σ → Bool) :
    (frame rows holes width id).eval x = assignment rows holes width id := by
  funext z
  simp only [frame,Frame.select_eval,Frame.step_eval]
  rfl

/-- Fit of the actual published words in the producer's chosen width. -/
def Fits := ∀ v (r : Record), r ∈ rows v → ∀ z ∈ marked r, z.2 < 2^width

private theorem read_fields (fit : Fits rows width) (r : Row rows holes) :
    (schema rows holes width).read (assignment rows holes width id) r = fields rows holes r := by
  have room (z) (hz : z ∈ fields rows holes r) : z.2 < 2^width := by
    rcases r with ⟨v,i⟩ | h
    · exact fit v _ (List.getElem_mem _) z hz
    · simp [fields] at hz
  apply List.ext_getElem
  · simp [Schema.read,schema]
  · intro j hj hk
    simp only [Schema.read,schema,List.getElem_ofFn,assignment]
    change (((fields rows holes r).map Prod.fst)[j]'(by simpa using hk),value ((numberWords width).symm
      (Fin.ofNat (2^width) (fields rows holes r)[j].2))) = _
    rw [List.getElem_map,value_encode,Fin.val_ofNat,Nat.mod_eq_of_lt (room _ (List.getElem_mem hk))]

omit [Fintype V] in
private theorem live_owner (v : V) (i : Fin (rows v).length) :
    owner (assignment rows holes width id) (.inl ⟨v,i⟩) = (id v).val :=
  value_encode (id v)

private theorem at_siteRows (fit : Fits rows width) (u v : V) :
    (siteRows rows holes u).filterMap (fun r => if assignment rows holes width id (.inl (r,.inl ())) ∧
      owner (assignment rows holes width id) r = (id v).val then some ((schema rows holes width).read
      (assignment rows holes width id) r) else none) =
    if u=v then (rows v).map marked else [] := by
  by_cases he : u=v
  · subst u
    simp only [siteRows,List.filterMap_map,Function.comp_def,assignment,live_owner,read_fields rows holes width id fit,
      fields,and_self,ite_true]
    rw [List.filterMap_eq_map_iff_forall_eq_some.mpr (fun _ _ => rfl)]
    simp only [← List.ofFn_eq_map,List.ofFn_getElem_eq_map]
  · have hn : (id u).val ≠ (id v).val := fun e => he (id.injective (Fin.ext e))
    simp [siteRows,List.filterMap_map,assignment,live_owner,hn,he]

/-- Reading the live rows by owner recovers the original public site-local list,
including exact numeric words, tag positions, empty sites and unused reservations. -/
theorem atSite (fit : Fits rows width) (v : V) :
    (schema rows holes width).atSite (assignment rows holes width id) (id v).val = (rows v).map marked := by
  let pick := fun r => if assignment rows holes width id (.inl (r,.inl ())) ∧
      owner (assignment rows holes width id) r = (id v).val then some ((schema rows holes width).read
      (assignment rows holes width id) r) else none
  have skip : ((List.finRange holes).map Sum.inr).filterMap pick = [] := by
    simp [pick,List.filterMap_map,assignment]
  have hflat (vs : List V) :
      (vs.flatMap (siteRows rows holes)).filterMap pick =
        vs.flatMap (fun u => if u=v then (rows v).map marked else []) := by
    induction vs with
    | nil => rfl
    | cons u vs ih => simp only [List.flatMap_cons,List.filterMap_append,at_siteRows rows holes width id fit u v,ih,pick]
  change (((siteList (V := V)).flatMap (siteRows rows holes) ++ (List.finRange holes).map Sum.inr).filterMap pick) = _
  rw [List.filterMap_append,skip,List.append_nil,hflat]
  have nd : (siteList (V := V)).Nodup := List.nodup_ofFn.mpr (Fintype.equivFin V).symm.injective
  have mem : v ∈ siteList (V := V) := List.mem_ofFn.mpr ⟨(Fintype.equivFin V) v,Equiv.symm_apply_apply ..⟩
  exact (flat_single _ v (fun _ => (rows v).map marked) nd).trans (ite_eq_left mem)

/-- The actual frame satisfies the frozen-tape interface at birth, before any
adaptive parallel placement or shortening step. -/
theorem image {σ : Type*} [Fintype σ] (fit : Fits rows width) (x : σ → Bool)
    (states : V → Site) (same : ∀ v, (states v).rows = rows v) :
    (schema rows holes width).Image ((frame rows holes width id).eval x) (id.trans Fin.valEmbedding) states := by
  rw [frame_eval]
  constructor
  · intro r _ active
    rcases r with ⟨v,i⟩ | h
    · exact ⟨v,live_owner rows holes width id v i⟩
    · cases active
  · intro v
    rw [same]
    exact atSite rows holes width id fit v

/-- Number of frozen slots in the padded static representation. -/
theorem card_rows : Fintype.card (Row rows holes) = (∑ v, (rows v).length)+holes := by
  simp [Row]

/-- Each real scalar has the chosen bit width. Disabled reservations have no payload. -/
theorem card_payload :
    Fintype.card (Payload rows holes width) = (∑ r : Row rows holes, (fields rows holes r).length)*width := by
  simp only [Payload,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Finset.sum_mul]

end Packing.Inherited.FrozenTape.Bottom

end BorderVNP
end Computability
end OAI
