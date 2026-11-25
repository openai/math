import OAI.Computability.BorderVNP.PackedBankBoxBinding

/-! # Paid-site observations from a merged private box directory

The emitted row points at a specified slot in the owning cell's directory.
Resolving that slot in the actual occurrence traversal produces one genuine
paid-entry address per copy, even when distinct entries have equal scalars.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidBinding

open BankPacket BankPacket.Paid PaidBox Crossing Crossing.CellBox CellSparse
open scoped Classical
open private rows_shape stage_lt from OAI.Computability.BorderVNP.PackedBankBoxBinding

variable {n : ℕ} (w : Fin n → ℕ) (copies off id : ℕ) (physical : Fin n → ℕ)

/-- A site's record segment resolved against the full cell's private box list. -/
def fragment (boxes : List (List Factor)) : Directory :=
  ⟨boxes,(rows w).map (RecordCode.read (fields w copies off id physical)),[]⟩

private theorem fragment_occurrences (boxes : List (List Factor)) (f : Factor) (hbox : boxes.getD id [] = [f]) :
    (fragment w copies off id physical boxes).occurrences = List.ofFn fun i : Fin copies =>
      (⟨f,(off+copies*(∑ r,w r))+i.val*(∑ r,w r),i.val⟩ : Occurrence) := by
  simp only [fragment,Directory.occurrences,rows_shape,List.flatMap_append]
  rw [show ((stageRecords copies (copies*∑ r,w r) (src w copies)).map (fun r => r.shift off)).flatMap _ =
      ([] : List Occurrence) from List.flatMap_eq_nil_iff.mpr (fun r hr => by
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hq
        rfl)]
  rw [show (List.ofFn (bundleTie w (fields w copies off id physical))).flatMap _ =
      ([] : List Occurrence) from List.flatMap_eq_nil_iff.mpr (fun r hr => by
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
        rfl)]
  simp only [List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,hbox,List.map_cons,List.map_nil]
  rw [← List.map_eq_flatMap]
  apply List.ext_getElem <;> simp

/-- The copy-major region of the canonical slab reads precisely the physical source lane. -/
theorem canonical_read (bank : ℕ → Bool) (i : Fin copies) (k : Fin (∑ r,w r)) :
    canonical w copies physical bank (copies*(∑ r,w r)+(i.val*(∑ r,w r)+k.val)) =
      data w copies physical bank i k := by
  simp [canonical,stageBank,packedBank_read,inputBank_read]

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
  (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site)

/-- Genuine local table address recovered from a copy of the wired physical incident lanes. -/
noncomputable def entryAt (physical : Fin (Fintype.card (Bundle (e.net a) v)) → ℕ)
    (bank : ℕ → Bool) (i : Fin copies) : e.Entry :=
  let bit (l : Lane (e.net a) v) := data (widths (e.net a) v) copies physical bank i ((laneOrder (e.net a) v) l)
  ⟨a,v,(fun u k => bit (.inl ⟨u,k⟩)),(fun u k => bit (.inr ⟨u,k⟩))⟩

/-- On a valid physical bank, the merged site's actual occurrence traversal selects
exactly the table positions of its incident wires, with its supplied box ID and cell offset. -/
theorem observations (physical : Fin (Fintype.card (Bundle (e.net a) v)) → ℕ)
    (boxes : List (List Factor)) (bank : ℕ → Bool)
    (hbox : boxes.getD id [] = [tableFactor e position a v])
    (hvalid : ∀ r ∈ (fragment (widths (e.net a) v) copies off id physical boxes).records, r.Valid boxes bank) :
    (fragment (widths (e.net a) v) copies off id physical boxes).observations bank =
      some (List.ofFn (fun i => (false,some (position (entryAt copies e a v physical bank i))))) := by
  let w := widths (e.net a) v
  let d := arity e a v
  have he := ((valid_iff w copies off id physical boxes bank).mp hvalid).2
  let result (i : Fin copies) := (false,some (position (entryAt copies e a v physical bank i)))
  have h (i : Fin copies) : (tableFactor e position a v).observe bank (off+copies*d+i.val*d) i.val = some (result i) := by
    rw [tableFactor,observe_factor]
    let z₁ := fun l => bank (off+copies*d+i.val*d+((laneOrder (e.net a) v) l).val)
    let z₂ := fun l => data w copies physical bank i ((laneOrder (e.net a) v) l)
    change some (false,some (localRow (e.net a) (ids e position a) v z₁)) =
      some (false,some (localRow (e.net a) (ids e position a) v z₂))
    apply congrArg (fun z => some (false,some (localRow (e.net a) (ids e position a) v z)))
    funext l
    let k := laneOrder (e.net a) v l
    change bank (off+copies*d+i.val*d+k.val) = data w copies physical bank i k
    have hlt := stage_lt i k
    rw [show off+copies*d+i.val*d+k.val = off+(copies*d+(i.val*d+k.val)) by omega,
      he _ (Nat.add_lt_add_left hlt _)]
    exact canonical_read w copies physical bank i k
  rw [Directory.observations,fragment_occurrences _ _ _ _ _ boxes _ hbox,List.ofFn_eq_map,List.mapM_map,List.ofFn_eq_map]
  change (List.finRange copies).mapM (fun i => (tableFactor e position a v).observe bank
    (off+copies*d+i.val*d) i.val) = some _
  rw [funext h]
  exact List.mapM_pure (m := Option) (f := result)

end Packing.PaidBinding

end BorderVNP
end Computability
end OAI
