import OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost
import OAI.Computability.BorderVNP.PackedFrozenBottomRows
import OAI.Computability.BorderVNP.PackedFrozenSubdivisionTape
import OAI.Computability.BorderVNP.PackedFrozenNodeProgram
import OAI.Computability.BorderVNP.PackedFinalTieFrozen

/-! # Enumerated rows and tagged scalar arities of the actual public schemas -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing CellSparse Shortening.StaticRows BankJoint
open private columns from OAI.Computability.BorderVNP.PackedFrozenBirthFields
open private siteList siteRows from OAI.Computability.BorderVNP.PackedFrozenBottomRows
open scoped Classical

/-- The count of stored rows in a complete site-major rectangle agrees with its dependent
sum of actual row counts, independently of the enumeration of sites. -/
private theorem flatLength {V R : Type*} [Fintype V] (f : V → List R) :
    ((List.ofFn (Fintype.equivFin V).symm).flatMap f).length = ∑ v, (f v).length := by
  simp only [List.length_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  exact (Fintype.equivFin V).symm.sum_comp (fun v => (f v).length)

variable {V : Type} [Fintype V] (rs : V → List Record) (holes w : ℕ)

/-- The bottom tape enumerates all true birth rows and all reserved holes exactly once. -/
theorem bottom_length : (Bottom.schema rs holes w).rows.length = Fintype.card (Bottom.Row rs holes) := by
  rw [Bottom.card_rows]
  simp only [Bottom.schema,List.length_append,List.length_map,List.length_finRange,siteList]
  rw [flatLength]
  change (∑ v, ((List.finRange (rs v).length).map fun i => (Sum.inl ⟨v,i⟩ : Bottom.Row rs holes)).length)+holes = _
  simp only [List.length_map,List.length_finRange]

/-- A hole has no fields. On true bottom rows the tag arity equals the marked record arity. -/
theorem bottom_tags (cap : ℕ) (bound : ∀ v, ∀ r ∈ rs v, (marked r).length ≤ cap) :
    ∀ r, ((Bottom.schema rs holes w).tags r).length ≤ cap := by
  rintro (⟨v,i⟩|i)
  · simpa only [Bottom.schema,Bottom.fields,List.length_map] using bound v _ (List.getElem_mem i.isLt)
  · simp [Bottom.schema,Bottom.fields]

private theorem flatSum {V R : Type*} (L : List V) (rows : V → List R) (weight : R → ℕ) :
    ((L.flatMap rows).map weight).sum = (L.map fun v => ((rows v).map weight).sum).sum := by
  induction L with
  | nil => rfl
  | cons v L ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,List.map_cons,List.sum_cons]

/-- The counted bottom tags are exactly the scalar fields of the true and reserved rows.
Consequently multiplying this count by the stored word width gives the payload bit count. -/
theorem bottom_tagWords :
    CellPacketGeometry.History.tagWords (Bottom.schema rs holes w) =
      ∑ r : Bottom.Row rs holes, (Bottom.fields rs holes r).length := by
  let weight (r : Bottom.Row rs holes) := (Bottom.fields rs holes r).length
  have one (v : V) : ((siteRows rs holes v).map weight).sum =
      ∑ i : Fin (rs v).length, weight (.inl ⟨v,i⟩) := by
    change (((List.finRange (rs v).length).map fun i => (Sum.inl ⟨v,i⟩ : Bottom.Row rs holes)).map weight).sum = _
    rw [←List.ofFn_eq_map,List.map_ofFn,List.sum_ofFn]
    rfl
  change ((((siteList (V := V)).flatMap (siteRows rs holes) ++ (List.finRange holes).map Sum.inr).map
    (fun r => ((Bottom.fields rs holes r).map Prod.fst).length)).sum) = _
  simp only [List.length_map,List.map_append,List.sum_append,Fintype.sum_sum_type,Fintype.sum_sigma]
  change (((siteList (V := V)).flatMap (siteRows rs holes)).map weight).sum +
    (((List.finRange holes).map Sum.inr).map weight).sum = _
  rw [flatSum,siteList,List.map_ofFn,List.sum_ofFn,List.map_map,←List.ofFn_eq_map,List.sum_ofFn]
  apply congrArg₂ Nat.add
  · simp only [Function.comp_def,one]
    exact (Fintype.equivFin V).symm.sum_comp (fun v => ∑ i : Fin (rs v).length, weight (.inl ⟨v,i⟩))
  · rfl

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- The fixed template bounds every tagged seed row, even when scalar data depend on the profile. -/
noncomputable def birthTagBound := ∑ v : TemplateSite e, ∑ i : Fin (rows e first v).length,
  (markedCode (rows e first v)[i]).length

/-- Birth row count is linear in the number of seeds, including zero multiplicities. -/
theorem birth_length (S : Type*) [Fintype S] :
    (Birth.schema e first S w).rows.length = Fintype.card (Birth.Row e first S) := by
  simp only [Birth.schema,Birth.rowList,flatLength,List.length_ofFn,Birth.Row,Fintype.card_sigma,Fintype.card_fin]

/-- Every immutable birth row has at most the fixed seed-template tag bound. -/
theorem birth_tags (S : Type*) [Fintype S] (r : Birth.Row e first S) :
    ((Birth.schema e first S w).tags r).length ≤ birthTagBound e first := by
  let cost (v : TemplateSite e) (i : Fin (rows e first v).length) := (markedCode (rows e first v)[i]).length
  change ((markedCode (Birth.code e first S r)).map Prod.fst).length ≤ _
  rw [List.length_map]
  exact (Finset.single_le_sum (f := cost r.1.2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r.2)).trans
    (Finset.single_le_sum (f := fun v => ∑ i, cost v i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r.1.2))

/-- The whole immutable seed schema stores at most one tag per emitted main-packet word.
The packet also reserves one count word at each seed site. -/
theorem birth_tagWords_le (S : Type) [Fintype S] :
    CellPacketGeometry.History.tagWords (Birth.schema e first S w) ≤ Fintype.card S*Fintype.card (Output e first) := by
  let words (z : S × TemplateSite e) := (BankPacket.tape (rows e first z.2)).length
  let weight (r : Birth.Row e first S) := (Birth.fieldTags e first S r).length
  let part (z : S × TemplateSite e) := List.ofFn (fun i : Fin (rows e first z.2).length => (⟨z,i⟩ : Birth.Row e first S))
  have localBound (z) : ((part z).map weight).sum ≤ words z := by
    simp only [part,List.map_ofFn,List.sum_ofFn,Function.comp_def,weight,columns,Birth.code]
    simp only [words,BankPacket.tape,List.length_cons,List.length_flatMap]
    rw [←List.ofFn_getElem_eq_map, List.sum_ofFn]
    exact Nat.le_succ _
  change (((List.ofFn (Fintype.equivFin (S × TemplateSite e)).symm).flatMap part).map weight).sum ≤ _
  rw [flatSum,List.map_ofFn,List.sum_ofFn]
  apply (Finset.sum_le_sum (fun i _ => localBound ((Fintype.equivFin (S × TemplateSite e)).symm i))).trans_eq
  rw [(Fintype.equivFin (S × TemplateSite e)).symm.sum_comp words]
  simp only [words,Output,Fintype.card_sigma,Fintype.card_fin,Fintype.sum_prod_type,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Nat.cast_id]

/-- All fixed endpoint, port and relay slots of the subdivision contribute one nine-field row. -/
theorem subdivision_length (m np extra : ℕ) :
    (Subdivision.Gates.tapeSchema m np extra w).rows.length = Fintype.card (Subdivision.Gates.Row m np extra) := by
  simp [Subdivision.Gates.tapeSchema,NineWords.schema,Subdivision.Gates.Row,Subdivision.Gates.Old]

/-- All old cable-band and port candidates occur in the retained-row writer. -/
theorem layer_length (m D np : ℕ) :
    (LayerRows.schema m D np w).rows.length = Fintype.card (Layer.Row m D np) := by
  simp [LayerRows.schema,NineWords.schema,LayerRows.rectangle]

/-- The terminal writer's source list enumerates all cable-direction-orientation slots. -/
theorem hook_length (m D : ℕ) :
    (HookTape.schema m D w).rows.length = Fintype.card (InheritedHook.Row m D) := by
  simp [HookTape.schema,HookTape.rows,InheritedHook.Row]

/-- The final binding tape reserves both cable ends and one row per exterior port. -/
theorem final_length (m np : ℕ) :
    (FinalTies.tieSchema m np w).rows.length = 2*m+np := by
  simp [FinalTies.tieSchema,NineWords.schema,FinalTies.staticRows,Nat.mul_comm]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
