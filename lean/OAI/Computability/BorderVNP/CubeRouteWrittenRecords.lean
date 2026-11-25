import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload
import OAI.Computability.BorderVNP.TransmissionDataMaterialized

/-! # The common routing table produced by the data and shared-row writers

The prefix consists of the populated delivery demands in directory order. The
suffix consists of the strictly increasing pairs of grouping symbols, in the
same triangular order as the native writer. The four scheduling columns are
independent of a team's local source and destination addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical RoutingISA RoutingISA.Transmission TeamContraction VPVNP.BurstRAM
open Packing.Directory (Row)

variable {q a R : ℕ}

/-- Rank by increasing upper endpoint and then lower endpoint, as in the physical suffix. -/
private def rank (p : Symbols q) : Fin (q.choose 2) :=
  ⟨p.val.2.val.choose 2+p.val.1.val,by
    have next := Nat.choose_le_choose 2 p.val.2.isLt
    rw [SharedRows.choose_succ_two] at next
    have lt : p.val.1.val < p.val.2.val := p.property
    omega⟩

private theorem rank_injective : Function.Injective (rank (q := q)) := by
  intro p r h
  have eqn : p.val.2.val.choose 2+p.val.1.val = r.val.2.val.choose 2+r.val.1.val := congrArg Fin.val h
  have hp : p.val.1.val < p.val.2.val := p.property
  have hr : r.val.1.val < r.val.2.val := r.property
  have right : p.val.2.val = r.val.2.val := by
    rcases lt_trichotomy p.val.2.val r.val.2.val with hl|he|hg
    · have next := Nat.choose_le_choose 2 hl
      rw [SharedRows.choose_succ_two] at next
      omega
    · exact he
    · have next := Nat.choose_le_choose 2 hg
      rw [SharedRows.choose_succ_two] at next
      omega
  rw [right] at eqn
  exact Subtype.ext (Prod.ext (Fin.ext (Nat.add_left_cancel eqn)) (Fin.ext right))

/-- Public ordinals of the two consecutive types of records. -/
noncomputable def ordinal (dataCount q : ℕ) :
    Fin dataCount ⊕ Symbols q ≃ Fin (dataCount+q.choose 2) :=
  let pairs := Equiv.ofBijective (rank (q := q)) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨rank_injective,(Owned.card_symbols q).trans (Fintype.card_fin _).symm⟩)
  ((Equiv.refl _).sumCongr pairs).trans finSumFinEquiv

/-- Genuine data records retain the compact directory order. -/
theorem ordinal_data (count : ℕ) (i : Fin count) : (ordinal count q (.inl i)).val = i.val := rfl

/-- The shared ordinal is exactly the addressable triangular rank after the data prefix. -/
theorem ordinal_shared (count : ℕ) (p : Symbols q) :
    (ordinal count q (.inr p)).val = count+p.val.2.val.choose 2+p.val.1.val := by
  change count+(p.val.2.val.choose 2+p.val.1.val) = _
  omega

/-- The four common scheduling columns of one populated data row. -/
def dataRow (owner : ℕ → Fin (R+1)) (r : Row) : TableRow := ⟨1,r.team,(owner r.cell).val,r.width⟩

/-- A real shared row has the two greedy group owners and the full reserved length. -/
def sharedRow (blocks K h : ℕ) (D : LengthDeclaration a q) (group : Fin q → Fin (R+1)) (p : Symbols q) :
    TableRow := ⟨0,(group p.val.1).val,(group p.val.2).val,SharedRows.reserved blocks K h D p⟩

/-- Common semantic table at every physical team; ordinals beyond the published count are unused. -/
noncomputable def combinedRow (data : List Row) (owner : ℕ → Fin (R+1)) (blocks K h : ℕ)
    (D : LengthDeclaration a q) (group : Fin q → Fin (R+1)) (i : ℕ) : TableRow :=
  if hi : i < data.length+q.choose 2 then
    ((ordinal data.length q).symm ⟨i,hi⟩).elim (fun k => dataRow owner data[k.val]) (sharedRow blocks K h D group)
  else ⟨0,0,0,0⟩

variable (data : List Row) (owner : ℕ → Fin (R+1)) (blocks K h : ℕ)
variable (D : LengthDeclaration a q) (group : Fin q → Fin (R+1))

private theorem atOrdinal (e : Fin data.length ⊕ Symbols q) :
    combinedRow data owner blocks K h D group (ordinal data.length q e).val =
      e.elim (fun i => dataRow owner data[i.val]) (sharedRow blocks K h D group) := by
  simp only [combinedRow,dite_eq_left (ordinal data.length q e).isLt,Fin.eta,Equiv.symm_apply_apply]

/-- At a populated prefix position the semantic table reads its actual data row. -/
theorem data_at (i : Fin data.length) :
    combinedRow data owner blocks K h D group i.val = dataRow owner data[i.val] :=
  atOrdinal data owner blocks K h D group (.inl i)

/-- At a native shared suffix position the semantic table reads exactly that symbol pair. -/
theorem shared_at (g : SharedRows.Layout) (count : g.dataCount = data.length) (p : Symbols q) :
    combinedRow data owner blocks K h D group (g.rowIndex p.val.1 p.val.2) = sharedRow blocks K h D group p := by
  rw [SharedRows.Layout.rowIndex,count,← ordinal_shared data.length p]
  exact atOrdinal data owner blocks K h D group (.inr p)

/-- The native scheduler's total width consists exactly of the populated data
widths and one reserved list per strict symbol pair, including co-owned rows. -/
theorem sum_width :
    (∑ i ∈ Finset.range (data.length+q.choose 2), (combinedRow data owner blocks K h D group i).width) =
      (∑ i : Fin data.length, data[i.val].width) + ∑ p : Symbols q, SharedRows.reserved blocks K h D p := by
  let f (e : Fin data.length ⊕ Symbols q) :=
    (e.elim (fun i => dataRow owner data[i.val]) (sharedRow blocks K h D group)).width
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ e, f e := ((ordinal data.length q).sum_comp _).symm.trans
      (Finset.sum_congr rfl fun e _ => congrArg TableRow.width (atOrdinal data owner blocks K h D group e))
    _ = _ := Fintype.sum_sum_type f

/-- The complete post-state of the data writer and appended shared writer has all
four common scheduler columns, including their exact physical widths. -/
theorem recordsMatch_of_writers {w : ℕ} (tab : TableLayout) (g : SharedRows.Layout) (emit : DataWriter.Layout)
    (pub : Arg → Word w) (m : Memory w) (before : ℕ → ℕ)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) before)
    (frame : SymbolFrame g (readings (DataWriter.publish emit pub m)) blocks K h D group)
    (frameBase : g.frame = (pub 0).val) (output : g.records = emit.output) (sched : tab.records = emit.output)
    (count : g.dataCount = emit.count) (dataCount : data.length = emit.count)
    (total : tab.count = g.dataCount+g.groups.choose 2)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    (raw : ∀ i : Fin data.length, DataWriter.demandAt (readings m) (emit.input+i.val*7) = data[i.val])
    (fitted : ∀ i : Fin data.length, ∀ x ∈ DataWriter.record emit (readings m) data[i.val], x < 2^w)
    (owners : ∀ i : Fin data.length, readings m (emit.owners+data[i.val].cell*2) = (owner data[i.val].cell).val) :
    tab.recordsMatch (combinedRow data owner blocks K h D group) before := by
  have gCount := count.trans dataCount.symm
  have size : tab.count = data.length+q.choose 2 := by rw [total,gCount,frame.groups]
  intro k hk
  let ord : Fin (data.length+q.choose 2) := ⟨k,size ▸ hk⟩
  obtain ⟨key,keyEq⟩ := (ordinal data.length q).surjective ord
  have ind : (ordinal data.length q key).val = k := congrArg Fin.val keyEq
  cases key with
  | inl i =>
    change i.val = k at ind
    subst k
    rw [data_at]
    have field (j : Fin 7) := DataWriter.retained_record emit pub m shared frameBase output count sep
      (dataCount ▸ i.isLt) (raw i) (fitted i) j
    simp only [sched,Nat.mul_comm 7 i.val,Nat.add_comm (i.val*7) emit.output]
    refine ⟨?_,?_,?_,?_⟩
    · simpa [DataWriter.record,dataRow] using field 0
    · exact field 1
    · exact (field 2).trans (owners i)
    · exact field 3
  | inr p =>
    have ki : g.rowIndex p.val.1 p.val.2 = k := by rw [SharedRows.Layout.rowIndex,gCount,← ordinal_shared]; exact ind
    rw [← ki]
    rw [shared_at data owner blocks K h D group g gCount p]
    have field (j : Fin 7) := shared.rows p.val.2.val (frame.groups ▸ p.val.2.isLt) p.val.1.val p.property j
    have addr : 7*g.rowIndex p.val.1 p.val.2+tab.records = g.address (g.rowIndex p.val.1 p.val.2) := by
      rw [SharedRows.Layout.address,sched,output,Nat.add_comm]
    simp only [addr]
    refine ⟨?_,?_,?_,?_⟩
    · simpa [SharedRows.Layout.row,sharedRow] using field 0
    · exact (field 1).trans (frame.owners p.val.1)
    · exact (field 2).trans (frame.owners p.val.2)
    · exact (field 3).trans (frame.toDeclarationFields.width p)

/-- Valid source teams and the bound on the two physical volume sums furnish the
native scheduler's full `RowsFit` property. -/
theorem rowsFit {w : ℕ} (tab : TableLayout) (total : tab.count = data.length+q.choose 2)
    (teams : R+1 = tab.teams) (senders : ∀ i : Fin data.length, data[i.val].team < R+1)
    (room : (∑ i : Fin data.length, data[i.val].width) + (∑ p : Symbols q, SharedRows.reserved blocks K h D p) < 2^w) :
    tab.RowsFit w (combinedRow data owner blocks K h D group) := by
  constructor
  · intro k hk
    obtain ⟨key,keyEq⟩ := (ordinal data.length q).surjective (⟨k,total ▸ hk⟩ : Fin (data.length+q.choose 2))
    have hv : (ordinal data.length q key).val = k := congrArg Fin.val keyEq
    rw [← hv,atOrdinal]
    cases key with
    | inl i => exact ⟨by change 1 < 2; decide,teams ▸ senders i,teams ▸ (owner data[i.val].cell).isLt⟩
    | inr p => exact ⟨by change 0 < 2; decide,teams ▸ (group p.val.1).isLt,teams ▸ (group p.val.2).isLt⟩
  · rwa [total,sum_width]

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
