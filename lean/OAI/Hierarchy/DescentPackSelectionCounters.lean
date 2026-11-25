import OAI.Hierarchy.DescentPackSelectionTrace

namespace OAI
/-! # Turning first-fit receipts into the actual dense and raw pair-number counters -/

namespace Hierarchy.DescentPacking.SelectionTrace
open FirstFitRAM PairRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {w : ℕ} {I V : Type*} [Fintype V] [DecidableEq V]

theorem sum_before {n j : ℕ} (le : j≤n) (f : Fin n→ℕ) :
    (∑i : Fin j,f ⟨i.val,i.isLt.trans_le le⟩)=∑ i : Fin n,if i.val < j then f i else 0 := by
  let e : Fin j ≃ {i : Fin n // i.val < j} :=
    ⟨fun i=>⟨⟨i.val,i.isLt.trans_le le⟩,i.isLt⟩,fun i=>⟨i.val.val,i.property⟩,fun _=>rfl,fun _=>rfl⟩
  rw [←Finset.sum_filter,Finset.sum_subtype (p:=fun i : Fin n=>i.val < j) _ (fun _=>by simp) f]
  exact Fintype.sum_equiv e _ _ (fun _=>rfl)

theorem first_amount {p : Layout} {n : ℕ} (m : Memory w) (r : Room w n p) (i : ℕ) :
    first p n m (p.amount i)=m (p.amount i) := by
  apply history_before
  simpa [capacityBase] using Layout.need_low r i

private theorem original_lt {p : Layout} {n : ℕ} (r : Room w n p) : p.caps≤p.offsets := by
  have reserve := r.reserve
  have start : p.caps≤capacityBase p.bits p.caps p.slots := Nat.le_add_right _ _
  exact start.trans ((Nat.le_add_right _ _).trans ((Nat.le_succ _).trans reserve))

private theorem bit_count {p : Layout} {n : ℕ} (r : Room w n p) : n < 2^w := by
  have := r.bins
  have := r.reserve
  have := r.end_
  dsimp [Prefix.base] at *
  omega

theorem counters {p : Layout} (amount : I→ℕ) (xs : List I) (cap : V→ℕ) (m : Memory w)
    (room : Room w (Fintype.card V) p) (fits : xs.length≤p.slots)
    (values : capacityWords p.caps cap m) (bounded : ∀v,cap v < 2^w)
    (input : ∀i : Fin xs.length,m (p.need+i.val)=(amount (xs.get i):Word w))
    (widths : ∀i∈xs,amount i < 2^w) (j : Locations (pack amount xs cap).decisions) :
    let ds := (pack amount xs cap).decisions
    let o := final p (Fintype.card V) m
    o (Prefix.base p.offsets j.val)=
      (∑i : Fin ds.length,if i.val < j.val ∧ (ds.get i).2.isSome then amount (ds.get i).1 else 0:ℕ) ∧
    o (Prefix.base p.offsets j.val+1)=(∑ i : Fin ds.length,if i.val < j.val then amount (ds.get i).1 else 0:ℕ) := by
  let ds := (pack amount xs cap).decisions
  let n := Fintype.card V
  let mid := first p n m
  have len : ds.length=xs.length := by simpa [ds] using congrArg List.length (pack amount xs cap).order
  have count : n < 2^w := bit_count room
  have wide : 1 < 2^w := by have := room.end_;omega
  have mData (i : Fin ds.length) : Prefix.mass mid p.amount i.val=amount (ds.get i).1 := by
    let pos : Fin xs.length := ⟨i.val,i.isLt.trans_eq len⟩
    have same : (ds.get i).1=xs.get pos := by
      have equ := (pack amount xs cap).order
      change ds.map Prod.fst=xs at equ
      have hit := congrArg (fun l : List I=>l[i.val]?) equ
      simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem (i.isLt.trans_eq len),
        Option.map_some,Option.some.injEq] at hit
      exact hit
    have mem : m (p.amount i.val)=(amount (xs.get pos):Word w) := by
      simpa [Layout.amount,Layout.index,(i.isLt.trans_eq len).trans_le fits,pos] using input pos
    rw [Prefix.mass,show mid (p.amount i.val)=m (p.amount i.val) from first_amount m room i.val,mem,same]
    exact Fin.val_cast_of_lt (widths _ (List.get_mem xs pos))
  have tagData (i : Fin ds.length) :
      mid (p.tag i.val)=(binTag (ds.get i).2:Word w) := by
    have h := decisions amount xs cap m room fits values bounded input widths i
    exact (Prefix.issued_frame n p.amount p.tag p.offsets p.slots mid _ (Layout.tag_low room _)).symm.trans h
  have matchedData (i : Fin ds.length) : Prefix.matched n mid p.amount p.tag i.val=
      if (ds.get i).2.isSome then amount (ds.get i).1 else 0 := by
    rw [Prefix.matched,mData,tagData]
    cases choose : (ds.get i).2 with
    | none => simp [binTag,tag,n,Fin.val_cast_of_lt count]
    | some v =>
      have vi := (Fintype.equivFin V v).isLt
      simp [binTag,tag,Fin.val_cast_of_lt (vi.trans count),n,vi]
  have proof := Prefix.issued n p.amount p.tag p.offsets p.slots mid
    (fun i=>(Layout.need_low room i).trans_le (original_lt room)) (Layout.tag_low room) count wide j.val
      ((j.isLt.trans_eq len).le.trans fits)
  have old (i : Fin j.val) : i.val < ds.length := i.isLt.trans j.isLt
  have raw := sum_before j.isLt.le (fun i : Fin ds.length=>amount (ds.get i).1)
  have live := sum_before j.isLt.le (fun i : Fin ds.length=>if (ds.get i).2.isSome then amount (ds.get i).1 else 0)
  have a : (∑ i : Fin j.val,Prefix.mass mid p.amount i.val)=
      ∑i : Fin ds.length,if i.val < j.val then amount (ds.get i).1 else 0 :=
    (Finset.sum_congr rfl (fun (i : Fin j.val) _=>mData ⟨i.val,old i⟩)).trans raw
  have b : (∑ i : Fin j.val,Prefix.matched n mid p.amount p.tag i.val)=
      ∑i : Fin ds.length,if i.val < j.val ∧ (ds.get i).2.isSome then amount (ds.get i).1 else 0 := by
    rw [Finset.sum_congr rfl (fun (i : Fin j.val) _=>matchedData ⟨i.val,old i⟩),live]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  simpa only [a,b,final,mid,n,ds] using proof

end
end Hierarchy.DescentPacking.SelectionTrace

end OAI
