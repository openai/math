import OAI.Hierarchy.DescentFirstColonyRAM

namespace OAI
/-! # A fixed public site bound with a private suffix key for all ghost rows -/

namespace Hierarchy.DescentFirstColonyRAM.Padding
open DescentFirstOccurrence Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {U C : Type*} [Fintype C] {n limit cells w : ℕ}
variable (row : U ≃ Fin n) (group : U → C) (cover : Function.Surjective group)

def extended (i : Fin limit) : Option C :=
  if h : i.val < n then some (group (row.symm ⟨i.val,h⟩)) else none

omit [Fintype C] in
private theorem extended_cast (le : n ≤ limit) (i : Fin n) :
    extended row group (i.castLE le) = some (group (row.symm i)) :=
  dite_eq_left i.isLt

include cover in
omit [Fintype C] in
private theorem surjective (extra : n < limit) : Function.Surjective (extended (limit:=limit) row group) := by
  rintro (_ | c)
  · exact ⟨⟨n,extra⟩,by simp [extended]⟩
  · obtain ⟨u,rfl⟩ := cover c
    exact ⟨(row u).castLE extra.le,by rw [extended_cast,Equiv.symm_apply_apply]⟩

def keyed (cell : C ↪ Fin cells) : Option C ↪ Fin (cells+1) where
  toFun | some c => (cell c).castSucc | none => Fin.last _
  inj' := by
    rintro (_|a) (_|b) eqn
    · rfl
    · exact False.elim ((cell b).castSucc_ne_last eqn.symm)
    · exact False.elim ((cell a).castSucc_ne_last eqn)
    · exact congrArg some (cell.injective ((Fin.castSucc_injective cells) eqn))

def raw (cell : C ↪ Fin cells) (i : Fin limit) := keyed cell (extended row group i)

omit [Fintype C] in
private theorem first_some (extra : n < limit) (c : C) :
    rank (Equiv.refl _) (extended row group) (surjective row group cover extra) (some c) = rank row group cover c := by
  let group' := extended (limit:=limit) row group
  let r' := rank (Equiv.refl _) group' (surjective row group cover extra)
  obtain ⟨i,hi,old⟩ := rank_at row group cover c
  obtain ⟨j,hj,new_⟩ := rank_at (Equiv.refl _) group' (surjective row group cover extra) (some c)
  have small : j.val < n := by
    by_contra off
    simp [group',extended,off] at hj
  have belongs : group (row.symm ⟨j.val,small⟩) = c := by simpa [group',extended,small] using hj
  have orig := rank_le row group cover ⟨j.val,small⟩
  rw [belongs] at orig
  let target := i.castLE extra.le
  have named : group' target=some c := (extended_cast row group extra.le i).trans (congrArg some hi)
  have lifted := rank_le (Equiv.refl _) group' (surjective row group cover extra) target
  change r' (group' target) ≤ i.val at lifted
  rw [named] at lifted
  change j.val = r' (some c) at new_
  exact le_antisymm (lifted.trans_eq old) (orig.trans_eq new_)

omit [Fintype C] in
private theorem first_none (extra : n < limit) :
    n ≤ rank (Equiv.refl _) (extended row group) (surjective row group cover extra) none := by
  obtain ⟨i,h,eqn⟩ := rank_at (Equiv.refl _) (extended row group) (surjective row group cover extra) none
  have hi : ¬i.val < n := by intro small; simp [extended,small] at h
  exact (Nat.le_of_not_gt hi).trans_eq eqn

theorem compact_real (extra : n < limit) (c : C) :
    (DescentPhysicalOrder.physical (rank (Equiv.refl _) (extended row group)
        (surjective row group cover extra)) (some c)).val =
      (DescentPhysicalOrder.physical (rank row group cover) c).val := by
  let r := rank (Equiv.refl (Fin limit)) (extended row group) (surjective row group cover extra)
  have realRank (d : C) : r (some d) = rank row group cover d :=
    first_some row group cover extra d
  change (DescentPhysicalOrder.physical r (some c)).val = _
  simp only [DescentPhysicalOrder.physical_val]
  apply (Finset.card_bij (s:=Finset.univ.filter (fun d=>rank row group cover d < rank row group cover c))
    (t:=Finset.univ.filter (fun x=>r x < r (some c))) (fun d _=>some d) ?_ ?_ ?_).symm
  · intro d hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [realRank d,realRank c]
    exact (Finset.mem_filter.mp hd).2
  · intro _ _ _ _ h;exact Option.some.inj h
  · rintro (_ | d) h
    · obtain ⟨i,_,hi⟩ := rank_at row group cover c
      have low : n ≤ r none := first_none row group cover extra
      have less : r none < r (some c) := (Finset.mem_filter.mp h).2
      rw [realRank c] at less
      have top := i.isLt
      omega
    · have less : r (some d) < r (some c) := (Finset.mem_filter.mp h).2
      rw [realRank d,realRank c] at less
      exact ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,less⟩,rfl⟩

theorem compact_none (extra : n < limit) :
    (DescentPhysicalOrder.physical (rank (Equiv.refl _) (extended row group)
      (surjective row group cover extra)) none).val = Fintype.card C := by
  let r := rank (Equiv.refl _) (extended row group) (surjective row group cover extra)
  change (DescentPhysicalOrder.physical r none).val = _
  rw [DescentPhysicalOrder.physical_val,←Finset.card_univ]
  apply (Finset.card_bij (s:=Finset.univ) (t:=Finset.univ.filter (fun x=>r x < r none))
    (fun c _=>some c) ?_ ?_ ?_).symm
  · intro c _
    obtain ⟨i,_,hi⟩ := rank_at row group cover c
    have hlo := first_none row group cover extra
    have eqn : r (some c) = rank row group cover c := first_some row group cover extra c
    have bound := i.isLt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [eqn,←hi]
    exact bound.trans_le hlo
  · intro _ _ _ _ eqn; exact Option.some.inj eqn
  · rintro (_ | c) hx
    · exact False.elim ((lt_irrefl (r none)) (Finset.mem_filter.mp hx).2)
    · exact ⟨c,Finset.mem_univ _,rfl⟩

structure Real (row : U ≃ Fin n) (group : U → C) (cover : Function.Surjective group)
    (cell : C ↪ Fin cells) (L : Chart) (m o : Memory w) : Prop where
  site : ∀u,o (L.out+(row u).val)=((DescentPhysicalOrder.physical (rank row group cover) (group u)).val:Word w)
  first : ∀c,(o (L.heads.base+(cell c).val)).val=rank row group cover c+1
  empty : ∀b : Fin cells,(∀c,cell c≠b) → (o (L.heads.base+b.val)).val=0
  compact : ∀c,o (L.starts.base+rank row group cover c)=((DescentPhysicalOrder.physical (rank row group cover) c).val:Word w)
  prior : ∀x < L.heads.base,o x=m x

structure Detailed (limit : ℕ) (row : U ≃ Fin n) (group : U → C) (cover : Function.Surjective group)
    (cell : C ↪ Fin cells) (L : Chart) (m o : Memory w) : Prop extends Real row group cover cell L m o where
  ghost : ∀i : Fin limit, n ≤ i.val → o (L.out+i.val) = (Fintype.card C : Word w)

theorem publish_detail (le : n≤limit) (cell : C ↪ Fin cells) (L : Chart) (space : Room L w limit (cells+1)) :
    (program L w limit (cells+1)).Spec (TraceIntervalScanner.Loaded L.keys.base (raw (limit:=limit) row group cell))
      (Detailed limit row group cover cell L) (clock L limit (cells+1)) := by
  rcases le.eq_or_lt with rfl | extra
  · let packed := cell.trans (Fin.castSuccEmb)
    have exactKey : raw (limit:=n) row group cell=dest row group packed := by
      funext i
      exact congrArg (keyed cell) (show extended row group i = some (group (row.symm i)) from dite_eq_left i.isLt)
    rw [exactKey]
    intro P R K M
    refine Procedure.Spec.mono (A:=program L w n (cells+1)) (post':=Detailed n row group cover cell L)
      (DescentFirstColonyRAM.publish row group cover packed L space) (fun _ h=>h) ?_ le_rfl M
    intro m o h
    exact ⟨⟨h.site,h.first,fun b missing=>h.empty b.castSucc (fun c eqn=>missing c ((Fin.castSucc_injective cells) eqn)),
      h.compact,h.prior⟩,fun i hi=>False.elim (i.isLt.not_ge hi)⟩
  · let g := extended (limit:=limit) row group
    let surj := surjective row group cover extra
    intro P R K M
    refine Procedure.Spec.mono (A:=program L w limit (cells+1)) (post':=Detailed limit row group cover cell L)
      (DescentFirstColonyRAM.publish (Equiv.refl (Fin limit)) g surj (keyed cell) L space)
      (fun _ h=>h) ?_ le_rfl M
    intro m o h
    let ranks := rank (Equiv.refl (Fin limit)) g surj
    have firstReal (c : C) : ranks (some c) = rank row group cover c :=
      first_some row group cover extra c
    have compactReal (c : C) : (DescentPhysicalOrder.physical ranks (some c)).val =
        (DescentPhysicalOrder.physical (rank row group cover) c).val :=
      compact_real row group cover extra c
    have siteRead (i : Fin limit) : o (L.out+i.val) = ((DescentPhysicalOrder.physical ranks (g i)).val : Word w) :=
      h.site i
    refine ⟨⟨?_,?_,?_,?_,h.prior⟩,?_⟩
    · intro u
      have valid : g ((row u).castLE extra.le) = some (group u) := by
        change extended row group ((row u).castLE extra.le) = some (group u)
        rw [extended_cast,Equiv.symm_apply_apply]
      simpa only [Fin.val_castLE,valid,compactReal] using siteRead ((row u).castLE extra.le)
    · intro c
      have value := h.first (some c)
      change (o (L.heads.base+(cell c).val)).val = ranks (some c)+1 at value
      rwa [firstReal] at value
    · intro b missing
      apply h.empty b.castSucc
      rintro (_|c) eqn
      · exact b.castSucc_ne_last eqn.symm
      · exact missing c ((Fin.castSucc_injective cells) eqn)
    · intro c
      have value := h.compact (some c)
      change o (L.starts.base+ranks (some c)) = ((DescentPhysicalOrder.physical ranks (some c)).val : Word w) at value
      rwa [firstReal,compactReal] at value
    · intro i hi
      have ghost : g i = none := dite_eq_right (Nat.not_lt.mpr hi)
      have last : (DescentPhysicalOrder.physical ranks none).val = Fintype.card C :=
        compact_none row group cover extra
      simpa only [ghost,last] using siteRead i

theorem publish (le : n≤limit) (cell : C ↪ Fin cells) (L : Chart) (space : Room L w limit (cells+1)) :
    (program L w limit (cells+1)).Spec (TraceIntervalScanner.Loaded L.keys.base (raw (limit:=limit) row group cell))
      (Real row group cover cell L) (clock L limit (cells+1)) :=
  Procedure.Spec.mono (A:=program L w limit (cells+1)) (publish_detail row group cover le cell L space)
    (fun _ h=>h) (fun _ _ h=>h.toReal) le_rfl

end
end Hierarchy.DescentFirstColonyRAM.Padding

end OAI
