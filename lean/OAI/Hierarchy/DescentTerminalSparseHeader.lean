import OAI.Hierarchy.DescentTerminalHeaderGroups

namespace OAI
/-! # The native profile stream may use the received nonempty pairs and either actual cable end -/

namespace Hierarchy.DescentTerminalSparseHeader
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalHeaderGroups
open DescentTerminalDenseWindow DescentTerminalDenseHeader ThreeFlat.Routing
open scoped BigOperators Classical
noncomputable section

variable {D S p q : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S)

def occupied (limit : ℕ) := ((Finset.univ.filter (fun e : N.Edge=>0<N.width e)).image (pairIndex N home)).filter (·<limit)

omit [Fintype P] in
theorem positive_iff (t : ℕ) : 0<pairMass N home t ↔ ∃e : N.Edge,0<N.width e ∧ pairIndex N home e=t := by
  constructor
  · intro positive
    by_contra! h
    have zero : pairMass N home t=0 := by
      apply Finset.sum_eq_zero
      intro e he
      have eq := (Finset.mem_filter.mp he).2
      by_contra ne
      exact h e (Nat.pos_of_ne_zero ne) eq
    omega
  · rintro ⟨e,width,eq⟩
    apply width.trans_le
    exact Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ e,eq⟩)

omit [Fintype P] in
theorem occupied_sort (limit : ℕ) : (occupied N home limit).sort =
    (List.range limit).filter (fun i=>decide (0<pairMass N home i)) := by
  let keep:=(List.range limit).filter (fun i=>decide (0<pairMass N home i))
  have set : keep.toFinset=occupied N home limit := by
    ext a
    simp only [keep,List.mem_toFinset,List.mem_filter,List.mem_range,decide_eq_true_eq,positive_iff,
      occupied,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
    tauto
  rw [←set]
  apply (List.toFinset_sort (· ≤ ·) ((List.nodup_range (n:=limit)).filter _)).mpr
  exact ((Finset.sort_range limit) ▸ (Finset.pairwise_sort (Finset.range limit) (· ≤ ·))).filter _

variable {L : Order N S p}

/-- For a fixed pair, the sequence of clipped cable widths is literally
the same at the two physical ends, even for parallel cables. -/
theorem sides (g h : GroupBlock N L) (same : g.tag=h.tag) :
    Fintype.card (Order.At L g.site g.group)=Fintype.card (Order.At L h.site h.group) ∧
      ∀k,lengthAt g.lengths k=lengthAt h.lengths k := by
  rcases g with ⟨i,j,g,near⟩
  rcases h with ⟨a,b,h,far⟩
  rcases (pair_iff i j a b).mp same with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have eq : g=h:=Subtype.ext (near.trans far.symm)
    subst h
    exact ⟨rfl,fun _=>rfl⟩
  · have eq : h=Order.partner L g near := Subtype.ext (far.trans (Order.partner_val L g near).symm)
    subst h
    let mv:=Order.transfer L g near
    have size:=Fintype.card_congr mv
    refine ⟨size,fun k=>?_⟩
    by_cases live : k<Fintype.card (Order.At L i g)
    · let u:=(Order.inGroup L i g).symm ⟨k,live⟩
      have other : k<Fintype.card (Order.At L j (Order.partner L g near)):=size ▸ live
      have v : Order.inGroup L j (Order.partner L g near) (mv u)=⟨k,other⟩ := Fin.ext (by
        simpa [u,mv] using Order.transfer_rank L g near u)
      simp only [lengthAt,dite_eq_left live,dite_eq_left other,GroupBlock.lengths,groupLengths,←v,Equiv.symm_apply_apply]
      rfl
    · have other : ¬k<Fintype.card (Order.At L j (Order.partner L g near)):=size ▸ live
      simp [lengthAt,live,other]

theorem side_rows (g h : GroupBlock N L) (same : g.tag=h.tag) : g.rows q=h.rows q := by
  obtain ⟨sz,atBit⟩:=sides N g h same
  apply List.ext_getElem
  · simpa [GroupBlock.rows] using congrArg (fun n=>poolBatchCount n q) sz
  · intro k kr ks
    simp only [GroupBlock.rows,chunkRows,List.getElem_ofFn]
    funext s
    exact Fin.ext (atBit (k*q+s.val))

variable (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L'" => order N home native p external nodes ops

/-- Finite stream from a sparse, ordered catalogue of actual cable groups.
The local row table can use whichever endpoint its native header names.
There is no scan of the square of the number of candidate homes. -/
theorem sparse (hp : 0<p) (limit : ℕ) (groups : List (GroupBlock N L'))
    (catalog : groups.map GroupBlock.tag=(occupied N home limit).sort)
    (active : ∀g∈groups,0<pairMass N home g.tag) :
    groups.flatMap (fun g=>g.rows q)=
      stream N home native external nodes ops q hp limit := by
  let block:=blockRows N home native external nodes ops q hp
  have each : ∀g∈groups,g.rows q=block g.tag := by
    intro g h
    have live:=active g h
    change _=if h : 0<pairMass N home g.tag then _ else _
    rw [dite_eq_left live]
    apply side_rows N
    exact (selected_tag N home native external nodes ops hp g.tag live).symm
  have skip (l : List ℕ) :
      (l.filter (fun n=>decide (0<pairMass N home n))).flatMap block=l.flatMap block := by
    induction l with
    | nil=>rfl
    | cons a l ih=>
      by_cases h : 0<pairMass N home a
      · simp [h,ih]
      · simp [h,ih,block,blockRows]
  calc
    _ = groups.flatMap (fun g=>block g.tag) := List.flatMap_congr each
    _ = (groups.map GroupBlock.tag).flatMap block :=
      (List.flatMap_map GroupBlock.tag block groups).symm
    _ = _ := by rw [catalog,occupied_sort,skip]; rfl

end
end Hierarchy.DescentTerminalSparseHeader

end OAI
