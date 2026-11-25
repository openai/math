import OAI.Hierarchy.DescentOldOccurrenceFibers

namespace OAI
/-! # The predecessors counted by each whole-pack input address -/

namespace Hierarchy.DescentOldOccurrenceRAM
open Computability.BorderVNP.Crossing DescentPacking ProtocolRAMPortRanks
open scoped Classical BigOperators
noncomputable section
variable {d : ℕ} {P : Type*} {bits : P→ℕ} (N : Network d P bits)
    {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)
    (color : N.Site→Bool) (c : C)
local notation "T" => nativeTraffic N core home
local notation "thin" => thinList home color c
local notation "thick" => thickList home color c
local notation "row" => Fintype.equivFin N.Site
local notation "bin" => Fintype.equivFin C

def active (side : Bool) (e : N.Edge) := e∈core ∧ home (N.src e)=c ∧ color (N.src e)=side

theorem outsideThick (v : C) :
    PairRAM.thickOffset N core home color c v =
      count (fun f => active N core home color c true f ∧ bin (home (N.dst f)) < bin v) := by
  unfold PairRAM.thickOffset
  have h (b : C) : Fintype.card (ThickPool T thick b) =
      count (fun f => active N core home color c true f ∧ home (N.dst f)=b) := by
    rw [thick_eq]
    apply count_congr
    intro f
    simp only [active]
    tauto
  simp_rw [h]
  exact prefix_count_fibers (fun f => home (N.dst f)) (active N core home color c true) (fun b=>(bin b).val) v

theorem thick_site (v : C) (j : Fin (thick).length) :
    «prefix» (fun i : Fin (thick).length => T ((thick).get i) v) Fin.val j =
      count (fun f => active N core home color c true f ∧ home (N.dst f) = v ∧
        row (N.src f) < row ((thick).get j)) := by
  have before := middle_site (U := N.Site) (row).toEmbedding (fun u => T u v) (thick)
    (colorSites_ordered home color true c) j
  have colored := colored_amount (U := N.Site) home color true c
    (fun u => if row u < row ((thick).get j) then T u v else 0)
  let ok (u : N.Site) : Prop :=
    (home u = c ∧ color u = true) ∧ row u < row ((thick).get j)
  have fibers := filter_fibers (fun f : N.Edge => f ∈ core ∧ home (N.dst f) = v)
    N.src ok
  refine before.trans (colored.trans (Eq.trans ?_ (fibers.trans ?_)))
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hs : home u = c ∧ color u = true
    · by_cases hb : row u < row ((thick).get j)
      · have hv : ok u := ⟨hs, hb⟩
        simp only [ite_eq_left hs, ite_eq_left hb, ite_eq_left hv]
        exact (traffic_eq N core home u v).trans (count_congr (fun f => by tauto))
      · have hv : ¬ok u := fun h => hb h.2
        simp only [ite_eq_left hs, ite_eq_right hb, ite_eq_right hv]
    · have hv : ¬ok u := fun h => hs h.1
      simp only [ite_eq_right hs, ite_eq_right hv]
  · apply count_congr
    intro f
    dsimp only [ok, active]
    tauto

theorem thin_destination (u : N.Site) (v : C) :
    «prefix» (T u) (fun b=>(bin b).val) v =
      count (fun f=>f∈core ∧ N.src f=u ∧ bin (home (N.dst f)) < bin v) := by
  have at_site : T u = fun b => count (fun f => f ∈ core ∧ N.src f = u ∧ home (N.dst f) = b) :=
    funext (traffic_eq N core home u)
  rw [at_site]
  simpa only [and_assoc, Fin.lt_def] using prefix_count_fibers (fun f=>home (N.dst f))
    (fun f=>f∈core ∧ N.src f=u) (fun b=>(bin b).val) v

theorem thin_site (B : ℕ) :
    let pk := slabPacking T B thin thick
    ∀ (j : Locations pk.decisions) (i : Fin (pk.decisions.get j).1.length),
      PairRAM.rawOffset N core home color B c j+
        «prefix» (fun z : Fin (pk.decisions.get j).1.length=> live T ((pk.decisions.get j).1.get z)) Fin.val i =
        count (fun f=>active N core home color c false f ∧ row (N.src f) < row ((pk.decisions.get j).1.get i)) := by
  intro pk j i
  let ds : List (List N.Site × Option C) := pk.decisions
  let weight : N.Site → ℕ := fun u => live T u
  let ord := (Fintype.equivFin N.Site).toEmbedding
  let blocks : List (List N.Site) := ds.map Prod.fst
  let outer : Fin blocks.length := ⟨j.val, by rw [show blocks.length = pk.decisions.length from List.length_map Prod.fst]; exact j.isLt⟩
  have block_eq : blocks.get outer = (ds.get j).1 := by
    simp only [blocks, outer, List.get_eq_getElem, List.getElem_map]; rfl
  let inner : Fin (blocks.get outer).length :=
    ⟨i.val, by rw [block_eq]; exact i.isLt⟩
  let focus : N.Site := (ds.get j).1.get i
  have current : (blocks.get outer).get inner = focus :=
    getElem_congr block_eq (rfl : inner.val = i.val) inner.isLt
  have stream : blocks.flatten = thin := thin_stream T B thin thick
  have sorted : blocks.flatten.Pairwise (fun x y => ord x < ord y) := by
    rw [stream]
    exact colorSites_ordered home color false c
  have pos := nested_site ord weight blocks sorted outer inner
  rw [list_prefix (amount weight) blocks outer, list_prefix weight (blocks.get outer) inner] at pos
  rw [current, stream] at pos

  have raw : PairRAM.rawOffset N core home color B c j =
      amount (amount weight) (blocks.take outer.val) := by
    let price : List N.Site × Option C → ℕ := fun p => amount weight p.1
    change «prefix» (fun z : Fin ds.length => price (ds.get z)) Fin.val j = _
    refine (list_prefix price ds j).trans ?_
    simp only [amount, blocks, outer, List.map_take, List.map_map, Function.comp_def, price]
  have inside :
      «prefix» (fun z : Fin (ds.get j).1.length => weight ((ds.get j).1.get z)) Fin.val i =
        amount weight ((blocks.get outer).take inner.val) :=
    (list_prefix weight (ds.get j).1 i).trans
      (congrArg (fun xs : List N.Site => amount weight (xs.take i.val)) block_eq.symm)

  have colored := colored_amount (U := N.Site) home color false c
    (fun u => if ord u < ord focus then weight u else 0)
  let ok (u : N.Site) := (home u = c ∧ color u = false) ∧ ord u < ord focus
  have fibers := filter_fibers (fun f : N.Edge => f ∈ core) N.src ok
  refine (congrArg₂ Nat.add raw inside).trans (pos.trans (colored.trans ?_))
  refine Eq.trans ?_ (fibers.trans ?_)
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hs : home u = c ∧ color u = false
    · by_cases hr : ord u < ord focus
      · have hk : ok u := ⟨hs, hr⟩
        simpa only [ite_eq_left hs, ite_eq_left hr, ite_eq_left hk] using live_eq N core home u
      · have hk : ¬ok u := fun h => hr h.2
        simp only [ite_eq_left hs, ite_eq_right hr, ite_eq_right hk]
    · have hk : ¬ok u := fun h => hs h.1
      simp only [ite_eq_right hs, ite_eq_right hk]
  · apply count_congr
    intro f
    change (f ∈ core ∧ ((home (N.src f) = c ∧ color (N.src f) = false) ∧
      ord (N.src f) < ord focus)) ↔ (f ∈ core ∧ home (N.src f) = c ∧
      color (N.src f) = false) ∧ ord (N.src f) < ord focus
    tauto

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
