import OAI.Hierarchy.DescentMatchedOccurrences

namespace OAI
/-! # Chronological compact ordinals of accepted whole-item units -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {I V : Type*} [Fintype V] [DecidableEq V]

abbrev Active (ds : List (I×Option V)) := {i : Locations ds // (ds.get i).2.isSome}

def byItem (amount : I→ℕ) (ds : List (I×Option V)) :
    Pairs amount ds ≃ (Σ i : Active ds,Fin (amount (ds.get i.val).1)) where
  toFun e := ⟨⟨e.2.1.val,by rw [e.2.1.property];rfl⟩,e.2.2⟩
  invFun e := ⟨(ds.get e.1.val).2.get e.1.property,
    ⟨e.1.val,(Option.some_get e.1.property).symm⟩,e.2⟩
  left_inv := by
    rintro ⟨v,⟨i,hi⟩,s⟩
    have valid : (ds.get i).2.isSome := by rw [hi]; rfl
    have reconstruct (target : V) (seen : (ds.get i).2=some target)
        (j : Fin (amount (ds.get i).1)) :
        (⟨(ds.get i).2.get valid, ⟨i,(Option.some_get valid).symm⟩,j⟩ : Pairs amount ds) =
          ⟨target,⟨i,seen⟩,j⟩ := by
      have chosen : (ds.get i).2.get valid=target :=
        Option.some.inj ((Option.some_get valid).trans seen)
      subst target
      rfl
    exact reconstruct v hi s
  right_inv _ := rfl

def pairNumber (amount : I→ℕ) (ds : List (I×Option V)) :
    Pairs amount ds ≃ Fin (Fintype.card (Pairs amount ds)) :=
  let e := byItem amount ds
  let number := orderedUnits (fun i : Active ds=>amount (ds.get i.val).1) (fun i=>i.val.val)
    (fun _ _ hit=>Subtype.ext (Fin.ext hit))
  (e.trans number).trans (finCongr (Fintype.card_congr e).symm)

theorem pairNumber_val (amount : I→ℕ) (ds : List (I×Option V)) (e : Pairs amount ds) :
    (pairNumber amount ds e).val =
      ProtocolRAMPortRanks.«prefix» (fun i : Active ds=>amount (ds.get i.val).1)
        (fun i=>i.val.val) ((byItem amount ds e).1)+e.2.2.val := rfl

/-- The residual bit within its selected whole item follows all earlier accepted
whole quantities. Rejected rows contribute zero, including when they share a size. -/
theorem pairNumber_prefix (amount : I→ℕ) (ds : List (I×Option V)) (e : Pairs amount ds) :
    (pairNumber amount ds e).val =
      (∑ i : Locations ds,if i.val<e.2.1.val.val ∧ (ds.get i).2.isSome then
        amount (ds.get i).1 else 0)+e.2.2.val := by
  rw [pairNumber_val]
  congr 1
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter]
  change (∑ i : Active ds,if i.val.val<e.2.1.val.val then amount (ds.get i.val).1 else 0)=_
  rw [← Finset.sum_subtype (p:=fun i : Locations ds=>(ds.get i).2.isSome)
    (Finset.univ.filter fun i : Locations ds=>(ds.get i).2.isSome) (fun _=>by simp)
    (fun i=>if i.val < e.2.1.val.val then amount (ds.get i).1 else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

omit [Fintype V] in
theorem thickEnd_prefix {amount : I→ℕ} {input : List I} {cap : V→ℕ}
    (p : Packing amount input cap) (e : Pairs amount p.decisions) :
    (thickEnd p e).2.val =
      (∑ i : Locations p.decisions,if i.val<e.2.1.val.val ∧ (p.decisions.get i).2=some e.1 then
        amount (p.decisions.get i).1 else 0)+e.2.2.val := by
  rw [thickEnd_offset]
  congr 1
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter]
  rw [← Finset.sum_subtype (p:=fun i : Locations p.decisions=>(p.decisions.get i).2=some e.1)
    (Finset.univ.filter fun i : Locations p.decisions=>(p.decisions.get i).2=some e.1)
    (fun _=>by simp) (fun i=>if i.val < e.2.1.val.val then amount (p.decisions.get i).1 else 0),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- Enumerate genuine occupied colonies by the ranks inherited from their
external (vertex, depth, cell) records. Gaps in the rank domain consume no rows. -/
def tableNumberBy {C : Type*} [Fintype C] (amount : I→ℕ) (ds : C→List (I×Option V)) (rank : C↪ℕ) :
    (Σ c,Pairs amount (ds c)) ≃ Fin (Fintype.card (Σ c,Pairs amount (ds c))) :=
  let rows := Equiv.sigmaCongrRight (fun c=>pairNumber amount (ds c))
  let groups := orderedUnits (fun c=>Fintype.card (Pairs amount (ds c))) rank rank.injective
  (rows.trans groups).trans (finCongr (Fintype.card_congr rows).symm)

@[simp] theorem tableNumberBy_val {C : Type*} [Fintype C] (amount : I→ℕ) (ds : C→List (I×Option V))
    (rank : C↪ℕ) (c : C) (e : Pairs amount (ds c)) :
    (tableNumberBy amount ds rank ⟨c,e⟩).val =
      ProtocolRAMPortRanks.«prefix» (fun d=>Fintype.card (Pairs amount (ds d))) rank c+
        (pairNumber amount (ds c) e).val := rfl

/-- Enumerate the complete selected table in public colony order. Within each
colony the compact whole-item ordinal is the chronological one proved above. -/
def tableNumber {C : Type*} [Fintype C] (amount : I→ℕ) (ds : C→List (I×Option V)) :
    (Σ c,Pairs amount (ds c)) ≃ Fin (Fintype.card (Σ c,Pairs amount (ds c))) :=
  tableNumberBy amount ds ((Fintype.equivFin C).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩)

@[simp] theorem tableNumber_val {C : Type*} [Fintype C] (amount : I→ℕ) (ds : C→List (I×Option V))
    (c : C) (e : Pairs amount (ds c)) :
    (tableNumber amount ds ⟨c,e⟩).val =
      ProtocolRAMPortRanks.«prefix» (fun d=>Fintype.card (Pairs amount (ds d)))
        (fun d=>(Fintype.equivFin C d).val) c+(pairNumber amount (ds c) e).val := rfl

end
end Hierarchy.DescentPacking

end OAI
