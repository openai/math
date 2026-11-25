import OAI.Hierarchy.ProtocolRAMReportOrdinal

namespace OAI
/-! # Immutable incident-port and dyadic group coordinates of a mixed native report -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {n groups D w scale γ : ℕ}

/-- Fix the physical stage scale while retaining every reported occurrence in the
native row array. Records of other stages have no transported subslots. -/
def atScale (positive : Fin n → Prop) (stage : Fin n → ℕ) (j : ℕ) (rows : Fin n → ProtocolRAMEmit.Row) (i : Fin n) : ProtocolRAMEmit.Row :=
  { rows i with width := if positive i ∧ stage i=j then (rows i).width else 0 }

/-- A cut at a single stage can be priced from the whole report even
when a dormant row names a supergroup belonging to a different stage. -/
theorem grouped_le_total (rows : Fin n → ProtocolRAMEmit.Row) (groups w m γ : ℕ) :
    (∑ g : Fin groups,count rows w m γ g.val) ≤
      ∑ i : {i : Fin n // TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ},
        pieces rows w i.val := by
  classical
  let P (i : Fin n) := TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ
  let f := pieces rows w
  have unpack (g : Fin groups) : count rows w m γ g.val =
      ∑ i : Fin n,if (rows i).group=g.val ∧ P i then f i else 0 := by
    change (∑ i : {i : Fin n // (rows i).group=g.val ∧ P i},f i.val)=_
    rw [←Finset.sum_subtype (Finset.univ.filter (fun i=>(rows i).group=g.val ∧ P i)) (fun _=>by simp) f,
      Finset.sum_filter]
  simp_rw [unpack]
  rw [Finset.sum_comm]
  change _ ≤ ∑ i : {i : Fin n // P i},f i.val
  rw [←Finset.sum_subtype (Finset.univ.filter P) (fun _=>by simp) f,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hit : P i
  · simp only [hit,and_true]
    by_cases inside : (rows i).group<groups
    · let own : Fin groups := ⟨(rows i).group,inside⟩
      rw [Finset.sum_eq_single own]
      · have inClass : TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ := hit
        simp [own,inClass]
      · intro g _ ne
        exact ite_eq_right (fun h=>ne (Fin.ext h.symm))
      · simp
    · have outside (g : Fin groups) : (rows i).group≠g.val := fun eqn=>inside (by simpa only [eqn] using g.isLt)
      simp [outside]
  · simp [hit]

/-- The sum of the physical group sizes is bounded by the cardinal charge
in the uniform two-dimensional dyadic menu. -/
theorem count_atScale_le (positive : Fin n → Prop) (stage : Fin n → ℕ) (rows : Fin n → ProtocolRAMEmit.Row) (j m γ w groups : ℕ) :
    (∑ g : Fin groups,count (atScale positive stage j rows) w m γ g.val) ≤
      TaggedShorterBudget.active (Finset.univ.filter positive) stage
        (fun i => (rows i).width/(w:ℝ)) m j γ := by
  classical
  apply (grouped_le_total (atScale positive stage j rows) groups w m γ).trans_eq
  let P (i : Fin n) := TaggedShorterBudget.widthIndex m (((atScale positive stage j rows i).width:ℝ)/w)=γ
  let f := pieces (atScale positive stage j rows) w
  change (∑ i : {i : Fin n // P i},f i.val) = _
  rw [←Finset.sum_subtype (Finset.univ.filter P) (fun _=>by simp) f,Finset.sum_filter]
  unfold TaggedShorterBudget.active
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases live : positive i <;> by_cases atRow : stage i=j <;>
    simp [f,pieces,atScale,live,atRow,TaggedShorterBudget.copies]

/-- The installed hardware reserves all the subslots of a physical
incident port, including the inactive ones. The address is independent
of every other port's activity and width. -/
def fixedSlot {ports lanes D : ℕ} (fit : ports*lanes≤D) :
    Fin ports × Fin lanes ↪ Fin D :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb fit)

/-- Dormant records consume no subslots and may reuse any reserved
address. Distinctness is needed only between actual live incident ports. -/
def PortDistinct {ports : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (w scale γ g : ℕ)
    (port : Fin n → Fin ports) : Prop :=
  Set.InjOn (fun i : InGroup rows w scale γ g => port i.val) {i | 0<pieces rows w i.val}

/-- The source and target numbered path embeddings already distinguish
the pair (group, physical incident port). On a given reported group this
is precisely the injectivity needed by the static board. -/
theorem portDistinct_of_grouped {ports : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (w m γ : ℕ)
    (port : Fin n → Fin ports)
    (number : {i : Fin n // 0<pieces rows w i} ↪ Fin groups × Fin ports)
    (groupKey : ∀ i,(number i).1.val=(rows i.val).group)
    (portKey : ∀ i,(number i).2=port i.val) (g : Fin groups) :
    PortDistinct rows w m γ g.val port := by
  intro i hi j hj same
  let a : {i : Fin n // 0<pieces rows w i} := ⟨i.val,hi⟩
  let b : {i : Fin n // 0<pieces rows w i} := ⟨j.val,hj⟩
  have groupEq : (number a).1=(number b).1 := Fin.ext <|
    (groupKey a).trans (i.property.1.trans (j.property.1.symm.trans (groupKey b).symm))
  have portEq : (number a).2=(number b).2 := (portKey a).trans (same.trans (portKey b).symm)
  apply Subtype.ext
  exact congrArg (fun q : {i : Fin n // 0<pieces rows w i}=>q.val) (number.injective (Prod.ext groupEq portEq))

def staticUnit {ports lanes : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (g : Fin groups)
    (port : Bool → Fin n → Fin ports)
    (distinct : ∀ b, PortDistinct rows w scale γ g.val (port b))
    (room : ∀ i,pieces rows w i≤lanes) (fit : ports*lanes≤D) (b : Bool) :
    ProtocolRAMReportedPorts.Unit rows w scale γ g.val ↪ Fin D where
  toFun ij := fixedSlot fit (port b ij.1.val,Fin.castLE (room _) ij.2)
  inj' := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ eqn
    have same := (fixedSlot fit).injective eqn
    obtain rfl := distinct b (show 0<pieces rows w i.val from Nat.zero_lt_of_lt j.isLt)
      (show 0<pieces rows w i'.val from Nat.zero_lt_of_lt j'.isLt) (congrArg Prod.fst same)
    have eqj : j=j' := Fin.ext (congrArg (fun z : Fin ports × Fin lanes => z.2.val) same)
    cases eqj
    rfl

/-- Convert the literal settled per-edge bit bound, including both
prescribed route loads, to the reservation's number of physical pieces. -/
theorem pieces_of_bit_bound (rows : Fin n → ProtocolRAMEmit.Row) (w lanes : ℕ) (hw : 0<w)
    (paid : ∀ i,(rows i).width≤lanes*w) : ∀ i,pieces rows w i≤lanes := by
  intro i
  change ⌈(rows i).width/(w:ℝ)⌉₊≤lanes
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (Nat.cast_pos.mpr hw : 0<(w:ℝ))).mpr
  exact_mod_cast paid i

/-- The actual reservation already bounds every group's number of live
transport units, including all the pieces of a repeated wide row. -/
theorem static_capacity {ports lanes : ℕ} (rows : Fin n → ProtocolRAMEmit.Row)
    (distinct : Function.Injective fun i => (rows i).link) (g : Fin groups)
    (port : Bool → Fin n → Fin ports)
    (disjoint : ∀ b,PortDistinct rows w scale γ g.val (port b))
    (room : ∀ i,pieces rows w i≤lanes) (fit : ports*lanes≤D) :
    count rows w scale γ g.val≤D := by
  let e := (common rows w scale γ g.val distinct).symm.toEmbedding.trans
    (staticUnit rows g port disjoint room fit false)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding e

@[simp] theorem read_staticUnit {ports lanes : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (g : Fin groups)
    (port : Bool → Fin n → Fin ports)
    (portsInj : ∀ b,PortDistinct rows w scale γ g.val (port b))
    (room : ∀ i,pieces rows w i≤lanes) (fit : ports*lanes≤D)
    (b : Bool) (i : InGroup rows w scale γ g.val) (j : Fin (pieces rows w i.val)) :
    staticUnit rows g port portsInj room fit b ⟨i,j⟩ =
      fixedSlot fit (port b i.val,Fin.castLE (room i.val) j) := rfl

end Hierarchy.Tagged.WideStack

end
end OAI
