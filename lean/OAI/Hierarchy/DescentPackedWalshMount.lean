import OAI.Hierarchy.DescentPackedWalshResident

namespace OAI
/-! # A calendar of immutable reset images occupies one prefix disjoint from all mutable scratch -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

theorem literal_after (E : EstimatorArena) (m : Memory w) {z : ℕ} (past : E.staticEnd≤z) :
    E.literal m z=m z := by
  obtain ⟨a,b,c,d,e,f,g⟩:=E.areas
  have sq : E.squareAt+2^(smallKey E.low E.precision)≤z:=past
  have top : E.squareAt≤z := (Nat.le_add_right _ _).trans sq
  have transform : E.transformAt≤z := d.trans top
  unfold literal initial
  rw [mounted_outside E.transformAt z _ _ E.hosts E.precision (Or.inr (by
    simpa only [axesList,List.length_map,List.length_reverse,List.length_finRange,squareAt,dim] using top))]
  rw [squareROM,ite_eq_left top,dite_eq_right (by omega)]
  simp only [baseMemory,ite_eq_right (show ¬(E.orderAt≤z ∧ z<E.transformAt) by omega)]
  rw [E.plan.mount_high E.reduceAt _ E.plan.depth z (c.trans transform)]
  exact Weight.frame _ _ _ _ _ _ _ _ (Or.inr (b.trans (c.trans transform)))

theorem literal_inside (E : EstimatorArena) (a b : Memory w) (z : ℕ)
    (lo : E.origin≤z) (hi : z<E.staticEnd) : E.literal a z=E.literal b z := by
  by_cases old : z<E.transformAt
  · rw [E.literal_low a old,E.literal_low b old]
    by_cases prior : z<E.orderAt
    · rw [E.lower_reduce a z prior,E.lower_reduce b z prior]
      by_cases left : z<E.reduceAt
      · rw [E.plan.mount_low _ _ _ _ left,E.plan.mount_low _ _ _ _ left]
        simp only [Weight.install,ite_eq_left (show E.origin≤z ∧ z<E.origin+
          Weight.footprint E.hosts E.high E.low E.precision E.gainBits from ⟨lo,left⟩)]
      · exact E.plan.mount_inside _ _ _ _ _ (by omega) prior
    · simp [baseMemory,show E.orderAt≤z by omega,old]
  · by_cases squared : E.squareAt≤z
    · unfold literal initial
      have beyond : E.transformAt+((axesList E.high E.low).map axis).length*
          span E.hosts E.high E.low E.precision≤z := by simpa [axesList,squareAt,dim] using squared
      rw [mounted_outside _ _ _ _ _ _ (Or.inr beyond),mounted_outside _ _ _ _ _ _ (Or.inr beyond)]
      simp only [squareROM,ite_eq_left squared,dite_eq_left (show z-E.squareAt<2^(smallKey E.low E.precision) by
        change z<E.squareAt+2^(smallKey E.low E.precision) at hi;omega)]
    · have started : E.transformAt≤z := by omega
      let width:=span E.hosts E.high E.low E.precision
      have widthPos : 0<width:=by unfold width span;positivity
      have physical : (z-E.transformAt)/width<E.dim := by
        apply (Nat.div_lt_iff_lt_mul widthPos).mpr
        change ¬E.transformAt+E.dim*width≤z at squared
        omega
      have lengthOK : (z-E.transformAt)/width<((axesList E.high E.low).map axis).length := by simpa [axesList,dim] using physical
      have atAxis := List.getElem?_eq_getElem lengthOK
      dsimp only [width] at atAxis
      simp only [literal,initial,mounted,ite_eq_left started]
      rw [atAxis]

/-- The initial ROM for arbitrarily many public reset arenas is installed before dense scratch,
with no literal words allocated by the individual stages' data gaps. -/
def mountCalendar (stages : List EstimatorArena) (base : Memory w) : Memory w :=
  stages.foldr (fun E m=>E.literal m) base

theorem present {E : EstimatorArena} (stages : List EstimatorArena) (base : Memory w)
    (disjoint : stages.Pairwise (fun L R=>L.staticEnd≤R.origin)) (used : E∈stages) :
    E.literal (mountCalendar stages base)=mountCalendar stages base := by
  funext z
  by_cases lo : z<E.origin
  · exact E.literal_before _ lo
  by_cases hi : z<E.staticEnd
  · have fixed : ∀st : List EstimatorArena,st.Pairwise (fun L R=>L.staticEnd≤R.origin)→E∈st→
        ∀m : Memory w,mountCalendar st m z=E.literal base z := by
      intro st separated found
      induction st with
      | nil=>simp at found
      | cons a tail ih=>
        intro m
        rw [List.pairwise_cons] at separated
        rcases List.mem_cons.mp found with rfl|b
        · exact E.literal_inside _ _ z (by omega) hi
        · exact (a.literal_after _ (by have old:=separated.1 E b;omega)).trans (ih separated.2 b m)
    exact (E.literal_inside _ _ _ (by omega) hi).trans (fixed stages disjoint used base).symm
  · exact E.literal_after _ (by omega)

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
