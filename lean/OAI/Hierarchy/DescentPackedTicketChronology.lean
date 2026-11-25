import OAI.Hierarchy.DescentSourceSorted
import OAI.Hierarchy.DescentSharedCableExchange
import OAI.Hierarchy.DescentOrderedResetRows
import OAI.Hierarchy.DescentGroupSiteOrder
import OAI.Hierarchy.DescentObservedReservations

namespace OAI
/-! # True reset ticket chronology from prior source coordinates and the signed physical edge fields -/
namespace Hierarchy.DescentPackedTicketChronology
open DescentCompiler DescentSixParty DescentChosenRouter DescentOrderedWords DescentPacking
open DescentSharedCableNames.Stage DescentColonies Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {J V : Type} [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ} (ready : A.StateBounds S i)
variable (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "serial" => DescentOrderedReset.grains W A.grainCount order
local notation "native" => order.trans Fin.valEmbedding

theorem earlier_grain (x y : Grain A) :
    serial x<serial y ↔ order x.1<order y.1 ∨ x.1=y.1 ∧ x.2.val<y.2.val := by
  rcases x with ⟨e,a⟩
  rcases y with ⟨f,b⟩
  change offset order A.grainCount e+a.val < offset order A.grainCount f+b.val ↔
    order e < order f ∨ e=f ∧ a.val < b.val
  have sep {g h : W.graph.Edge} (lt : order g < order h)
      (s : Fin (A.grainCount g)) (t : Fin (A.grainCount h)) :
      offset order A.grainCount g+s.val < offset order A.grainCount h+t.val :=
    (Nat.add_lt_add_left s.isLt _).trans_le
      ((earlier order A.grainCount g h lt).trans (Nat.le_add_right _ _))
  rcases lt_trichotomy (order e) (order f) with less|eqn|later
  · exact ⟨fun _ => Or.inl less, fun _ => sep less a b⟩
  · have eqn':=order.injective eqn
    subst f;simp
  · constructor
    · intro forward
      exact (lt_asymm forward (sep later b a)).elim
    · rintro (forward | ⟨hit,_⟩)
      · exact (lt_asymm forward later).elim
      · subst f
        exact (lt_irrefl _ later).elim

def outgoingSlot (x : Grain A) : Fin A.cap :=
  outgoing A native S ready ⟨x.1,Nat.zero_lt_of_lt x.2.isLt⟩

def before (site slot within site' slot' within' : ℕ) :=
  site<site' ∨ site=site' ∧ (slot<slot' ∨ slot=slot' ∧ within<within')

theorem actual_before (sorted : SourceSorted W order) (x y : Grain A) :
    serial x<serial y ↔ before (originalId W.graph.Site (W.graph.src x.1)) (outgoingSlot A S ready order x).val x.2.val
      (originalId W.graph.Site (W.graph.src y.1)) (outgoingSlot A S ready order y).val y.2.val := by
  rw [earlier_grain]
  let u:=W.graph.src x.1
  let v:=W.graph.src y.1
  have active (z : Grain A) : 0<W.graph.width z.1 := by
    by_contra no
    have dead:W.graph.width z.1=0:=by omega
    have:=z.2.isLt;simp [GroupStage.grainCount,dead] at this
  rcases lt_trichotomy (originalId W.graph.Site u) (originalId W.graph.Site v) with less|eqn|later
  · have go:=sorted x.1 y.1 (active x) (active y) less
    exact ⟨fun _=>Or.inl less,fun _=>Or.inl go⟩
  · have same:u=v:=(originalId W.graph.Site).injective eqn
    have ord:=outgoing_lt A native S ready ⟨x.1,Nat.zero_lt_of_lt x.2.isLt⟩ ⟨y.1,Nat.zero_lt_of_lt y.2.isLt⟩ same
    have rev:=outgoing_lt A native S ready ⟨y.1,Nat.zero_lt_of_lt y.2.isLt⟩ ⟨x.1,Nat.zero_lt_of_lt x.2.isLt⟩ same.symm
    change (outgoingSlot A S ready order x).val<(outgoingSlot A S ready order y).val ↔ (order x.1).val<(order y.1).val at ord
    change (outgoingSlot A S ready order y).val<(outgoingSlot A S ready order x).val ↔ (order y.1).val<(order x.1).val at rev
    have sameSlot : x.1=y.1 ↔ (outgoingSlot A S ready order x).val=(outgoingSlot A S ready order y).val := by
      constructor
      · intro hit
        have val:=congrArg (fun e=>(order e).val) hit;omega
      · intro hit
        exact order.injective (Fin.ext (by omega))
    change _ ↔ before (originalId W.graph.Site u) _ _ (originalId W.graph.Site v) _ _
    simp only [before,eqn,lt_self_iff_false,false_or,true_and,ord,sameSlot]
   ; rfl
  · have go:=sorted y.1 x.1 (active y) (active x) later
    have neq:x.1≠y.1:=fun h=>by rw [h] at go;exact (lt_irrefl _ go)
    change _ ↔ before (originalId W.graph.Site u) _ _ (originalId W.graph.Site v) _ _
    simp [before,go.not_gt,neq,later.not_gt,later.ne']

/-- With equal old host vertex, no global vertex name enters the source comparison.
The two digits are the original pre-remix group and block recovered from the signed source. -/
theorem site_source {groups : ℕ} (A₀ : GroupStage W G q ε (Fin groups) V k) (vertex : V↪Fin (Fintype.card V))
    (coord : Function.Injective (fun v=>(A₀.pos v,A₀.block v)))
    (u v : W.graph.Site) (same : (A₀.pos u).2=(A₀.pos v).2) :
    A₀.site vertex coord u<A₀.site vertex coord v ↔
      (A₀.pos u).1.val*2^k+(A₀.block u).val < (A₀.pos v).1.val*2^k+(A₀.block v).val := by
  change DescentPhysicalOrder.physical (DescentSiteTape.rank (A₀.siteSlot vertex coord)) u<
    DescentPhysicalOrder.physical (DescentSiteTape.rank (A₀.siteSlot vertex coord)) v ↔ _
  rw [DescentPhysicalOrder.physical_lt_iff]
  change (A₀.siteSlot vertex coord u).val<(A₀.siteSlot vertex coord v).val ↔ _
  rw [A₀.siteSlot_val,A₀.siteSlot_val,same]
  have lex (a b c d M : ℕ) (hb:b<M) (hd:d<M) :
      a*M+b<c*M+d ↔ a<c ∨ a=c ∧ b<d := by
    rcases lt_trichotomy a c with x|x|x
    · have:=Nat.mul_le_mul_right M x;rw [Nat.succ_mul] at this;omega
    · subst c;omega
    · have:=Nat.mul_le_mul_right M x;rw [Nat.succ_mul] at this;omega
  simp only [lex _ _ _ _ _ (A₀.block u).isLt (A₀.block v).isLt,Nat.add_lt_add_iff_right,Nat.add_left_inj]
  have pos:0<Fintype.card V:=Nat.zero_lt_of_lt (vertex (A₀.pos v).2).isLt
  simp [pos.ne',Nat.mul_lt_mul_right pos]

theorem old_source {groups : ℕ} (A₀ : GroupStage W G q ε (Fin groups) V k) (vertex : V↪Fin (Fintype.card V))
    (coord : Function.Injective (fun v=>(A₀.pos v,A₀.block v))) (names : ∀v,originalId W.graph.Site v=(A₀.site vertex coord v).val)
    (u v : W.graph.Site) (same : (A₀.pos u).2=(A₀.pos v).2) :
    originalId W.graph.Site u<originalId W.graph.Site v ↔
      (A₀.pos u).1.val*2^k+(A₀.block u).val < (A₀.pos v).1.val*2^k+(A₀.block v).val := by
  rw [names,names]
  exact site_source A₀ vertex coord u v same

end
end Hierarchy.DescentPackedTicketChronology

end OAI
