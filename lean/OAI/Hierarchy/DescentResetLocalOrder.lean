import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentCableDonorNames
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # A fresh source-local comparison order after an actual reset -/

namespace Hierarchy.DescentResetLocalOrder
open DescentSixParty DescentSharedCableNames DescentSharedCableNames.Stage
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
local notation "E" => W.graph.Edge
local notation "active" => {e : E // e∈W.core}
local notation "B" => Stage.source A native
local notation "src" => fun e : active => W.graph.src (Subtype.val e)

def firstGrain (e : active) : Stage.Grain A := ⟨e.val,⟨0,A.quantum_positive _ e.property⟩⟩

def incidence (e : active) : ↥((B).incident (Stage.home A (src e))) :=
  ⟨Stage.stream A native (firstGrain A e),by
    apply Finset.mem_filter.mpr;refine ⟨Finset.mem_univ _,Or.inl ?_⟩
    simp only [Stage.source,Equiv.symm_apply_apply,firstGrain]⟩

/-- This is the sorted local incidence position of the first actual quantum.
Core quanta are positive. Tethers, including empty ones, retain their own band. -/
def ticket (e : active) : Fin A.cap :=
  (B).position (Stage.measured A native S ready) _ (incidence A native e)

theorem ticket_signed (e : active) :
    (ticket A native S ready e).val=
      (Stage.signed A native S ready (A.pos (src e)) (A.block (src e))
        (.inl ⟨⟨e.val,rfl,rfl⟩,(firstGrain A e).2⟩)).val := by
  change _=(ticket A native S ready e).val+A.cap*0
  simp

private theorem priority (e f : active) :
    Stage.stream A native (firstGrain A e)<Stage.stream A native (firstGrain A f) ↔ native e.val<native f.val := by
  have mono (a b : active) (lt : native a.val<native b.val) :
      Stage.stream A native (firstGrain A a)<Stage.stream A native (firstGrain A b) := by
    change ProtocolRAMPortRanks.«prefix» A.grainCount native a.val+0<
      ProtocolRAMPortRanks.«prefix» A.grainCount native b.val+0
    have span:=ProtocolRAMPortRanks.prefix_disjoint A.grainCount native lt
    have positive:=A.quantum_positive _ a.property
    omega
  constructor
  · intro lt
    by_contra! off
    rcases off.eq_or_lt with eqn|right
    · obtain rfl : f=e := Subtype.ext (native.injective eqn)
      exact lt.false
    · exact lt.not_gt (mono _ _ right)
  · apply mono

theorem ticket_lt {e f : active} (same : src e=src f) :
    ticket A native S ready e<ticket A native S ready f ↔ native e.val<native f.val := by
  have atCell {x y : Stage.Host J V k} (h : x=y) (p : ↥((B).incident x)) (q : ↥((B).incident y)) :
      (B).position (Stage.measured A native S ready) x p<(B).position (Stage.measured A native S ready) y q ↔ p.val<q.val := by
    subst y;exact (B).position_lt _ _ _ _
  change (B).position _ _ (incidence A native e)<(B).position _ _ (incidence A native f) ↔ _
  rw [atCell (congrArg (Stage.home A) same)]
  exact priority A native e f

theorem unique_ticket (e f : active) (same : src e=src f)
    (eqn : ticket A native S ready e=ticket A native S ready f) : e=f := by
  apply Subtype.ext
  apply native.injective
  apply le_antisymm
  · exact le_of_not_gt (fun lt=>((ticket_lt A native S ready same.symm).mpr lt).ne eqn.symm)
  · exact le_of_not_gt (fun lt=>((ticket_lt A native S ready same).mpr lt).ne eqn)

variable (site : W.graph.Site↪ℕ)
def eligibleCode : active↪ℕ :=
  DescentCableDonorNames.sourceGrouped src site (ticket A native S ready) (unique_ticket A native S ready)

/-- The global sparse names concatenate actual sources in their fixed host
order. Within one source, every physical edge uses its chronological reset
ordinal. This includes unmarked, positive-width hub limbs. -/
def allCode (A : GroupStage W G price ε J V k) (native : E↪ℕ)
    (S : DescentCompiler.AtomSchedule) (_ready : A.StateBounds S i) (site : W.graph.Site↪ℕ) : E↪ℕ :=
  let bound:=(Finset.univ.sup native)+1
  let digit : E→Fin bound:=fun e=>⟨native e,Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))⟩
  DescentCableDonorNames.sourceGrouped W.graph.src site digit
    (fun _ _ _ same=>native.injective (congrArg Fin.val same))

theorem code_val (e : E) : allCode A native S ready site e=
    site (W.graph.src e)*((Finset.univ.sup native)+1)+native e := rfl

theorem adjacent {x y : E} (same : W.graph.src x=W.graph.src y) (prior : native y=native x+1) :
    allCode A native S ready site y=allCode A native S ready site x+1 := by
  simp only [code_val,same,prior,Nat.add_assoc]

theorem positive_before_next {x y : E} (same : W.graph.src x=W.graph.src y) (prior : native y=native x+1)
    (e : E) : allCode A native S ready site e<allCode A native S ready site y ↔
      allCode A native S ready site e<allCode A native S ready site x ∨ e=x := by
  rw [adjacent A native S ready site same prior,Nat.lt_succ_iff,le_iff_lt_or_eq]
  simp only [Function.Embedding.apply_eq_iff_eq]

/-- Each comparison uses a source number and the first actual local signed
port, including the unmarked cables. The global pitch enters only the proof. -/
theorem positive_compare (x y : Positive A) :
    allCode A native S ready site x.val<allCode A native S ready site y.val ↔
      site (W.graph.src x.val)<site (W.graph.src y.val) ∨
      (W.graph.src x.val=W.graph.src y.val ∧ outgoing A native S ready x<outgoing A native S ready y) := by
  let D:=(Finset.univ.sup native)+1
  have room (e : E) : native e<D:=Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))
  have order {u v : E} (earlier : site (W.graph.src u)<site (W.graph.src v)) :
      allCode A native S ready site u<allCode A native S ready site v := by
    rw [code_val,code_val]
    change site (W.graph.src u)*D+native u<site (W.graph.src v)*D+native v
    calc
      _ < (site (W.graph.src u)+1)*D := by rw [Nat.succ_mul];exact Nat.add_lt_add_left (room u) _
      _ ≤ site (W.graph.src v)*D := Nat.mul_le_mul_right D earlier
      _ ≤ _ := Nat.le_add_right ..
  rcases lt_trichotomy (site (W.graph.src x.val)) (site (W.graph.src y.val)) with less|eqn|more
  · exact iff_of_true (order less) (.inl less)
  · have same:=site.injective eqn
    rw [code_val,code_val,same,Nat.add_lt_add_iff_left]
    simp [outgoing_lt A native S ready x y same]
  · refine iff_of_false (not_lt_of_gt (order more)) ?_
    rintro (bad|⟨same,_⟩)
    · exact more.not_gt bad
    · exact more.ne (congrArg site same.symm)

def order : E≃Fin (Fintype.card E) := DescentPhysicalOrder.physical (allCode A native S ready site)

theorem on_source (e f : active) (same : src e=src f) :
    order A native S ready site e.val<order A native S ready site f.val ↔
      ticket A native S ready e<ticket A native S ready f := by
  rw [order,DescentPhysicalOrder.physical_lt_iff,code_val,code_val]
  change W.graph.src e.val=W.graph.src f.val at same
  rw [same,Nat.add_lt_add_iff_left]
  exact (ticket_lt A native S ready same).symm

theorem preserves (e f : active) (same : src e=src f) :
    order A native S ready site e.val<order A native S ready site f.val ↔ native e.val<native f.val :=
  (on_source A native S ready site e f same).trans (ticket_lt A native S ready same)

end
end Hierarchy.DescentResetLocalOrder

end OAI
