import OAI.Hierarchy.DescentResetWindowCompare

namespace OAI
/-! # Signed post-reset windows from the actual weighted incident and peer scans -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e : (coarse).graph.Edge => (coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

def rows (h₀ : Host) : Fin (2*(A).cap)→Option (Record (A).degree (A).cap) :=
  DescentResetWindowFields.canonicalRows A ord S B.next.valid names C₀ live h₀

/-- The signed output can be mounted directly by the bounded eight-column
publisher. All positions left empty at either sign are certified absent. -/
theorem complete (h₀ : Host) (j : Fin (2*(A).cap)) :
    let rs:=rows B names h₀
    let panel:=Stage.signedPanel A ord S B.next.valid names h₀ j
    (panel=none→∀a,(rs a).bind (fun r=>read r j)=none) ∧
      (∀t,panel=some t→∃a,(rs a).bind (fun r=>read r j)=some t ∧
        ∀b,b≠a→(rs b).bind (fun r=>read r j)=none) :=
  DescentResetWindowFields.canonical_scope A ord S B.next.valid names C₀ live (emission B) h₀ j

/-- The numeric comparator implemented by an installed row's source coordinate
and actual parent code. A receiving end never supplies its own side-dependent
rank here. -/
def earlier (x y : (coarse).graph.Edge) : Prop :=
  rawSite ((coarse).graph.src x)<rawSite ((coarse).graph.src y) ∨
    rawSite ((coarse).graph.src x)=rawSite ((coarse).graph.src y) ∧
    ((Z).installedResetOrdinal T vertexCode birth x).val<((Z).installedResetOrdinal T vertexCode birth y).val

private theorem prefix_sum_with (pred : (coarse).graph.Edge→Prop) [dec : DecidablePred pred] (e : (coarse).graph.Edge) (positive : 0<wt e) :
    (∑f,if pred f ∧ (C₀).first f<(C₀).first e then (C₀).count f else 0)=
    ∑f,if pred f ∧ earlier B f e then (coarse).graph.width f/(Z).unit else 0 := by
  apply Finset.sum_congr rfl
  intro f _
  change (if pred f ∧ (C₀).first f<(C₀).first e then wt f else 0)=_
  by_cases alive : 0<wt f
  · have order : (C₀).first f < (C₀).first e ↔ earlier B f e := first_before B f e alive positive
    by_cases before : pred f ∧ (C₀).first f < (C₀).first e
    · exact (ite_eq_left before).trans ((weight_quotient B f).trans (ite_eq_left ⟨before.1,order.mp before.2⟩).symm)
    · have absent : ¬(pred f ∧ earlier B f e) := fun present => before ⟨present.1,order.mpr present.2⟩
      exact (ite_eq_right before).trans (ite_eq_right absent).symm
  · have zero : wt f=0:=Nat.eq_zero_of_not_pos alive
    have empty:=((weight_quotient B f).symm.trans zero)
    simp only [zero,empty,ite_self]

theorem prefix_sum (pred : (coarse).graph.Edge→Prop) (e : (coarse).graph.Edge) (positive : 0<wt e) :
    (∑f,if pred f ∧ (C₀).first f<(C₀).first e then (C₀).count f else 0)=
    ∑f,if pred f ∧ earlier B f e then (coarse).graph.width f/(Z).unit else 0 :=
  prefix_sum_with B pred e positive

/-- The strictly positive resident parents are placed by the first genuine
incidence, hence the per-site sum can be computed from just `cap` slots. -/
def residentAt (h₀ : Host) (j : Fin (A).cap) : Option (Local C₀ h₀) :=
  if found : ∃e,DescentResetWindowFields.residentAddress A ord S B.next.valid C₀ h₀ e=j
    then some found.choose else none

theorem resident_at (h₀ : Host) (e : Local C₀ h₀) :
    residentAt B h₀ (DescentResetWindowFields.residentAddress A ord S B.next.valid C₀ h₀ e)=some e := by
  let addr:=DescentResetWindowFields.residentAddress A ord S B.next.valid C₀ h₀
  have found : ∃f,addr f=addr e:=⟨e,rfl⟩
  exact (dite_eq_left found).trans (congrArg some (addr.injective found.choose_spec))

theorem resident_sum (h₀ : Host) (cost : (coarse).graph.Edge→ℕ)
    (outside : ∀e,¬(0<wt e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀))→cost e=0) :
    (∑j : Fin (A).cap,(residentAt B h₀ j).elim 0 (fun f=>cost f.val))=∑e,cost e := by
  let addr:=DescentResetWindowFields.residentAddress A ord S B.next.valid C₀ h₀
  let active:=Finset.univ.map addr
  let charge (j : Fin (A).cap):=(residentAt B h₀ j).elim 0 (fun f=>cost f.val)
  have keep : ∑j,charge j=∑j∈active,charge j := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ miss
    have off : ¬∃f,addr f=j := by
      rintro ⟨f,eqn⟩
      exact miss (Finset.mem_map.mpr ⟨f,Finset.mem_univ _,eqn⟩)
    change (residentAt B h₀ j).elim 0 (fun f=>cost f.val)=0
    have absent : residentAt B h₀ j = none := dite_eq_right off
    rw [absent]
    rfl
  have atSlot (f : Local C₀ h₀) : charge (addr f)=cost f.val := by
    change (residentAt B h₀ (addr f)).elim 0 (fun t=>cost t.val)=_
    rw [resident_at]
    rfl
  change (∑j,charge j)=_
  rw [keep]
  change (∑j∈Finset.univ.map addr,charge j)=_
  rw [Finset.sum_map]
  simp only [atSlot]
  let hit:=fun e : (coarse).graph.Edge=>0<wt e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀)
  have missing : ∑e∈Finset.univ.filter (fun f=>¬hit f),cost e=0 := by
    apply Finset.sum_eq_zero
    exact fun e miss=>outside e (Finset.mem_filter.mp miss).2
  have parts := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (f:=cost) (p:=hit)
  have whole : (∑e∈Finset.univ.filter hit,cost e) = ∑e,cost e :=
    (congrArg (fun t => (∑e∈Finset.univ.filter hit,cost e) + t) missing.symm).trans parts
  apply Eq.trans _ whole
  exact (Finset.sum_subtype _ (fun _=>by simp; rfl) _).symm

/-- All three offsets are literal masked weighted sums on the same list of
installed parents. The passive endpoint of a tether retains the actual source
handle. A loop contributes once to each endpoint count even though it has
two different signed output slots. -/
theorem row_scans (h₀ : Host) (f₀ : Roster.Face A ord C₀ h₀) :
    let e:=f₀.val.1
    let entry:=DescentResetWindowFields.record A ord S B.next.valid C₀ live h₀ f₀
      (DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ h₀ f₀)
    let amount:=fun a : (coarse).graph.Edge=>(coarse).graph.width a/(Z).unit
    let before:=earlier B
    entry.position=(∑a,if ((C₀).src a=h₀ ∨ (C₀).dst a=h₀) ∧ before a e then amount a else 0) ∧
      entry.shared=(∑a,if (C₀).parallel ((C₀).src e) ((C₀).dst e) a ∧ before a e then amount a else 0) ∧
      entry.atSource=(∑a,if ((C₀).src a=(C₀).src e ∨ (C₀).dst a=(C₀).src e) ∧ before a e then amount a else 0) ∧
      entry.count=amount e := by
  intro e entry amount before
  let resident:=Roster.resident A ord C₀ h₀ f₀
  let root:= (C₀).src e
  let source : Local C₀ root:=⟨e,f₀.property.1,Or.inl rfl⟩
  have positive : 0<wt e:=f₀.property.1
  have pos := prefix_sum_with B (fun a => (C₀).src a=h₀ ∨ (C₀).dst a=h₀) e positive
  have serial := prefix_sum B ((C₀).parallel ((C₀).src e) ((C₀).dst e)) e positive
  have src := prefix_sum_with B (fun a => (C₀).src a=root ∨ (C₀).dst a=root) e positive
  refine ⟨(Incidence.initial C₀ h₀ fit resident).trans pos,
    ((C₀).first_serial e positive).trans serial,
    (Incidence.initial C₀ root fit source).trans src,weight_quotient B e⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
