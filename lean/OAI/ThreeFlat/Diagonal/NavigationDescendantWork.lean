import OAI.ThreeFlat.Diagonal.PhysicalEndLevel
import OAI.ThreeFlat.Diagonal.NavigationSlotSchedule

namespace OAI
/-! # Summing native per-node work along physical terminal-parent fibers -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open RAM RAM.HistoryNodeDirectory
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {a : RootArchive} (N : Nodes a)

/-- Absolute ordinal of one root in the final consecutive layer. -/
def terminalId (r : Fin a.rootCount) : Fin a.rootsTotal :=
  ⟨a.firstFinal+r.val,by have:=r.isLt;unfold rootsTotal;omega⟩

private theorem lastRoot_terminal (j : Fin a.rootsTotal) (high : a.firstFinal≤j.val) :
    (N.lastRoot j).val=j.val-a.firstFinal := by
  have terminal {n : ℕ} (D : Chronology n) (i : Fin n) (hi : D.firstFinal ≤ i.val) :
      D.root i=i.val-D.firstFinal := by
    rw [Chronology.root,dite_eq_right (Nat.not_lt.mpr hi)]
  exact (terminal N.chronology j (N.first.le.trans high)).trans (congrArg (j.val - ·) N.first)

theorem lastRoot_parent (j : Fin a.rootsTotal) (old : j.val<a.firstFinal) :
    N.lastRoot j=N.lastRoot (N.chronology.parent j) := by
  have earlier {n : ℕ} (D : Chronology n) (i : Fin n) (hi : i.val<D.firstFinal) :
      D.root i=D.root (D.parent i) := by
    conv_lhs => rw [Chronology.root,dite_eq_left hi]
  exact Fin.ext (earlier N.chronology j (old.trans_eq N.first.symm))

abbrev Nonterminal (a : RootArchive) := {j : Fin a.rootsTotal // j.val<a.firstFinal}
abbrev EarlierChild {a : RootArchive} (N : Nodes a) (i : Fin a.rootsTotal) :=
  {j : Nonterminal a // N.chronology.parent j.val=i}

/-- The sum over all descendants reached by the physical parent map telescopes
from local child budgets. The only term left in a root fiber is its final
node's budget. -/
theorem descendant_sum_le (cost potential : Fin a.rootsTotal→ℕ)
    (step : ∀ i,cost i+∑ j : EarlierChild N i,potential j.val.val≤potential i)
    (r : Fin a.rootCount) :
    (∑ i : {i // N.lastRoot i=r},cost i.val)≤potential (terminalId r) := by
  classical
  let mass (i : Fin a.rootsTotal):=if N.lastRoot i=r then potential i else 0
  let paid (i : Fin a.rootsTotal):=if N.lastRoot i=r then cost i else 0
  let parent (j : Nonterminal a) : Fin a.rootsTotal := N.chronology.parent j.val
  have localLaw (i : Fin a.rootsTotal) :
      paid i+(∑ j : {j : Nonterminal a // parent j=i},mass j.val.val)≤ mass i := by
    have belongs (j : {j : Nonterminal a // parent j=i}) : N.lastRoot j.val.val=N.lastRoot i :=
      (lastRoot_parent N j.val.val j.val.property).trans (congrArg N.lastRoot j.property)
    by_cases h : N.lastRoot i=r
    · simp only [paid,mass,belongs,h,ite_true]
      refine (le_of_eq ?_).trans (step i)
      apply congrArg (cost i + ·)
      exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)
    · simp [paid,mass,belongs,h]
  have total:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>localLaw i
  rw [Finset.sum_add_distrib,Fintype.sum_fiberwise parent (fun j=>mass j.val)] at total
  have partition:=Fintype.sum_subtype_add_sum_subtype (fun i : Fin a.rootsTotal=>i.val<a.firstFinal) mass
  let endNode : {i : Fin a.rootsTotal // ¬i.val<a.firstFinal}:=⟨terminalId r,by dsimp only [terminalId];omega⟩
  have unique (i : {i : Fin a.rootsTotal // ¬i.val<a.firstFinal}) :
      N.lastRoot i.val=r ↔ i=endNode := by
    constructor
    · intro h
      have val:=congrArg Fin.val h
      rw [lastRoot_terminal N _ (Nat.le_of_not_gt i.property)] at val
      have hi:=i.property
      apply Subtype.ext
      apply Fin.ext
      change i.val.val=a.firstFinal+r.val
      omega
    · rintro rfl
      apply Fin.ext
      rw [lastRoot_terminal N _ (Nat.le_of_not_gt endNode.property)]
      change (a.firstFinal+r.val)-a.firstFinal=r.val
      omega
  have tail : (∑ j : {i : Fin a.rootsTotal // ¬i.val<a.firstFinal},mass j.val)=potential (terminalId r) := by
    rw [Finset.sum_eq_single endNode]
    · simp only [mass,(unique endNode).mpr rfl,ite_true,endNode]
    · intro i _ ne
      exact ite_eq_right (fun h=>ne ((unique i).mp h))
    · simp
  have expenses : (∑ i : Fin a.rootsTotal,paid i)=(∑ i : {i // N.lastRoot i=r},cost i.val) := by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun i=>N.lastRoot i=r) paid]
    have add_zero_of {x y z : ℕ} (hx : x=z) (hy : y=0) : x+y=z := by omega
    apply add_zero_of
    · exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
        (fun i _ => ite_eq_left i.property)
    · exact Finset.sum_eq_zero (fun i _ => ite_eq_right i.property)
  rw [←partition,tail,expenses] at total
  have cancel {c₁ c₂ p x y : ℕ} (hc : c₁=c₂) (hxy : x=y)
      (bound : c₂+x≤y+p) : c₁≤p := by omega
  refine cancel ?_ ?_ total <;>
    exact Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl)

/-- Direct input for selected_descendant_budget from per-node native work and
the actual capacity stored in each S11 root charge row. -/
theorem selected_budget_of_local {W : ℕ} (slots : ℕ) (facts : ScheduleFacts a W slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^W) (slotsFit : slots≤2^W) (rootsFit : a.rootCount≤2^W)
    (g : Fin a.groups) (s : Fin slots) (cost potential : Fin a.rootsTotal→ℕ)
    (step : ∀ i,cost i+∑ j : EarlierChild N i,potential j.val.val≤potential i)
    (terminal : ∀ r,potential (terminalId r)≤N.work r) :
    let D:=a.selectedDirectory N slots (g.val:Computability.VPVNP.BurstRAM.Word W) (s.val:Computability.VPVNP.BurstRAM.Word W)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)≤a.slotBudget/4 :=
  selected_descendant_budget a N slots facts groupsFit slotsFit rootsFit g s cost
    (fun r=>(descendant_sum_le N cost potential step r).trans (terminal r))


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- All nonterminal rows whose published parent column equals this absolute ordinal. -/
abbrev Incoming (parent : ℕ→ℕ) (firstFinal dest : ℕ) :=
  {i : Fin firstFinal // parent i.val=dest}

private theorem site_for_id {d l : ℕ} {A : State d l} (O : A.ArchiveSites) {i : ℕ}
    (lo : O.layer.first≤ i) (hi : i<O.layer.first+O.layer.count) : ∃ x,O.id x=i := by
  refine ⟨O.ord.symm ⟨i-O.layer.first,by omega⟩,?_⟩
  simp only [State.ArchiveSites.id,Equiv.apply_symm_apply,Nat.add_sub_of_le lo]

private theorem site_id_injective {d l : ℕ} {A : State d l} (O : A.ArchiveSites) :
    Function.Injective O.id := by
  intro x y eq
  apply O.ord.injective
  apply Fin.ext
  exact Nat.add_left_cancel eq

namespace Run

private theorem parent_after_front {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (m : ℕ→ℕ)
    (rows : r.ArchiveRowsStored b m h C O p)
    (asc : ∀ i,i<(r.finalArchive h C O p).1.first → i< m (b.nodes+8*i+1))
    (i : ℕ) (lo : O.layer.first≤ i) (old : i<(r.finalArchive h C O p).1.first) :
    O.layer.first+O.layer.count≤ m (b.nodes+8*i+1) := by
  cases r with
  | done A=>change i<O.layer.first at old;omega
  | step R next=>
    by_cases inside : i<O.layer.first+O.layer.count
    · obtain ⟨x,rfl⟩:=site_for_id O lo inside
      rw [rows.2.1 x,←p.1.row.contiguous]
      exact Nat.le_add_right _ _
    · have:=asc i old
      omega

/-- Each physical move row enumerates the full incoming fiber in the native
archive. This includes exclusion of incoming pointers from any other layer. -/
def ChildFibers (parent : ℕ→ℕ) (firstFinal : ℕ) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → Prop
  | _,_,_,.done _,_,_,_,_ => True
  | _,_,_,.step R next,h,C,_,p =>
    (∀ v,∃ e : Fin p.1.sites.layer.childCount ≃ Incoming parent firstFinal (p.1.sites.id v),
      ∀ j,(e j).val.val=p.1.data.child (p.1.sites.ord v) j) ∧
    ChildFibers parent firstFinal (next h.1) (tailHistory R next h) (C.2 h.1) p.1.sites p.2

private theorem child_fibers_from {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (m : ℕ→ℕ)
    (rows : r.ArchiveRowsStored b m h C O p) (final : ℕ) (hf : final=(r.finalArchive h C O p).1.first)
    (asc : ∀ i,i<final → i< m (b.nodes+8*i+1))
    (before : ∀ i,i<O.layer.first → m (b.nodes+8*i+1)<O.layer.first+O.layer.count) :
    ChildFibers (fun i=>m (b.nodes+8*i+1)) final r h C O p := by
  induction r with
  | done A=>trivial
  | @step d l D lanes A R next ih =>
    let s:=p.1
    let tail:=tailHistory R next h
    have cont : s.sites.layer.first=O.layer.first+O.layer.count:=s.row.contiguous
    have tailFirst : final=((next h.1).finalArchive tail (C.2 h.1) s.sites p.2).1.first:=hf
    have oldStop : s.sites.layer.first≤final:=((next h.1).archive_bounds tail (C.2 h.1) s.sites p.2).1.trans_eq tailFirst.symm
    have stored (x : A.Site) : m (b.nodes+8*(O.id x)+1)=s.sites.id (R.parent h.1 x):=rows.2.1 x
    have fromOld (i : ℕ) (lo : O.layer.first≤ i) (hi : i<s.sites.layer.first) :
        m (b.nodes+8*i+1)<s.sites.layer.first+s.sites.layer.count := by
      obtain ⟨x,rfl⟩:=site_for_id O lo (hi.trans_eq cont)
      rw [stored];exact s.sites.id_lt _
    constructor
    · intro v
      let direct (x : {x // R.parent h.1 x=v}) :
          Incoming (fun i=>m (b.nodes+8*i+1)) final (s.sites.id v) :=
        ⟨⟨O.id x.val,((O.id_lt x.val).trans_eq cont.symm).trans_le oldStop⟩,
          (stored x.val).trans (congrArg s.sites.id x.property)⟩
      have bij : Function.Bijective direct := by
        constructor
        · intro x y e
          exact Subtype.ext (site_id_injective O (congrArg (fun z=>z.val.val) e))
        · intro j
          have eq : m (b.nodes+8*j.val.val+1)=s.sites.id v:=j.property
          have low : O.layer.first≤j.val.val := by
            by_contra! bad
            have left:=(before j.val.val bad).trans_eq cont.symm
            have right : s.sites.layer.first ≤ s.sites.id v:=Nat.le_add_right _ _
            omega
          have high : j.val.val<s.sites.layer.first := by
            by_contra! late
            have cutoff:=(next h.1).parent_after_front tail (C.2 h.1) s.sites p.2 b m rows.2.2
              (by simpa only [←tailFirst] using asc) j.val.val late (j.val.isLt.trans_eq tailFirst)
            have bound:=s.sites.id_lt v
            omega
          obtain ⟨x,id⟩:=site_for_id O low (high.trans_eq cont)
          have belongs : R.parent h.1 x=v := by
            apply site_id_injective s.sites
            rw [←stored,id,eq]
          exact ⟨⟨x,belongs⟩,Subtype.ext (Fin.ext id)⟩
      let e := (s.row.children v).trans (Equiv.ofBijective direct bij)
      exact ⟨e,fun j=>(s.row.childId v j).symm⟩
    · apply ih h.1 tail (C.2 h.1) s.sites p.2 rows.2.2 tailFirst
      intro i hi
      by_cases early : i<O.layer.first
      · exact ((before i early).trans_eq cont.symm).trans_le (Nat.le_add_right _ _)
      · exact fromOld i (Nat.le_of_not_gt early) hi

/-- The real S44 owner scan certifies the child map in every typed stage. -/
theorem child_fibers {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (m : ℕ→ℕ)
    (rows : r.ArchiveRowsStored b m h C O p) (zero : O.layer.first=0) :
    ChildFibers (fun i=>m (b.nodes+8*i+1)) (r.finalArchive h C O p).1.first r h C O p := by
  let final:=(r.finalArchive h C O p).1.first
  let n:=(r.finalArchive h C O p).1.count
  let D:=r.archiveDirectory h C O p b m rows zero final n rfl rfl
  apply child_fibers_from r h C O p b m rows final rfl
  · intro i hi
    let j : Fin (final+n):=⟨i,by omega⟩
    have up:=D.later j hi
    have word:=r.archiveDirectory_parent h C O p b m rows zero final n rfl rfl j hi
    exact up.trans_eq word
  · intro i hi
    rw [zero] at hi
    omega


end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
namespace Run

/-- Per-site native instruction costs are combined only with the typed
children named by this move's physical S45 row. -/
def RowPayments (cost potential : ℕ→ℕ) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → Prop
  | _,_,_,.done _,_,_,_,_=>True
  | _,_,_,.step R next,h,C,_,p=>
    (∀ v,cost (p.1.sites.id v)+(∑ j,potential (p.1.data.child (p.1.sites.ord v) j))≤potential (p.1.sites.id v)) ∧
    RowPayments cost potential (next h.1) (tailHistory R next h) (C.2 h.1) p.1.sites p.2

private theorem all_payments_from {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (parent cost potential : ℕ→ℕ)
    (final : ℕ) (fib : ChildFibers parent final r h C O p) (paid : RowPayments cost potential r h C O p)
    (head : ∀ v,cost (O.id v)+(∑ j : Incoming parent final (O.id v),potential j.val.val)≤potential (O.id v))
    (i : ℕ) (lo : O.layer.first≤ i) (hi : i<(r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count) :
    cost i+(∑ j : Incoming parent final i,potential j.val.val)≤potential i := by
  induction r generalizing i with
  | done A=>
    obtain ⟨v,rfl⟩:=site_for_id O lo hi
    exact head v
  | step R next ih=>
    by_cases here : i<O.layer.first+O.layer.count
    · obtain ⟨v,rfl⟩:=site_for_id O lo here
      exact head v
    have co:=p.1.row.contiguous
    apply ih h.1 (tailHistory R next h) (C.2 h.1) p.1.sites p.2 fib.2 paid.2 _ i (by omega) hi
    intro v
    obtain ⟨e,ids⟩:=fib.1 v
    have eq:=(e.sum_comp (fun j=>potential j.val.val)).symm
    simp only [ids] at eq
    rw [eq]
    exact paid.1 v

/-- Native S44 determines every contributing child. The initial layer has no
children, including when the run consists of a single terminal layer. -/
theorem all_payments {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (m : ℕ→ℕ)
    (rows : r.ArchiveRowsStored b m h C O p) (zero : O.layer.first=0) (cost potential : ℕ→ℕ)
    (seed : ∀ v,cost (O.id v)≤potential (O.id v)) (paid : RowPayments cost potential r h C O p)
    (i : Fin ((r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count)) :
    cost i.val+(∑ j : Incoming (fun j=>m (b.nodes+8*j+1)) (r.finalArchive h C O p).1.first i.val,
      potential j.val.val)≤potential i.val := by
  let final:=(r.finalArchive h C O p).1.first
  let n:=(r.finalArchive h C O p).1.count
  let D:=r.archiveDirectory h C O p b m rows zero final n rfl rfl
  have asc (j : ℕ) (hj : j<final) : j< m (b.nodes+8*j+1) := by
    let k : Fin (final+n):=⟨j,by omega⟩
    exact (D.later k hj).trans_eq (r.archiveDirectory_parent h C O p b m rows zero final n rfl rfl k hj)
  apply all_payments_from r h C O p _ cost potential _ (r.child_fibers h C O p b m rows zero) paid _ i.val (by rw [zero];omega) i.isLt
  intro v
  have empty (j : Incoming (fun j=>m (b.nodes+8*j+1)) final (O.id v)) : False := by
    have stop:=r.parent_after_front h C O p b m rows asc j.val.val (by rw [zero];omega) j.val.isLt
    exact (Nat.not_lt_of_ge (stop.trans_eq j.property)) (O.id_lt v)
  let : IsEmpty (Incoming (fun j=>m (b.nodes+8*j+1)) final (O.id v)):=⟨empty⟩
  change cost (O.id v)+(∑ j : Incoming (fun j=>m (b.nodes+8*j+1)) final (O.id v),potential j.val.val)≤potential (O.id v)
  simpa using seed v


end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open PhysicalStage RAM RAM.HistoryNodeDirectory Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W d l : ℕ} {A : State d l}

/-- The incoming physical memory fiber is exactly the immediate-child type
used by the chronological selected-directory scan. -/
def incomingEquiv {a : RootArchive} (N : Nodes a) (parent : ℕ→ℕ) (final : ℕ)
    (first : a.firstFinal=final)
    (read : ∀ i : Fin a.rootsTotal,i.val<a.firstFinal → (N.chronology.parent i).val=parent i.val)
    (i : Fin a.rootsTotal) : EarlierChild N i ≃ Incoming parent final i.val where
  toFun j:=⟨⟨j.val.val.val,j.val.property.trans_eq first⟩,
    (read j.val.val j.val.property).symm.trans (congrArg Fin.val j.property)⟩
  invFun j:=by
    have early:=j.val.isLt.trans_eq first.symm
    let k : Fin a.rootsTotal:=⟨j.val.val,by unfold rootsTotal;omega⟩
    exact ⟨⟨k,early⟩,Fin.ext ((read k early).trans j.property)⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- End-to-end selector arithmetic for the true archive and greedy schedule.
Per-site native fees use the genuine mounted immediate children, and the
terminal inequality is against the scaled physical charge of the same root. -/
theorem selected_of_archive (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (m : Memory W)
    (rows : r.ArchiveRowsStored a.nodeBank (fun u=>(m u).val) h C O p) (zero : O.layer.first=0)
    (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (card : a.rootCount=(r.finalArchive h C O p).1.count) (start pairs : A.Site→ℕ)
    (slots : ℕ) (cost potential : ℕ→ℕ)
    (seed : ∀ v,cost (O.id v)≤potential (O.id v)) (paid : Run.RowPayments cost potential r h C O p)
    (terminal : ∀ z : Fin a.rootCount,potential (a.firstFinal+z.val)≤a.nodeBank.unitWork*r.chargeAt h C start
      (runRootSite a r h C O p card z))
    (facts : let N:=nodesOfRun a r h C O p m rows zero first card start pairs
      ScheduleFacts a W slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^W) (slotsFit : slots≤2^W) (rootsFit : a.rootCount≤2^W)
    (g : Fin a.groups) (s : Fin slots) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    let D:=a.selectedDirectory N slots (g.val:Word W) (s.val:Word W)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i.val else 0)≤a.slotBudget/4 := by
  intro N D
  let parent (k : ℕ):=(m (a.nodeBank.nodes+8*k+1)).val
  have read (k : Fin a.rootsTotal) (old : k.val<a.firstFinal) : (N.chronology.parent k).val=parent k.val :=
    r.archiveDirectory_parent h C O p a.nodeBank (fun u=>(m u).val) rows zero a.firstFinal a.rootCount first card k old
  have payment (i : Fin a.rootsTotal) :
      cost i.val+(∑ j : EarlierChild N i,potential j.val.val.val)≤potential i.val := by
    let final := (r.finalArchive h C O p).1
    let e := incomingEquiv N parent final.first first read i
    have mass : (∑ j : EarlierChild N i,potential j.val.val.val) =
        ∑ j : Incoming parent final.first i.val,potential j.val.val :=
      e.sum_comp (fun j=>potential j.val.val)
    have fits : i.val<final.first+final.count := by
      change i.val<(r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count
      rw [←first,←card]
      exact i.isLt
    exact (Nat.add_le_add_left mass.le (cost i.val)).trans
      (r.all_payments h C O p a.nodeBank (fun u=>(m u).val) rows zero cost potential seed paid ⟨i.val,fits⟩)
  exact selected_budget_of_local (W:=W) N slots facts groupsFit slotsFit rootsFit g s
    (fun i=>cost i.val) (fun i=>potential i.val) payment terminal


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
namespace Run

/-- A true stage charges its kernel and root emission against the increase
in the scaled, inherited charge of the actual typed owner. -/
def StagePrices (cost fee : ℕ→ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → ℕ → (A.Site→ℕ) → Prop
  | _,_,_,.done _,_,_,_,_,_,_=>True
  | _,_,_,.step R next,h,C,_,p,depth,start=>
    (∀ v,cost (p.1.sites.id v)+fee depth*(∑ x : {x // R.parent h.1 x=v},start x.val)≤
      fee (depth+1)*(R.push h.1 (C.1 h.1) start v)) ∧
    StagePrices cost fee (next h.1) (tailHistory R next h) (C.2 h.1) p.1.sites p.2 (depth+1)
      (R.push h.1 (C.1 h.1) start)

private theorem place_layer_prices {d l : ℕ} {A : State d l} (O : A.ArchiveSites)
    (value : A.Site→ℕ) (prior : ℕ→ℕ) :
    ∃ front : ℕ→ℕ,(∀ i,i<O.layer.first → front i=prior i) ∧ ∀ x,front (O.id x)=value x := by
  let front (i : ℕ) := if inside : O.layer.first≤ i ∧ i<O.layer.first+O.layer.count then
    value (O.ord.symm ⟨i-O.layer.first,by omega⟩) else prior i
  refine ⟨front,?_,?_⟩
  · intro i old
    exact dite_eq_right (fun inside=>Nat.not_le_of_lt old inside.1)
  · intro x
    have inside : O.layer.first≤O.id x ∧ O.id x<O.layer.first+O.layer.count:=
      ⟨Nat.le_add_right _ _,O.id_lt x⟩
    simp only [front,dite_eq_left inside]
    apply congrArg value
    apply O.ord.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change (O.layer.first+(O.ord x).val)-O.layer.first=(O.ord x).val
    omega
/-- Read any level-dependent weight by absolute ordinal. All addresses before
the current layer retain the caller's numbering. -/
private theorem place_stage_prices {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (cost fee : ℕ→ℕ)
    (depth : ℕ) (start : A.Site→ℕ) (prior : ℕ→ℕ) (prices : StagePrices cost fee r h C O p depth start) :
    ∃ potential : ℕ→ℕ,(∀ i,i<O.layer.first → potential i=prior i) ∧
      (∀ x,potential (O.id x)=fee depth*start x) ∧ RowPayments cost potential r h C O p ∧
      ∀ z,potential ((r.finalArchive h C O p).1.first+((r.finalArchive h C O p).2 z).val)=
        fee (r.endLevel h depth)*r.rootArray h C start z := by
  induction r generalizing depth prior with
  | done A=>
    obtain ⟨front,keep,placed⟩:=place_layer_prices O (fun x=>fee depth*start x) prior
    exact ⟨front,keep,placed,trivial,placed⟩
  | @step d l D lanes A R next ih=>
    obtain ⟨front,keep,placed⟩:=place_layer_prices O (fun x=>fee depth*start x) prior
    let s:=p.1
    have cont : s.sites.layer.first=O.layer.first+O.layer.count:=s.row.contiguous
    obtain ⟨pot,frozen,active,rest,terminal⟩:=ih h.1 (tailHistory R next h)
      (C.2 h.1) s.sites p.2 (depth+1) (R.push h.1 (C.1 h.1) start) front prices.2
    have old (x : A.Site) : pot (O.id x)=fee depth*start x :=
      (frozen _ ((O.id_lt x).trans_eq cont.symm)).trans (placed x)
    refine ⟨pot,fun i hi=>(frozen i (by omega)).trans (keep i hi),old,⟨?_,rest⟩,terminal⟩
    intro v
    have sums : (∑ j,pot (s.data.child (s.sites.ord v) j)) =
        fee depth*(∑ x : {x // R.parent h.1 x=v},start x.val) := by
      calc
        _ = ∑ j,fee depth*start (s.row.children v j).val := by
          apply Finset.sum_congr rfl
          intro j _
          rw [s.row.childId,old]
        _ = _ := by rw [←Finset.mul_sum,(s.row.children v).sum_comp (fun x=>start x.val)]
    rw [active,sums]
    exact prices.1 v

theorem endLevel_rows {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) (depth : ℕ) :
    r.endLevel h depth+1=depth+(r.archiveList h C O p seed).length := by
  induction r generalizing depth with
  | done A=>rfl
  | step R next ih=>
    have e:=ih h.1 (tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data (depth+1)
    change _=depth+(_ :: _).length
    rw [List.length_cons]
    change (next h.1).endLevel (tailHistory R next h) (depth+1)+1=_
    omega

/-- Only a scalar comparison at the last level is required to pay the whole
actual archive. Each root receives its own genuine inherited charge. -/
theorem stage_potential {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (cost fee : ℕ→ℕ)
    (depth : ℕ) (start : A.Site→ℕ) (prices : StagePrices cost fee r h C O p depth start)
    (seed : ∀ x,cost (O.id x)≤fee depth*start x) {unitWork : ℕ} (bound : fee (r.endLevel h depth)≤unitWork) :
    ∃ potential : ℕ→ℕ,(∀ x,cost (O.id x)≤potential (O.id x)) ∧ RowPayments cost potential r h C O p ∧
      ∀ z,potential ((r.finalArchive h C O p).1.first+((r.finalArchive h C O p).2 z).val)≤
        unitWork*r.rootArray h C start z := by
  obtain ⟨pot,_,placed,pay,terminal⟩:=place_stage_prices r h C O p cost fee depth start (fun _=>0) prices
  exact ⟨pot,fun x=>(seed x).trans_eq (placed x).symm,pay,
    fun z=>(terminal z).trans_le (Nat.mul_le_mul_right _ bound)⟩


end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open PhysicalStage RAM RAM.HistoryNodeDirectory Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {W d l : ℕ} {A : State d l}

/-- The physical group and slot pay their actual chronological nodes. The
only branch-level comparison is the common final scalar tariff. -/
theorem selected_of_stage_prices (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (m : Memory W)
    (rows : r.ArchiveRowsStored a.nodeBank (fun u=>(m u).val) h C O p) (zero : O.layer.first=0)
    (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (card : a.rootCount=(r.finalArchive h C O p).1.count) (start pairs : A.Site→ℕ)
    (slots : ℕ) (cost fee : ℕ→ℕ) (depth : ℕ) (prices : Run.StagePrices cost fee r h C O p depth start)
    (seed : ∀ x,cost (O.id x)≤fee depth*start x) (bound : fee (r.endLevel h depth)≤a.nodeBank.unitWork)
    (facts : let N:=nodesOfRun a r h C O p m rows zero first card start pairs
      ScheduleFacts a W slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^W) (slotsFit : slots≤2^W) (rootsFit : a.rootCount≤2^W)
    (g : Fin a.groups) (s : Fin slots) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    let D:=a.selectedDirectory N slots (g.val:Word W) (s.val:Word W)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i.val else 0)≤a.slotBudget/4 := by
  obtain ⟨pot,base,increment,root⟩:=r.stage_potential h C O p cost fee depth start prices seed bound
  apply selected_of_archive a r h C O p m rows zero first card start pairs slots cost pot base increment _
    facts groupsFit slotsFit rootsFit g s
  intro z
  let x:=(r.finalArchive h C O p).2.symm (finCongr card z)
  have terminal:=root x
  have id : (r.finalArchive h C O p).1.first+((r.finalArchive h C O p).2 x).val=a.firstFinal+z.val:=by
    dsimp only [x]
    rw [Equiv.apply_symm_apply,←first]; rfl
  rw [id] at terminal
  change pot (a.firstFinal+z.val)≤a.nodeBank.unitWork*r.rootArray h C start ((r.finalSite h).symm (r.finalSite h x))
  simpa only [Equiv.symm_apply_apply] using terminal


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM RAM.HistoryNodeDirectory RAM.TickTerminalRoot HistoryTerminalJoin
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

private theorem sum_at_slot {α : Type*} (xs : List α) (f : α→ℕ) {n : ℕ} (len : n=xs.length) :
    (∑ i : Fin n,f (xs.get (i.cast len)))=(xs.map f).sum := by
  subst n
  rw [←List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map xs f)

omit [Field F] in
/-- The terminal loop uses the remainder of each root's original S43 charge
after paying its selected interior tree. Both transfers draw on one slot. -/
theorem joint_finish_budget {p H J n : ℕ} {arity : Fin n→ℕ}
    (a : RootArchive) (N : Nodes a) (slots : ℕ)
    (facts : ScheduleFacts a (16*a.age^10) slots N.work N.pairs a.ids)
    (groupsFit : a.groups≤2^(16*a.age^10)) (slotsFit : slots≤2^(16*a.age^10))
    (rootsFit : a.rootCount≤2^(16*a.age^10)) (g : Fin a.groups) (s : Fin slots)
    (net : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p)
    (wireStart wirePrefix : ℕ) (m : Memory (16*a.age^10))
    (cg : m (TickWorkspace.base a.age 1)=(g.val:Word (16*a.age^10)))
    (cs : m (TickWorkspace.base a.age 1+3)=(s.val:Word (16*a.age^10)))
    (selectedCount : n=(rootIds a.age (a.summaryHeader N) (a.scheduledOwner N slots) m).length)
    (cost : Fin a.rootsTotal→ℕ) (pot : Fin a.rootsTotal→ℕ)
    (localCost : ∀ i,cost i+(∑ j : EarlierChild N i,pot j.val.val)≤pot i)
    (priced : let xs:=a.slotBlock N slots g.val s.val
      let len : n=xs.length:=by
        rw [selectedCount,a.selected_block N slots facts groupsFit slotsFit g s m cg cs,List.length_map]
      let A:=RAM.TickTerminalRoot.mounted a.age p wireStart wirePrefix
      let init:=rootStart a.age (a.summaryHeader N) (a.scheduledOwner N slots) m
      ∀ i : Fin n,let r:=xs.get (i.cast len)
        pot (terminalId r)+iterationCost A init i.val≤N.work r) :
    let D:=a.selectedDirectory N slots (g.val:Word (16*a.age^10)) (s.val:Word (16*a.age^10))
    let G:=TickSlotForest.network (projected net pins)
    let b:=H-G.internal
    let q:=J-(G.cells+b)
    (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)+
      finishCost (H:=H) (J:=J) net pins wireStart wirePrefix (a.summaryHeader N) (a.scheduledOwner N slots) m≤
      28+11*a.rootCount+7*n+a.slotBudget/4+TickTerminalPadding.budget F b q := by
  intro D G b q
  let xs:=a.slotBlock N slots g.val s.val
  let A:=RAM.TickTerminalRoot.mounted a.age p wireStart wirePrefix
  let init:=rootStart a.age (a.summaryHeader N) (a.scheduledOwner N slots) m
  have len : n=xs.length:=by
    rw [selectedCount,a.selected_block N slots facts groupsFit slotsFit g s m cg cs,List.length_map]
  let sub (r : Fin a.rootCount):=∑ i : {i // N.lastRoot i=r},cost i.val
  have each (i : Fin n) : sub (xs.get (i.cast len))+iterationCost A init i.val≤N.work (xs.get (i.cast len)) :=
    (Nat.add_le_add_right (descendant_sum_le N cost pot localCost _) _).trans (priced i)
  have total:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>each i
  rw [Finset.sum_add_distrib,sum_at_slot xs sub len,sum_at_slot xs N.work len] at total
  have share : (xs.map N.work).sum≤a.slotBudget/4:=a.slotBlock_budget N slots g.val s.val
  have sum:=total.trans share
  have front : (∑ i : Fin a.rootsTotal,if Selected.picked D i.val then cost i else 0)=(xs.map sub).sum:=
    a.selected_descendant_sum N slots facts groupsFit slotsFit rootsFit g s cost
  have reflect : (∑ j ∈ Finset.range n,iterationCost A init (n-(j+1)))=∑ i : Fin n,iterationCost A init i.val:=by
    rw [Fin.sum_univ_eq_sum_range]
    simpa only [Nat.sub_sub,Nat.add_comm] using Finset.sum_range_reflect (iterationCost A init) n
  rw [front]
  change (xs.map sub).sum+((24+11*a.rootCount)+(4+7*n+∑ j ∈ Finset.range n,iterationCost A init (n-(j+1)))+
    TickTerminalPadding.budget F b q)≤_
  rw [reflect]
  omega


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
