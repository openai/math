import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveRun
import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows

namespace OAI
/-! # The selected history's literal outgoing node and charge banks -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalStage
open scoped Fin.CommRing Classical
noncomputable section

def records (xs : List NodeRow) : List Layers := xs.map (fun q=>⟨q.layer,q.parent⟩)

def program : (xs : List NodeRow) → Program (records xs)
  | [] => ⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  | q::qs =>
    { data := Fin.cases (motive:=fun i=>LayerData ((records (q::qs)).get i).actual)
        q.data (fun i=>(program qs).data i)
      owners := Fin.cases (motive:=fun i=>Fin ((records (q::qs)).get i).actual.count → ℕ)
        q.owners (fun i=>(program qs).owners i) }

def view {rs : List Layers} (P : Program rs) (i : Fin rs.length) : NodeRow :=
  ⟨(rs.get i).actual,(rs.get i).parent,P.data i,P.owners i⟩

theorem every_view (xs : List NodeRow) (q : NodeRow) (mem : q∈xs) :
    ∃ i : Fin (records xs).length, view (program xs) i=q := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with rfl|rest
    · exact ⟨⟨0,Nat.zero_lt_succ _⟩,rfl⟩
    · obtain ⟨i,eq⟩:=ih rest
      exact ⟨i.succ,eq⟩

/-- The tuple of view rows is exactly the selected trace's typed archive. -/
theorem written_rows {W : ℕ} (a : NodeArchive) (xs : List NodeRow) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a (records xs) budget) (ordered : Chronological (records xs))
    (old : ∀ i j k, ((program xs).data i).child j k<((records xs).get i).actual.first)
    (fit : ∀ (i : Fin (records xs).length) j c,
      ((program xs).data i).cost a.banks (prior a (decrement a (state a (program xs) m i.val))) j c<2^W)
    (parentFit : ∀ (i : Fin (records xs).length), ((records xs).get i).parent.finalLayer=false →
      ∀ j,((records xs).get i).parent.first+(program xs).owners i j<2^W) :
    ∀ q∈xs, q.Written a.banks (natural (state a (program xs) m (records xs).length)) := by
  intro q mem
  obtain ⟨i,rfl⟩:=every_view xs q mem
  refine ⟨fun j c=>final_charge a _ m room ordered i j c (old i j) (fit i j c),?_⟩
  intro nonfinal j
  have w := final_parent_word a (program xs) m room ordered i j
  change ((records xs).get i).parent.finalLayer=false at nonfinal
  simp only [nonfinal,Bool.false_eq_true,ite_false] at w
  exact (congrArg Fin.val w).trans (Fin.val_cast_of_lt (parentFit i nonfinal j))

variable {F : Type} [Field F]

/-- The first offset in the selected tail is the end of its immediate predecessor. -/
private theorem layer_order {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    let rs:=records (r.archiveList h C O p seed)
    (∀ i : Fin rs.length,O.layer.first≤(rs.get i).actual.first) ∧ Chronological rs := by
  induction r with
  | done A =>
    constructor
    · intro i
      change Fin 1 at i
      have eq : i=(0:Fin 1) := Subsingleton.elim _ _
      subst i
      exact le_rfl
    · intro i j lt
      change Fin 1 at i j
      have eq : i=j := Subsingleton.elim _ _
      exact False.elim ((not_lt_of_ge eq.ge) lt)
  | step R next ih =>
    have tail := ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    have co:=p.1.row.contiguous
    constructor
    · intro i
      induction i using Fin.cases with
      | zero => exact le_rfl
      | succ i =>
        have hb:=tail.1 i
        exact (show O.layer.first≤p.1.sites.layer.first by omega).trans hb
    · intro i k less
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact False.elim (lt_irrefl _ less)
        | succ k =>
          change O.layer.first+O.layer.count≤_
          exact co ▸ tail.1 k
      | succ i =>
        induction k using Fin.cases with
        | zero => exact False.elim (Nat.not_lt_zero _ less)
        | succ k => exact tail.2 i k (Fin.succ_lt_succ_iff.mp less)

theorem archive_chronological {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    Chronological (records (r.archiveList h C O p seed)) := (layer_order r h C O p seed).2

theorem view_mem (xs : List NodeRow) (i : Fin (records xs).length) :
    view (program xs) i∈xs := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    induction i using Fin.cases with
    | zero => exact List.mem_cons_self ..
    | succ i => exact List.mem_cons_of_mem _ (ih i)

private theorem row_before {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (first : ∀ j k,seed.child j k<O.layer.first) :
    ∀ q ∈ r.archiveList h C O p seed, ∀ j k,q.data.child j k<q.layer.first := by
  induction r with
  | done A =>
    intro q mem
    obtain rfl := List.mem_singleton.mp mem
    exact first
  | step R next ih =>
    intro q mem
    rcases List.mem_cons.mp mem with rfl|rest
    · exact first
    · apply ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data _ q rest
      intro j k
      let v:=p.1.sites.ord.symm j
      have atRow:=p.1.row.childId v k
      have eq : p.1.sites.ord v=j := Equiv.apply_symm_apply _ _
      rw [eq] at atRow
      rw [atRow,p.1.row.contiguous]
      exact Nat.add_lt_add_left (O.ord ((p.1.row.children v k).val)).isLt O.layer.first

/-- The initial zero-child layer and the actual finite parent fibers imply all
strict bounds on daughter addresses. -/
theorem archive_old {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (noChildren : O.layer.childCount=0) :
    let xs:=r.archiveList h C O p seed
    ∀ i j k,((program xs).data i).child j k<((records xs).get i).actual.first := by
  intro xs i
  have head (j) (k : Fin O.layer.childCount) : seed.child j k<O.layer.first := by have h:=k.isLt;omega
  exact row_before r h C O p seed head _ (view_mem _ i)

private theorem first_row {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    ∃ q ∈ r.archiveList h C O p seed,q.layer=O.layer := by
  cases r with
  | done A => exact ⟨_,List.mem_cons_self ..,rfl⟩
  | step R next => exact ⟨_,List.mem_cons_self ..,rfl⟩

private theorem row_parents {W d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (bounded : ∀ q∈r.archiveList h C O p seed,q.layer.first+q.layer.count<2^W) :
    ∀ q ∈ r.archiveList h C O p seed, q.parent.finalLayer=false → ∀ j,q.parent.first+q.owners j<2^W := by
  induction r with
  | done A =>
    intro q mem
    obtain rfl := List.mem_singleton.mp mem
    simp
  | step R next ih =>
    let ys := (next h.1).archiveList (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    have tail : ∀ q∈ys,q.layer.first+q.layer.count<2^W := fun q hq=>bounded q (List.mem_cons_of_mem _ hq)
    intro q mem
    rcases List.mem_cons.mp mem with rfl|rest
    · intro _ j
      obtain ⟨q,hq,eq⟩:=first_row (next h.1) (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
      have end':=tail q hq
      rw [eq] at end'
      exact (Nat.add_lt_add_left (p.1.sites.ord (R.parent h.1 (O.ord.symm j))).isLt _).trans end'
    · exact ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data tail q rest

/-- The native endpoint range for each successor layer already bounds its physical
parent identifiers, including the high-offset final layer. -/
theorem archive_parent_fits {W d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (a : NodeArchive) {budget : ℕ} (room : RunBounds W a (records (r.archiveList h C O p seed)) budget) :
    let xs:=r.archiveList h C O p seed
    ∀ (i : Fin (records xs).length),((records xs).get i).parent.finalLayer=false →
        ∀ j,((records xs).get i).parent.first+(program xs).owners i j<2^W := by
  let xs:=r.archiveList h C O p seed
  have bounded (q : NodeRow) (mem : q∈xs) : q.layer.first+q.layer.count<2^W := by
    obtain ⟨i,rfl⟩:=every_view xs q mem
    have fit:=(room.layer i).nodeEnd
    change a.banks.nodes+8*(((records xs).get i).actual.first+((records xs).get i).actual.count)<2^W at fit
    change ((records xs).get i).actual.first+((records xs).get i).actual.count<_
    omega
  exact fun i=>row_parents r h C O p seed bounded _ (view_mem _ i)

/-- Every registered physical daughter points into the preceding emitted part of S43;
the final image therefore gives the literal cost equations and stored parent map. -/
theorem archive_rows_stored {W d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer)
    (a : NodeArchive) (m : Memory W) {budget : ℕ}
    (room : RunBounds W a (records (r.archiveList h C O p seed)) budget)
    (old : let xs:=r.archiveList h C O p seed
      ∀ i j k, ((program xs).data i).child j k<((records xs).get i).actual.first)
    (fit : let xs:=r.archiveList h C O p seed
      ∀ (i : Fin (records xs).length) j c,
        ((program xs).data i).cost a.banks (prior a (decrement a (state a (program xs) m i.val))) j c<2^W)
    (parentFit : let xs:=r.archiveList h C O p seed
      ∀ (i : Fin (records xs).length),((records xs).get i).parent.finalLayer=false →
        ∀ j, ((records xs).get i).parent.first+(program xs).owners i j<2^W) :
    let xs:=r.archiveList h C O p seed
    let mem:=natural (state a (program xs) m (records xs).length)
    (∀ v c, archiveColumn a.banks mem (O.id v) c=seed.cost a.banks (archiveColumn a.banks mem) (O.ord v) c) ∧
      r.ArchiveRowsStored a.banks mem h C O p :=
  r.archiveRows_of_list h C O p seed a.banks _
    (written_rows a _ m room (archive_chronological r h C O p seed) old fit parentFit)

end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
