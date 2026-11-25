import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields

namespace OAI
/-! # Following the native owner columns of the selected compression history

Each address is the owner-array pointer in field 44 of the actual stage.
The successor ordinal uses precisely the numbering of the next stage's input.
-/

noncomputable section
namespace Hierarchy.TraceReceiverArchive

open ThreeFlat Diagonal Diagonal.PhysicalStage RAM.NavigationNodeRows
open Computability.VPVNP.BurstRAM

variable {F : Type} [Field F]

/-- The address sequence in the exact execution order, excluding the final
layer, whose nodes are their own roots. -/
def ownerBases : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (h : r.plan.History) → (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → List ℕ
  | _, _, _, .done _, _, _, _, _ => []
  | _, _, _, .step R next, h, C, _, p =>
    p.1.ownerPtr :: ownerBases (next h.1) (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2

/-- Read only one word of each stage's owner column. -/
def follow (mem : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], j => j
  | b :: bs, j => follow mem bs (mem (b+j))

theorem follow_eq_foldl (mem : ℕ → ℕ) (bases : List ℕ) (j : ℕ) :
    follow mem bases j = bases.foldl (fun k b => mem (b+k)) j := by
  induction bases generalizing j with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- The concrete array of one move contains the typed parent, in the physical
ordinals of its source and target. These ordinal equivalences come from the
archive, including when source or target has a noncanonical site order. -/
def Issued {d l D L : ℕ} {A : State d l} (R : Move F A D L) (b : Fin R.rules.count)
    (O : A.ArchiveSites) {charge : (R.next b).Site → ℕ} (s : R.ArchiveStep b O charge)
    (mem : ℕ → ℕ) := ∀ x : A.Site, mem (s.ownerPtr+(O.ord x).val) = (s.sites.ord (R.parent b x)).val

theorem first_issued {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ b, Run F (R.next b)) (h : (Run.step R next).plan.History)
    (C : (Run.step R next).Charges) (O : A.ArchiveSites) (p : (Run.step R next).ArchivePath h C O)
    (data : LayerData O.layer) (mem : ℕ → ℕ)
    (source : ∀ q ∈ (Run.step R next).archiveList h C O p data, ParentReads q.parent q.owners mem) :
    Issued R h.1 O p.1 mem := by
  intro x
  have header := source _ (List.mem_cons_self ..) rfl (O.ord x)
  simpa only [Equiv.symm_apply_apply] using header

/-- Folding the physically read ordinals reaches the actual plan destination
for each initial site. No traversal of a semantic owner function occurs in
`follow` and the folded memory is the RAM image after the selected history. -/
theorem follow_actual {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (mem : ℕ → ℕ) (source : ∀ q ∈ r.archiveList h C O p data, ParentReads q.parent q.owners mem)
    (a : A.Site) :
    follow mem (ownerBases r h C O p) (O.ord a).val =
      ((r.finalArchive h C O p).2 (r.rawDestination h a)).val := by
  induction r with
  | done A => rfl
  | step R next ih =>
    change follow mem (ownerBases (next h.1) (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2)
      (mem (p.1.ownerPtr+(O.ord a).val)) = _
    rw [first_issued R next h C O p data mem source a]
    exact ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
      (fun q hit => source q (.tail _ hit)) (R.parent h.1 a)

/-- Every prefix of the numeric walk reads within its actual retained owner
array. Choosing `safe = (· < dp)` gives the scanner's disjoint scratch bound. -/
theorem prefix_extent {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (mem : ℕ → ℕ) (safe : ℕ → Prop)
    (source : ∀ q ∈ r.archiveList h C O p data, ParentReads q.parent q.owners mem)
    (bounds : ∀ q ∈ r.archiveList h C O p data, q.parent.finalLayer=false →
      ∀ j : Fin q.layer.count, safe (q.parent.owners+j.val))
    (a : A.Site) (t : ℕ) (ok : t < (ownerBases r h C O p).length) :
    let bases := ownerBases r h C O p
    safe (bases[t]+(bases.take t).foldl (fun j b=>mem (b+j)) (O.ord a).val) := by
  induction r generalizing t with
  | done A => cases Nat.not_lt_zero _ ok
  | step R next ih =>
    cases t with
    | zero => exact bounds _ (.head _) rfl (O.ord a)
    | succ t =>
      let tail := Run.tailHistory R next h
      have valid : t < (ownerBases (next h.1) tail (C.2 h.1) p.1.sites p.2).length :=
        Nat.lt_of_succ_lt_succ ok
      change safe ((ownerBases (next h.1) tail (C.2 h.1) p.1.sites p.2)[t]+
        ((ownerBases (next h.1) tail (C.2 h.1) p.1.sites p.2).take t).foldl (fun j b=>mem (b+j)) (mem (p.1.ownerPtr+(O.ord a).val)))
      rw [first_issued R next h C O p data mem source a]
      exact ih h.1 tail (C.2 h.1) p.1.sites p.2 p.1.data
        (fun q hit => source q (.tail _ hit)) (fun q hit => bounds q (.tail _ hit))
        (R.parent h.1 a) t valid

/-- Relating the numerically read root to the tensor plan itself. -/
theorem follow_destination {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (mem : ℕ → ℕ) (source : ∀ q ∈ r.archiveList h C O p data, ParentReads q.parent q.owners mem)
    (a : A.Site) :
    follow mem (ownerBases r h C O p) (O.ord a).val =
      ((r.finalArchive h C O p).2 ((r.finalSite h).symm (r.plan.destination h a))).val := by
  rw [follow_actual r h C O p data mem source, ←r.finalSite_rawDestination, Equiv.symm_apply_apply]

/-- The actual numeric destination read out of the owner arrays is the same
ordinal used to schedule a terminal factor and select its recorded metadata. -/
theorem follow_terminalOrder {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (mem : ℕ → ℕ) (source : ∀ q ∈ r.archiveList h C O p data, ParentReads q.parent q.owners mem)
    (numbered : r.FinalNumbered h C O p) (a : A.Site) :
    follow mem (ownerBases r h C O p) (O.ord a).val =
      (r.terminalOrderEquiv h (r.plan.destination h a)).val := by
  rw [follow_destination r h C O p data mem source a,r.terminalOrderEquiv_val]
  exact numbered _

open NavigationPass NavigationDirectory

private def readBases (xs : List Layers) : List ℕ :=
  xs.filterMap (fun q => if q.parent.finalLayer then none else some q.parent.owners)

private theorem actual_bases {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer) :
    readBases ((r.archiveList h C O p data).map (fun q => (⟨q.layer,q.parent⟩ : Layers))) =
      ownerBases r h C O p := by
  induction r with
  | done => rfl
  | step R next ih =>
    exact congrArg (p.1.ownerPtr :: ·) (ih h.1 (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data)

private theorem directory_bases_length (K : ℕ) (ops : List Stage) (c : Cursor) (old : Layer) :
    (readBases (nodeLayers K ops c old)).length = ops.length := by
  induction ops generalizing c old with
  | nil => rfl
  | cons hd tail ih => exact congrArg Nat.succ (ih (allocate K c hd).next (nodeLayer K c hd))

theorem ownerBases_length {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (K : ℕ) (ops : List Stage) (c : Cursor)
    (rows : (r.archiveList h C O p data).map (fun q => (⟨q.layer,q.parent⟩ : Layers)) =
      nodeLayers K ops c O.layer) :
    (ownerBases r h C O p).length = ops.length := by
  rw [←actual_bases r h C O p data, rows, directory_bases_length]

private theorem field44 {K : ℕ} (pre : List Stage) (op : Stage) (post : List Stage)
    (c : Cursor) (old : Layer) :
    (readBases (nodeLayers K (pre++op::post) c old))[pre.length]? =
      some ((allocate K (finish K pre c) op).words 44) := by
  induction pre generalizing c old with
  | nil => rfl
  | cons hd rest ih => exact ih (allocate K c hd).next (nodeLayer K c hd)

/-- Field 44 in each mounted 64-word stage header is the actual next owner
array. The row equality is exactly the first projection of `stagePost`. -/
theorem owner_base {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (K : ℕ) (pre : List Stage) (op : Stage) (post : List Stage) (c : Cursor)
    (rows : (r.archiveList h C O p data).map (fun q => (⟨q.layer,q.parent⟩ : Layers)) =
      nodeLayers K (pre++op::post) c O.layer) :
    (ownerBases r h C O p)[pre.length]? = some ((allocate K (finish K pre c) op).words 44) := by
  rw [←actual_bases r h C O p data,rows,field44]

theorem mounted_owner_base {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (data : LayerData O.layer)
    (K : ℕ) (pre : List Stage) (op : Stage) (post : List Stage) (c : Cursor) (dir : ℕ)
    (mem : ℕ → ℕ)
    (rows : (r.archiveList h C O p data).map (fun q => (⟨q.layer,q.parent⟩ : Layers)) =
      nodeLayers K (pre++op::post) c O.layer)
    (mounted : ∀ i v, (tape K (pre++op::post) c)[i]?=some v → mem (dir+i)=v) :
    (ownerBases r h C O p)[pre.length]? = some (mem (dir+(64*pre.length+44))) := by
  have field := tape_header K pre op post c (⟨44,by decide⟩ : Fin 64)
  rw [←actual_bases r h C O p data, rows, field44, mounted _ _ field]


end Hierarchy.TraceReceiverArchive

end
end OAI
