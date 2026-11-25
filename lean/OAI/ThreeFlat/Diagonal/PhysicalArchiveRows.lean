import OAI.ThreeFlat.Diagonal.PhysicalArchiveRowFields
import OAI.ThreeFlat.Diagonal.PhysicalChargeArray
import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # Typed owner ordinals and accumulated charges in the physical archive -/

namespace ThreeFlat.Diagonal.PhysicalStage.Run

open HistoryContraction
noncomputable section
variable {F : Type} [Field F]

/-- The terminal physical row reached by composing every actual parent assignment. -/
def rawDestination : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    A.Site → r.readTerminal (fun X => X.Site) h
  | _, _, _, .done _, _, a => a
  | _, _, _, .step R next, h, a =>
      (next h.1).rawDestination (tailHistory R next h) (R.parent h.1 a)

private theorem destination_cast_heq {X Y : Shape} (e : X=Y) (P : Plan F X)
    (h : (e ▸ P : Plan F Y).History) (v : Y.Site) :
    HEq (P.destination (historyOfCast e P h) ((congrArg Shape.Site e.symm) ▸ v))
      ((e ▸ P : Plan F Y).destination h v) := by
  cases e
  rfl

private theorem rawDestination_heq {d l : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (a : A.Site) : HEq (r.rawDestination h a) (r.plan.destination h a) := by
  induction r with
  | done A => rfl
  | step R next ih =>
      exact (ih h.1 (tailHistory R next h) (R.parent h.1 a)).trans
        (destination_cast_heq (R.target_eq h.1).symm (next h.1).plan h.2 (R.rules.owner h.1 a))

/-- The physical terminal row and the owner used in the tensor contraction pick
the same terminal site after transporting the physical site's type. -/
theorem finalSite_rawDestination {d l : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (a : A.Site) :
    r.finalSite h (r.rawDestination h a) = r.plan.destination h a := by
  let e := (terminal_relation (fun X => X.Site) (fun X => X.shape)
    (fun s t => s=t.Site) (fun _ => rfl) r h).trans (congrArg Shape.Site (r.terminal_shape h))
  exact eq_of_heq ((cast_heq e (r.rawDestination h a)).trans (r.rawDestination_heq h a))

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical BigOperators
open HistoryContraction
noncomputable section
variable {F : Type} [Field F]

def fiberMass {I J : Type} [Fintype I] (f : I → J) (a : I → ℕ) (j : J) : ℕ :=
  ∑ i : {x // f x=j}, a i.val

theorem fiberMass_id {I : Type} [Fintype I] (a : I → ℕ) (j : I) : fiberMass id a j = a j := by
  let e : {x // id x=j} ≃ Unit :=
    ⟨fun _ => (), fun _ => ⟨j,rfl⟩, fun i => Subtype.ext i.property.symm, fun _ => rfl⟩
  calc
    _ = ∑ _u : Unit, a j := (e.symm.sum_comp (fun i => a i.val)).symm
    _ = a j := by simp

theorem fiberMass_comp {I J Z : Type} [Fintype I] [Fintype J]
    (f : I → J) (g : J → Z) (a : I → ℕ) (z : Z) :
    fiberMass (g ∘ f) a z = fiberMass g (fiberMass f a) z := by
  let S := {x // g (f x)=z}
  let T := (y : {y // g y=z}) × {x // f x=y.val}
  let e : S ≃ T :=
    { toFun := fun x => ⟨⟨f x.val,x.property⟩, ⟨x.val,rfl⟩⟩
      invFun := fun y => ⟨y.2.val,(congrArg g y.2.property).trans y.1.property⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨j,hj⟩,⟨i,hi⟩⟩
        change f i=j at hi
        subst j
        rfl }
  let b (y : T) := a y.2.val
  calc
    _ = ∑ y : T, b y := e.sum_comp b
    _ = _ := Fintype.sum_sigma b


end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- Actual allocation and native row order of a physical site array. -/
structure State.ArchiveSites {d l : ℕ} (A : State d l) where
  layer : Layer
  ord : A.Site ≃ Fin layer.count

def State.ArchiveSites.id {d l : ℕ} {A : State d l} (O : A.ArchiveSites) (a : A.Site) :=
  O.layer.first+(O.ord a).val

def State.SeedRows {d l : ℕ} {A : State d l} (O : A.ArchiveSites) (data : LayerData O.layer)
    (b : Banks) (start pairs : A.Site→ℕ) : Prop :=
  ∀ (prior : ℕ→Fin 2→ℕ) (v : A.Site) (col : Fin 2), data.cost b prior (O.ord v) col =
    if col.val=0 then b.unitWork*start v else pairs v

/-- The absolute IDs published in the child array enumerate exactly the actual fiber.
The charge columns count the selected histogram copies and all incident words. -/
structure Move.ArchiveRow {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (old : A.ArchiveSites) (new : (R.next t).ArchiveSites) (data : LayerData new.layer)
    (charge : (R.next t).Site → ℕ) where
  contiguous : new.layer.first=old.layer.first+old.layer.count
  nonleaf : new.layer.kind≠0
  children : ∀ v, Fin new.layer.childCount ≃ {x // R.parent t x=v}
  childId : ∀ v j, data.child (new.ord v) j=old.id ((children v j).val)
  fresh : ∀ v, 1+(data.halfWidth (new.ord v)).sum+(data.motifCopies (new.ord v)).sum=charge v

structure Move.ArchiveStep {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (old : A.ArchiveSites) (charge : (R.next t).Site→ℕ) where
  sites : (R.next t).ArchiveSites
  data : LayerData sites.layer
  row : R.ArchiveRow t old sites data charge
  ownerPtr : ℕ := 0

namespace Run

def ArchivePath : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    r.Charges → A.ArchiveSites → Type
  | _, _, _, .done _, _, _, _ => Unit
  | _, _, _, .step R next, h, C, old =>
    (row : R.ArchiveStep h.1 old (C.1 h.1)) ×
      (next h.1).ArchivePath (tailHistory R next h) (C.2 h.1) row.sites

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

def archiveColumn (b : Banks) (mem : ℕ→ℕ) (i : ℕ) (col : Fin 2) := mem (b.charges+2*i+col.val)

def State.ArchiveSites.Charged {d l : ℕ} {A : State d l} (O : A.ArchiveSites)
    (b : Banks) (mem : ℕ→ℕ) (start pay : A.Site→ℕ) : Prop :=
  ∀ a, archiveColumn b mem (O.id a) 0=b.unitWork*start a ∧ archiveColumn b mem (O.id a) 1=pay a

theorem State.SeedRows.charged {d l : ℕ} {A : State d l} {O : A.ArchiveSites} {data : LayerData O.layer}
    {b : Banks} {start pay : A.Site→ℕ} (H : State.SeedRows O data b start pay) (mem : ℕ→ℕ)
    (written : ∀ v c, archiveColumn b mem (O.id v) c=data.cost b (archiveColumn b mem) (O.ord v) c) :
    O.Charged b mem start pay := by
  intro v
  constructor
  · exact (written v 0).trans (H _ v 0)
  · exact (written v 1).trans (H _ v 1)

theorem Move.ArchiveStep.cost_values {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {t : Fin R.rules.count} {old : A.ArchiveSites} {charge : (R.next t).Site→ℕ}
    (s : R.ArchiveStep t old charge) (b : Banks) (prior : ℕ→Fin 2→ℕ) (start pay : A.Site→ℕ)
    (previous : ∀ a, prior (old.id a) 0=b.unitWork*start a ∧ prior (old.id a) 1=pay a)
    (v : (R.next t).Site) :
    s.data.cost b prior (s.sites.ord v) 0=b.unitWork*R.push t charge start v ∧
    s.data.cost b prior (s.sites.ord v) 1=∑ a : {x // R.parent t x=v}, pay a.val := by
  have work : (∑ j, prior (s.data.child (s.sites.ord v) j) 0) =
      b.unitWork*(∑ a : {a // R.parent t a=v}, start a.val) := by
    calc
      _ = ∑ j, b.unitWork * start (s.row.children v j).val :=
        Finset.sum_congr rfl fun j _ => (congrArg (fun z => prior z 0) (s.row.childId v j)).trans (previous _).1
      _ = _ := by rw [←Finset.mul_sum]; exact congrArg (b.unitWork * ·) ((s.row.children v).sum_comp (fun a=>start a.val))
  have pairs : (∑ j, prior (s.data.child (s.sites.ord v) j) 1)=fiberMass (R.parent t) pay v := by
    calc
      _ = ∑ j, pay (s.row.children v j).val :=
        Finset.sum_congr rfl fun j _ => (congrArg (fun z => prior z 1) (s.row.childId v j)).trans (previous _).2
      _ = _ := (s.row.children v).sum_comp (fun a=>pay a.val)
  constructor
  · simp [LayerData.cost,s.row.nonleaf,s.row.fresh v,work,Move.push,Nat.mul_add]
  · simpa [LayerData.cost,s.row.nonleaf,fiberMass] using pairs

theorem Move.ArchiveStep.charged {d l D L : ℕ} {A : State d l} {R : Move F A D L}
    {t : Fin R.rules.count} {old : A.ArchiveSites} {charge : (R.next t).Site→ℕ}
    (s : R.ArchiveStep t old charge) (b : Banks) (mem : ℕ→ℕ) (start pay : A.Site→ℕ)
    (previous : old.Charged b mem start pay)
    (written : ∀ v c, archiveColumn b mem (s.sites.id v) c =
      s.data.cost b (archiveColumn b mem) (s.sites.ord v) c) :
    s.sites.Charged b mem (R.push t charge start) (fiberMass (R.parent t) pay) := by
  intro v
  have z := s.cost_values b (archiveColumn b mem) start pay previous v
  exact ⟨(written v 0).trans z.1,(written v 1).trans z.2⟩

namespace Run

def finalArchive : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O →
    (s : Layer) × (r.readTerminal (fun X => X.Site) h ≃ Fin s.count)
  | _, _, _, .done _, _, _, O, _ => ⟨O.layer,O.ord⟩
  | _, _, _, .step R next, h, C, _, p =>
    (next h.1).finalArchive (tailHistory R next h) (C.2 h.1) p.1.sites p.2

/-- The two S43 cells are precisely the prior-bank costs from the native scan.
The S44 field at offset one points at the immediately following physical owner. -/
def ArchiveRowsStored (b : Banks) (mem : ℕ→ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (h : r.plan.History) → (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → Prop
  | _, _, _, .done _, _, _, _, _ => True
  | _, _, _, .step R next, h, C, O, p =>
    (∀ v c, archiveColumn b mem (p.1.sites.id v) c =
      p.1.data.cost b (archiveColumn b mem) (p.1.sites.ord v) c) ∧
    (∀ a, mem (b.nodes+8*O.id a+1)=p.1.sites.id (R.parent h.1 a)) ∧
    (next h.1).ArchiveRowsStored b mem (tailHistory R next h) (C.2 h.1) p.1.sites p.2

private theorem archiveRawCharges {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (start pay : A.Site→ℕ) (seed : O.Charged b mem start pay)
    (v : r.readTerminal (fun X=>X.Site) h) :
    let last := r.finalArchive h C O p
    let i := last.1.first+(last.2 v).val
    archiveColumn b mem i 0 = b.unitWork*r.rootArray h C start v ∧
      archiveColumn b mem i 1 = fiberMass (r.rawDestination h) pay v := by
  induction r generalizing b mem with
  | done A =>
    exact ⟨(seed v).1,(seed v).2.trans (fiberMass_id pay v).symm⟩
  | step R next ih =>
    let t := h.1
    let rest := tailHistory R next h
    have z := ih t rest (C.2 t) p.1.sites p.2 b mem stored.2.2
      (R.push t (C.1 t) start) (fiberMass (R.parent t) pay)
      (p.1.charged b mem start pay seed stored.1) v
    exact ⟨z.1,z.2.trans (fiberMass_comp (R.parent t) ((next t).rawDestination rest) pay v).symm⟩

theorem archive_charges {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (start pay : A.Site→ℕ) (seed : O.Charged b mem start pay)
    (v : (r.plan.finish h).Site) :
    let last := r.finalArchive h C O p
    let i := last.1.first+(last.2 ((r.finalSite h).symm v)).val
    archiveColumn b mem i 0 = b.unitWork*r.chargeAt h C start v ∧
      archiveColumn b mem i 1 = ∑ a : {x // r.plan.destination h x=v}, pay a.val := by
  let e := r.finalSite h
  let iso : {a // r.plan.destination h a=v} ≃ {a // r.rawDestination h a=e.symm v} :=
    Equiv.subtypeEquivRight fun a => by
      rw [←r.finalSite_rawDestination h a]
      change e _=v ↔ _
      constructor
      · intro H
        simpa only [Equiv.symm_apply_apply] using congrArg e.symm H
      · intro H
        rw [H,Equiv.apply_symm_apply]
  have mass : (∑ a : {x // r.plan.destination h x=v},pay a.val) =
    fiberMass (r.rawDestination h) pay (e.symm v) := iso.sum_comp (fun a=>pay a.val)
  have z := r.archiveRawCharges h C O p b mem stored start pay seed (e.symm v)
  exact ⟨z.1,z.2.trans mass.symm⟩

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
noncomputable section
variable {F : Type} [Field F]

def NodeRow.Written (q : NodeRow) (b : Banks) (mem : ℕ→ℕ) : Prop :=
  (∀ j c, archiveColumn b mem (q.layer.first+j.val) c =
    q.data.cost b (archiveColumn b mem) j c) ∧
  (q.parent.finalLayer=false → ∀ j, mem (b.nodes+8*(q.layer.first+j.val)+1)=q.parent.first+q.owners j)

namespace Run

/-- The owner-pointer of each old layer comes from the following stage's
allocation. Its values are the numerals of that stage's typed parent map. -/
def archiveList : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    (C : r.Charges) → (O : A.ArchiveSites) → r.ArchivePath h C O → LayerData O.layer → List NodeRow
  | _, _, _, .done _, _, _, O, _, data => [⟨O.layer,⟨true,0,0⟩,data,fun _=>0⟩]
  | _, _, _, .step R next, h, C, O, p, data =>
    ⟨O.layer,⟨false,p.1.sites.layer.first,p.1.ownerPtr⟩,data,
      fun j=>(p.1.sites.ord (R.parent h.1 (O.ord.symm j))).val⟩ ::
      (next h.1).archiveList (tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data

theorem archiveRows_of_list {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (initial : LayerData O.layer) (b : Banks) (mem : ℕ→ℕ)
    (archived : ∀ q ∈ r.archiveList h C O p initial, q.Written b mem) :
    (∀ v c,archiveColumn b mem (O.id v) c=initial.cost b (archiveColumn b mem) (O.ord v) c) ∧
    r.ArchiveRowsStored b mem h C O p := by
  induction r with
  | done A =>
    change (∀ q ∈ [_],_) at archived
    exact ⟨fun v c=>(archived _ (List.mem_cons_self ..)).1 (O.ord v) c,trivial⟩
  | step R next ih =>
    let tail := (next h.1).archiveList (tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
    change (∀ q ∈ _ :: tail,_) at archived
    have head := archived _ (List.mem_cons_self ..)
    have rest := ih h.1 (tailHistory R next h) (C.2 h.1) p.1.sites p.2 p.1.data
      (fun q hq=>archived q (List.mem_cons_of_mem _ hq))
    refine ⟨fun v c=>head.1 (O.ord v) c,rest.1,?_,rest.2⟩
    intro v
    simpa only [Equiv.symm_apply_apply,State.ArchiveSites.id] using head.2 rfl (O.ord v)

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
