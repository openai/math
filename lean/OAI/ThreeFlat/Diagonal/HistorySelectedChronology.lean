import OAI.ThreeFlat.Diagonal.PhysicalArchiveJoin
import OAI.ThreeFlat.Diagonal.PhysicalWordForest
import OAI.ThreeFlat.Diagonal.PhysicalArchiveBounds

namespace OAI
/-! # The selected S44 node, its actual assembled history tree and its original external bits -/
namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins E : Type} [Field F]

/-- Dependent fields of one chronological node. Every external position retains its
original source even if the selected site was created several physical passes later. -/
structure SelectedNode (F Pins E : Type) [Field F] where
  degree : ℕ
  lanes : ℕ
  state : State degree lanes
  words : state.Words Pins
  site : state.Site
  tree : Tree F (words.ports.form.width site)
  origin : Fin (words.ext site)→E

namespace SelectedNode
variable (z : SelectedNode F Pins E)
def arity := z.words.ports.form.width z.site
def external := z.words.ext z.site
def net : BitNetwork F z.arity := z.tree.compile
end SelectedNode

variable {d l : ℕ} {A : State d l}

def nodeOfSite (L : A.Words Pins) (N : Forest F L.ports.form) (origin : ∀u,Fin (L.ext u)→E)
    (u : A.Site) : SelectedNode F Pins E := ⟨d,l,A,L,u,N u,origin u⟩

private def atCurrent (L : A.Words Pins) (N : Forest F L.ports.form) (origin : ∀u,Fin (L.ext u)→E)
    (O : A.ArchiveSites) (i : ℕ) (lower : O.layer.first≤ i) (upper : i<O.layer.first+O.layer.count) :
    SelectedNode F Pins E :=
  nodeOfSite L N origin (O.ord.symm ⟨i-O.layer.first,by omega⟩)

private theorem atCurrent_eq (L : A.Words Pins) (N : Forest F L.ports.form) (origin : ∀u,Fin (L.ext u)→E)
    (O : A.ArchiveSites) (u : A.Site) (lo hi) :
    atCurrent L N origin O (O.id u) lo hi=nodeOfSite L N origin u := by
  unfold atCurrent
  congr 1
  apply O.ord.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext;change O.layer.first+(O.ord u).val-O.layer.first=(O.ord u).val;omega

/-- Forward an inherited external location through the exact immediate child
map used when the stage builds its words. -/
def pushedOrigin {D m : ℕ} {R : Move F A D m} {i : Fin R.rules.count} {L : A.Words Pins}
    (step : R.WordStep Pins L i) (origin : ∀u,Fin (L.ext u)→E) :
    ∀v,Fin (step.words.ext v)→E :=
  fun v j=>origin (step.origin v j).1.val (step.origin v j).2

/-- The upper boundary is the end of the last genuine physical stage. The
chronological interval of the current stage precedes the recursive suffix. -/
def selectedAt : {d l : ℕ}→{A : State d l}→(r : Run F A)→(h : r.plan.History)→
    (J : Run.WordSteps Pins r)→(L : A.Words Pins)→Forest F L.ports.form→
    (C : r.Charges)→(O : A.ArchiveSites)→(path : r.ArchivePath h C O)→(∀u, Fin (L.ext u)→E)→
    (i : ℕ)→O.layer.first≤ i→i<(r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count→
    SelectedNode F Pins E
  | _,_,_,.done _,_,_,L,N,_,O,_,orig,i,lo,hi=>atCurrent L N orig O i lo hi
  | _,_,_,.step R next,h,J,L,N,C,O,path,orig,i,lo,hi=>
    if early : i<O.layer.first+O.layer.count then atCurrent L N orig O i lo early
    else
      let step:=J.1 L h.1
      (next h.1).selectedAt (tailHistory R next h) (J.2 h.1) step.words (step.nextForest N)
        (C.2 h.1) path.1.sites path.2 (pushedOrigin step orig) i (by rw [path.1.row.contiguous];omega) hi

theorem selectedSeed (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (orig : ∀u,Fin (L.ext u)→E) (u : A.Site) (lo hi) :
    r.selectedAt h J L N C O path orig (O.id u) lo hi=nodeOfSite L N orig u := by
  have early : O.id u<O.layer.first+O.layer.count := Nat.add_lt_add_left (O.ord u).isLt _
  cases r with
  | done A=>exact atCurrent_eq L N orig O u _ _
  | step R next=>rw [selectedAt,dite_eq_left early];exact atCurrent_eq L N orig O u _ _

/-- Reading a later entry discards this layer's rows and carries the actual
new word layout, the stage-assembled forest and the inherited source map. -/
theorem selectedLater {D m : ℕ} (R : Move F A D m) (next : ∀j,Run F (R.next j))
    (h : (Run.step R next).plan.History) (J : Run.WordSteps Pins (Run.step R next))
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : (Run.step R next).Charges) (O : A.ArchiveSites)
    (path : (Run.step R next).ArchivePath h C O) (orig : ∀u,Fin (L.ext u)→E)
    (i : ℕ) (lo hi) (later : path.1.sites.layer.first≤ i) :
    (Run.step R next).selectedAt h J L N C O path orig i lo hi =
      (next h.1).selectedAt (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words ((J.1 L h.1).nextForest N)
        (C.2 h.1) path.1.sites path.2 (pushedOrigin (J.1 L h.1) orig) i later hi := by
  have beyond : ¬i<O.layer.first+O.layer.count := by rw [←path.1.row.contiguous];omega
  rw [selectedAt,dite_eq_right beyond]

/-- The final base/lane site is charted into the last absolute S44 interval. -/
def endSites : {d l : ℕ}→{A : State d l}→(r : Run F A)→(h : r.plan.History)→
    (C : r.Charges)→(O : A.ArchiveSites)→ r.ArchivePath h C O→(r.terminalLayer h).state.ArchiveSites
  | _,_,_,.done _,_,_,O,_=>O
  | _,_,_,.step R next,h,C,_,path=>
    (next h.1).endSites (tailHistory R next h) (C.2 h.1) path.1.sites path.2

theorem endSites_layer (r : Run F A) (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) : (r.endSites h C O path).layer=(r.finalArchive h C O path).1 := by
  induction r with
  | done A=>rfl
  | step R next ih=>exact ih h.1 (tailHistory R next h) (C.2 h.1) path.1.sites path.2

/-- The node has the precise history-tree and the original source for every
external bit. Each equality is on the whole dependent record. -/
theorem selectedLast (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (orig : ∀u,Fin (L.ext u)→E) (v : (r.terminalLayer h).state.Site) (lo hi) :
    r.selectedAt h J L N C O path orig ((r.endSites h C O path).id v) lo hi =
      nodeOfSite (r.endWords h J L) (r.endForest h J L N)
        (fun u j=>orig (r.extAncestor h J L u j).1 (r.extAncestor h J L u j).2) v := by
  induction r with
  | done A=>exact selectedSeed (.done A) h J L N C O path orig v lo hi
  | step R next ih=>
    let t:=h.1
    let tail:=next t
    let rest:=tailHistory R next h
    have bound:=tail.archive_bounds rest (C.2 t) path.1.sites path.2
    have layer:=tail.endSites_layer rest (C.2 t) path.1.sites path.2
    have later : path.1.sites.layer.first≤((Run.step R next).endSites h C O path).id v := by
      change _≤(tail.endSites rest (C.2 t) path.1.sites path.2).layer.first+_
      rw [layer]
      exact bound.1.trans (Nat.le_add_right ..)
    rw [selectedLater R next h J L N C O path orig _ lo hi later]
    exact ih t rest (J.2 t) (J.1 L t).words ((J.1 L t).nextForest N)
      (C.2 t) path.1.sites path.2 (pushedOrigin (J.1 L t) orig) v _ _

/-- All global S44 indices, from zero through the last terminal record. -/
def archiveNode (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (zero : O.layer.first=0)
    (i : Fin ((r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count)) :
    SelectedNode F Pins (Σ u:A.Site,Fin (L.ext u)) :=
  r.selectedAt h J L N C O path (fun u j=>⟨u,j⟩) i.val (by rw [zero];exact Nat.zero_le _) i.isLt

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins E : Type} [Field F] {d l : ℕ} {A : State d l}
variable (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (zero : O.layer.first=0)

theorem archiveNode_at (i : Fin ((r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count))
    (v : (r.terminalLayer h).state.Site) (atV : i.val=(r.endSites h C O path).id v) :
    r.archiveNode h J L N C O path zero i =
      nodeOfSite (r.endWords h J L) (r.endForest h J L N) (fun v j=>r.extAncestor h J L v j) v := by
  obtain ⟨i,hi⟩:=i
  change i=_ at atV
  subst i
  exact r.selectedLast h J L N C O path (fun u j=>(⟨u,j⟩ : Σ u : A.Site, Fin (L.ext u)))
    v (by rw [zero]; exact Nat.zero_le _) hi

def archiveLastIndex (v : (r.terminalLayer h).state.Site) :
    Fin ((r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count) :=
  ⟨(r.endSites h C O path).id v,by
    rw [←r.endSites_layer h C O path]
    exact Nat.add_lt_add_left ((r.endSites h C O path).ord v).isLt _⟩

theorem archiveLastNode (v : (r.terminalLayer h).state.Site) :
    r.archiveNode h J L N C O path zero (r.archiveLastIndex h C O path v) =
      nodeOfSite (r.endWords h J L) (r.endForest h J L N) (fun z j=>r.extAncestor h J L z j) v :=
  r.archiveNode_at h J L N C O path zero _ v rfl

/-- Both the abstract history result and its native terminal layer arise from
the very same branch, so their site types admit the canonical equality cast. -/
theorem selectedSiteEq : r.readTerminal (fun X=>X.Site) h=(r.terminalLayer h).state.Site := by
  induction r with
  | done A=>rfl
  | step R next ih=>exact ih h.1 (tailHistory R next h)

theorem archiveLastOrdinal (v : r.readTerminal (fun X=>X.Site) h) :
    (r.archiveLastIndex h C O path (cast (r.selectedSiteEq h) v)).val=
      (r.finalArchive h C O path).1.first+((r.finalArchive h C O path).2 v).val := by
  induction r with
  | done A=>rfl
  | step R next ih=>exact ih h.1 (tailHistory R next h) (C.2 h.1) path.1.sites path.2 v

private theorem physical_width {X Y : Shape} (e : X=Y) (U : Form X Pins) (V : Form Y Pins)
    (linked : HEq U V) (x : X.Site) : U.width x=V.width (cast (congrArg Shape.Site e) x) := by
  cases e;cases eq_of_heq linked;rfl

omit [Field F] in
private theorem compile_heq {i j : ℕ} (sz : i=j) {x : Tree F i} {y : Tree F j}
    (h : HEq x y) : HEq x.compile y.compile := by cases sz;cases eq_of_heq h;rfl

/-- This is the actual network compiled from the Plan.assemble tree at the
selected terminal site. The only transport is the proven arity equality. -/
theorem archiveLastNetwork (v : (r.terminalLayer h).state.Site) :
    let z:=r.archiveNode h J L N C O path zero (r.archiveLastIndex h C O path v)
    let result:=r.plan.assemble h (r.wordAssembly J L) N
    let x:=cast (congrArg Shape.Site (r.terminalLayer_shape h)) v
    z.arity=result.1.width x ∧ HEq z.net ((result.2 x).compile) := by
  dsimp only
  rw [r.archiveLastNode h J L N C O path zero]
  have size:=physical_width (r.terminalLayer_shape h) (r.endWords h J L).ports.form
    (r.plan.assemble h (r.wordAssembly J L) N).1 (r.endWords_form h J L N).symm v
  exact ⟨size,compile_heq size (r.endForest_site h J L N v).symm⟩

section Stage
variable {D m : ℕ} (R : Move F A D m) (next : ∀t, Run F (R.next t))
    (hist : (Run.step R next).plan.History) (steps : Run.WordSteps Pins (Run.step R next))
    (charges : (Run.step R next).Charges) (p : (Run.step R next).ArchivePath hist charges O)
    (orig : ∀u,Fin (L.ext u)→E)

/-- The physical successor's own absolute index returns the newly assembled
tree using the exact local external-bit source from this move. -/
theorem selectedImmediate (v : (R.next hist.1).Site) (lo hi) :
    (Run.step R next).selectedAt hist steps L N charges O p orig (p.1.sites.id v) lo hi=
      nodeOfSite (steps.1 L hist.1).words ((steps.1 L hist.1).nextForest N)
        (pushedOrigin (steps.1 L hist.1) orig) v := by
  have later : p.1.sites.layer.first ≤ p.1.sites.id v := Nat.le_add_right ..
  rw [selectedLater R next hist steps L N charges O p orig _ lo hi later]
  exact selectedSeed (next hist.1) (tailHistory R next hist) (steps.2 hist.1) _ _ (charges.2 hist.1)
    p.1.sites p.2 _ v _ _

/-- The address stored at a real child index of the selected successor is an
earlier node whose tree and external source are exactly those of its owner fiber. -/
theorem selectedChild (v : (R.next hist.1).Site) (j : Fin p.1.sites.layer.childCount) (lo hi) :
    (Run.step R next).selectedAt hist steps L N charges O p orig (p.1.data.child (p.1.sites.ord v) j) lo hi =
      nodeOfSite L N orig ((p.1.row.children v j).val) := by
  have atChild:=p.1.row.childId v j
  generalize atId : (p.1.data.child (p.1.sites.ord v) j)=k at lo hi ⊢
  have id : k=O.id ((p.1.row.children v j).val) := atId.symm.trans atChild
  clear atId
  subst k
  exact selectedSeed (.step R next) hist steps L N charges O p orig _ _ _

end Stage
end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins E : Type} [Field F] {d l : ℕ} {A : State d l}
variable (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (zero : O.layer.first=0)

/-- The word array and the Plan finish sites use the same proven shape equality as terminalWire. -/
def physicalTerminal (v : (r.plan.finish h).Site) : (r.terminalLayer h).state.Site :=
  cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm v

private theorem casts_to_physical {X Y Z : Type} (e : X=Y) (f : Y=Z) (g : X=Z) (v : Z) :
    cast e ((Equiv.cast g).symm v)=cast f.symm v := by cases e;cases f;rfl

theorem finalSite_physical (v : (r.plan.finish h).Site) :
    cast (r.selectedSiteEq h) ((r.finalSite h).symm v)=r.physicalTerminal h v :=
  casts_to_physical (r.selectedSiteEq h) (congrArg Shape.Site (r.terminalLayer_shape h)) _ v

def archivePlanIndex (v : (r.plan.finish h).Site) :
    Fin ((r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count) :=
  ⟨(r.finalArchive h C O path).1.first+((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val,
    Nat.add_lt_add_left ((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).isLt _⟩

theorem archivePlanIndex_physical (v : (r.plan.finish h).Site) :
    r.archivePlanIndex h C O path v=r.archiveLastIndex h C O path (r.physicalTerminal h v) := by
  apply Fin.ext
  rw [←r.finalSite_physical h v]
  exact (r.archiveLastOrdinal h C O path ((r.finalSite h).symm v)).symm

/-- These are the actual network and arity for the root ordinal supplied by
the native group/slot selector, in precisely the finished Plan site type. -/
theorem archivePlanNetwork (v : (r.plan.finish h).Site) :
    let z:=r.archiveNode h J L N C O path zero (r.archivePlanIndex h C O path v)
    let result:=r.plan.assemble h (r.wordAssembly J L) N
    z.arity=result.1.width v ∧ HEq z.net ((result.2 v).compile) := by
  dsimp only
  rw [r.archivePlanIndex_physical]
  have atV : cast (congrArg Shape.Site (r.terminalLayer_shape h)) (r.physicalTerminal h v)=v :=
    (Equiv.cast (congrArg Shape.Site (r.terminalLayer_shape h))).apply_symm_apply v
  have found:=r.archiveLastNetwork h J L N C O path zero (r.physicalTerminal h v)
  have transport (a b : (r.plan.finish h).Site) (eqn : a=b) :
      HEq (((r.plan.assemble h (r.wordAssembly J L) N).2 a).compile)
        (((r.plan.assemble h (r.wordAssembly J L) N).2 b).compile) := by subst b; rfl
  exact ⟨by simpa only [atV] using found.1,found.2.trans (transport _ _ atV)⟩

/-- Ordered external origin pairs from the seed are the same ones decoded by
the terminal pin reader, including every inherited port after multiple moves. -/
theorem archivePlanExternal (v : (r.plan.finish h).Site) :
    let z:=r.archiveNode h J L N C O path zero (r.archivePlanIndex h C O path v)
    let endSite:=r.physicalTerminal h v
    z.external=(r.endWords h J L).ext endSite ∧
      List.ofFn z.origin=List.ofFn (r.extAncestor h J L endSite) := by
  dsimp only
  rw [r.archivePlanIndex_physical,r.archiveLastNode]
  exact ⟨rfl,rfl⟩

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
noncomputable section
variable {F Pins E : Type} [Field F] {d l : ℕ} {A : State d l}

/-- The only local induction obligations concern genuine moves and the
immediately preceding records addressed by their own archived child array. -/
def NodeSteps (Q : ℕ→SelectedNode F Pins E→Prop) : {d l : ℕ}→{A : State d l}→(r : Run F A)→
    (h : r.plan.History)→(J : Run.WordSteps Pins r)→(L : A.Words Pins)→Forest F L.ports.form→
    (C : r.Charges)→(O : A.ArchiveSites)→ r.ArchivePath h C O→(∀u,Fin (L.ext u)→E)→Prop
  | _,_,_,.done _,_,_,_,_,_,_,_,_=>True
  | _,_,_,.step R next,h,J,L,N,C,_O,p,orig=>
    let s:=J.1 L h.1
    (∀ v, (∀j,Q (p.1.data.child (p.1.sites.ord v) j) (nodeOfSite L N orig (p.1.row.children v j).val)) →
      Q (p.1.sites.id v) (nodeOfSite s.words (s.nextForest N) (pushedOrigin s orig) v)) ∧
    (next h.1).NodeSteps Q (tailHistory R next h) (J.2 h.1) s.words (s.nextForest N) (C.2 h.1)
      p.1.sites p.2 (pushedOrigin s orig)

/-- Induct over the authenticated S44 array using the selected seed and the
local rule at each physical stage, with no conditions at fictitious indices. -/
theorem selectedAt_induction (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (orig : ∀u,Fin (L.ext u)→E) (Q : ℕ→SelectedNode F Pins E→Prop)
    (seed : ∀u,Q (O.id u) (nodeOfSite L N orig u)) (nextRows : r.NodeSteps Q h J L N C O path orig)
    (i : ℕ) (lo hi) : Q i (r.selectedAt h J L N C O path orig i lo hi) := by
  induction r generalizing i with
  | done A=>
    let u:=O.ord.symm ⟨i-O.layer.first,by change i<O.layer.first+O.layer.count at hi;omega⟩
    have eqv : O.id u=i := by simp only [State.ArchiveSites.id,u,Equiv.apply_symm_apply];omega
    have seedU:=seed u
    rw [eqv] at seedU
    exact seedU
  | step R next ih=>
    by_cases early : i<O.layer.first+O.layer.count
    · rw [selectedAt,dite_eq_left early]
      let u:=O.ord.symm ⟨i-O.layer.first,by omega⟩
      have eqv : O.id u=i := by simp only [State.ArchiveSites.id,u,Equiv.apply_symm_apply];omega
      have seedU:=seed u
      rw [eqv] at seedU
      exact seedU
    · have later : path.1.sites.layer.first≤ i := by rw [path.1.row.contiguous];omega
      rw [selectedLater R next h J L N C O path orig i lo hi later]
      apply ih h.1 (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words ((J.1 L h.1).nextForest N)
        (C.2 h.1) path.1.sites path.2 (pushedOrigin (J.1 L h.1) orig) ?_ nextRows.2
      intro v
      apply nextRows.1 v
      intro j
      rw [path.1.row.childId]
      exact seed _

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins E : Type} [Field F] {d l : ℕ} {A : State d l}

theorem selectedAt_read (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (orig : ∀u,Fin (L.ext u)→E) (read : E→Pins→Bool)
    (initial : ∀u j pin,L.pin u pin j=read (orig u j) pin) (i : ℕ) (lo hi) :
    let z:=r.selectedAt h J L N C O path orig i lo hi
    ∀j pin,z.words.pin z.site pin j=read (z.origin j) pin := by
  induction r generalizing i with
  | done A=>exact initial _
  | step R next ih=>
    by_cases early : i<O.layer.first+O.layer.count
    · rw [selectedAt,dite_eq_left early]
      exact initial _
    · have later : path.1.sites.layer.first≤ i := by rw [path.1.row.contiguous];omega
      rw [selectedLater R next h J L N C O path orig i lo hi later]
      let s:=J.1 L h.1
      apply ih h.1 (tailHistory R next h) (J.2 h.1) s.words (s.nextForest N) (C.2 h.1) path.1.sites path.2
        (pushedOrigin s orig) ?_
      intro v j x
      exact (s.read v j x).trans (initial (s.origin v j).1.val (s.origin v j).2 x)

/-- Every external word at every selected node reads the actual original
endpoint bit, independently of that node's position in the archive. -/
theorem archiveNode_read (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (N : Forest F L.ports.form) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (zero : O.layer.first=0) (i : Fin ((r.finalArchive h C O path).1.first+(r.finalArchive h C O path).1.count)) :
    let z:=r.archiveNode h J L N C O path zero i
    ∀j pin,z.words.pin z.site pin j=L.pin (z.origin j).1 pin (z.origin j).2 :=
  r.selectedAt_read h J L N C O path (fun u j=>(⟨u,j⟩ : Σ u : A.Site,Fin (L.ext u)))
    (fun (a : Σ u,Fin (L.ext u)) pin=>L.pin a.1 pin a.2)
    (fun _ _ _=>rfl) i.val (by rw [zero]; exact Nat.zero_le _) i.isLt

theorem SelectedNode.arity_eq (z : SelectedNode F Pins E) : z.arity=z.external+z.words.ports.halfBits z.site := rfl

end
end ThreeFlat.Diagonal.PhysicalStage.Run

namespace ThreeFlat.Diagonal.PhysicalStage.Move.WordStep
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l} {R : Move F A D m} {i : Fin R.rules.count}
variable {L : A.Words Pins} (s : R.WordStep Pins L i)

/-- The genuine Plan stage child order transported to the physical target site. -/
def targetSite (v : (R.next i).Site) : (R.rules.target i).Site :=
  (Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm v

def children (v : (R.next i).Site) :
    Fin (s.stage.count (targetSite (R:=R) (i:=i) v)) ≃ {a // R.parent i a=v} :=
  (s.stage.child (targetSite (R:=R) (i:=i) v)).trans (Equiv.subtypeEquiv (Equiv.refl _) fun a=>by
    change (R.rules.owner i a=(Equiv.cast _).symm v) ↔ (Equiv.cast _ (R.rules.owner i a)=v)
    exact (Equiv.cast (congrArg Shape.Site (R.target_eq i))).eq_symm_apply.symm.symm)

variable {O : A.ArchiveSites} {ch : (R.next i).Site→ℕ} (row : R.ArchiveStep i O ch)

theorem count_eq (v : (R.next i).Site) : row.sites.layer.childCount=s.stage.count (targetSite (R:=R) (i:=i) v) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr ((row.row.children v).trans (s.children v).symm)

/-- An ordinal is preserved by the stage's typed forest and its archived child words. -/
def ChildOrder : Prop :=
  ∀v (j : Fin row.sites.layer.childCount),(row.row.children v j).val=
    ((s.children v) (j.cast (s.count_eq row v))).val

theorem childOrder_of_subsingleton (single : ∀v : (R.next i).Site,Subsingleton {a // R.parent i a=v}) :
    s.ChildOrder row := fun v _j=>congrArg Subtype.val (@Subsingleton.elim _ (single v) _ _)

theorem childId (order : s.ChildOrder row) (v : (R.next i).Site) (j : Fin row.sites.layer.childCount) :
    row.data.child (row.sites.ord v) j=O.id ((s.children v) (j.cast (s.count_eq row v))).val :=
  (row.row.childId v j).trans (congrArg O.id (order v j))

/-- Follow a selected compiled external bit back through the archived child word. -/
def originIndex (v : (R.next i).Site) (j : Fin (s.words.ext v)) : Fin row.sites.layer.childCount :=
  (((s.children v).symm (s.origin v j).1).cast (s.count_eq row v).symm)

theorem origin_childId (order : s.ChildOrder row) (v : (R.next i).Site) (j : Fin (s.words.ext v)) :
    row.data.child (row.sites.ord v) (s.originIndex row v j)=O.id (s.origin v j).1.val := by
  rw [s.childId row order v]
  have same : (s.originIndex row v j).cast (s.count_eq row v)=(s.children v).symm (s.origin v j).1 := Fin.ext rfl
  rw [same,Equiv.apply_symm_apply]

/-- External bits in each archived child row. The total function also applies
to the loop's unoccupied indices. -/
def childWidth (v : (R.next i).Site) (k : ℕ) : ℕ :=
  if hk : k<row.sites.layer.childCount then L.ext (row.row.children v ⟨k,hk⟩).val else 0

/-- Every numeric parent bit is exactly its child's prefix plus its residual
bit. Zero-length child intervals contribute zero to this address. -/
theorem origin_offset (order : s.ChildOrder row) (v : (R.next i).Site) (j : Fin (s.words.ext v)) :
    j.val=(∑ k : Fin (s.originIndex row v j).val,childWidth (L:=L) row v k.val)+(s.origin v j).2.val := by
  obtain ⟨hn,he⟩ := s.originOrder v
  let n := fun k : Fin (s.stage.count (targetSite (R:=R) (i:=i) v))=>L.ext (s.children v k).val
  let a : Σ k,Fin (n k) := finSigmaFinEquiv.symm (j.cast hn)
  have pair := he j
  have site : (s.origin v j).1=s.children v a.1 := Subtype.ext (congrArg Prod.fst pair)
  have residual : (s.origin v j).2.val=a.2.val := congrArg Prod.snd pair
  have index : (s.originIndex row v j).val=a.1.val := by
    change ((s.children v).symm (s.origin v j).1).val=a.1.val
    rw [site,Equiv.symm_apply_apply]
  have width (k : Fin a.1.val) :
      n (Fin.castLE a.1.isLt.le k)=childWidth (L:=L) row v k.val := by
    have hk : k.val<row.sites.layer.childCount := (k.isLt.trans_le (by rw [←index];exact (s.originIndex row v j).isLt.le))
    simp only [childWidth,dite_eq_left hk]
    rw [order v ⟨k.val,hk⟩]
    rfl
  have off : (finSigmaFinEquiv a).val=j.val := by
    change (finSigmaFinEquiv (finSigmaFinEquiv.symm (j.cast hn))).val=j.val
    simp
  rw [index,residual,←off,finSigmaFinEquiv_apply]
  congr 1
  exact Finset.sum_congr rfl (fun k _=>width k)

/-- The slot order of the native concatenated endpoint table, with the physical
old site and the local child bit left visible. -/
theorem origin_order (order : s.ChildOrder row) (v : (R.next i).Site) :
    List.ofFn (fun j : Fin (s.words.ext v)=>((s.origin v j).1.val,(s.origin v j).2.val)) =
      (List.ofFn (fun k : Fin row.sites.layer.childCount=>
        let u:=(row.row.children v k).val
        List.ofFn (fun b : Fin (L.ext u)=>(u,b.val)))).flatten := by
  classical
  let z := targetSite (R:=R) (i:=i) v
  let n := fun k : Fin (s.stage.count z)=>L.ext (s.children v k).val
  let f := fun (k : Fin (s.stage.count z)) (b : Fin (n k))=>((s.children v k).val,b.val)
  obtain ⟨hn,he⟩ := s.originOrder v
  have castList {a b : ℕ} (h : a=b) {α : Type} (g : Fin b→α) :
      List.ofFn (fun j : Fin a=>g (j.cast h))=List.ofFn g := by cases h;rfl
  calc
    _=List.ofFn (fun j : Fin (s.words.ext v)=>
        let p : Σ k,Fin (n k):=finSigmaFinEquiv.symm (j.cast hn)
        f p.1 p.2) := congrArg List.ofFn (funext he)
    _=List.ofFn (fun j : Fin (∑k,n k)=>let p : Σ k,Fin (n k):=finSigmaFinEquiv.symm j;f p.1 p.2) :=
      castList hn (fun j : Fin (∑ k,n k) =>
        let pair : Σ k,Fin (n k) := finSigmaFinEquiv.symm j
        f pair.1 pair.2)
    _=(List.ofFn (fun k=>List.ofFn (f k))).flatten := HistoryContraction.flatten_finSigma_order n f
    _=(List.ofFn (fun k : Fin row.sites.layer.childCount=>
      List.ofFn (f (k.cast (s.count_eq row v))))).flatten := congrArg List.flatten (castList (s.count_eq row v) (fun k=>List.ofFn (f k))).symm
    _=_ := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext k
      dsimp [f,n]
      rw [order v k]

end
end ThreeFlat.Diagonal.PhysicalStage.Move.WordStep

namespace ThreeFlat.Diagonal.PhysicalStage.Run
open HistoryContraction
noncomputable section
variable {F Pins : Type} [Field F]

/-- The dependent local predicate remembers the chosen word assembler (and
hence its exact tree syntax) beside the archive row on this historical branch. -/
abbrev WordVisit (F Pins : Type) [Field F] :=
  ∀{d l D m : ℕ} {A : State d l} (R : Move F A D m) (i : Fin R.rules.count) (L : A.Words Pins),
    R.WordStep Pins L i → (O : A.ArchiveSites) → (charge : (R.next i).Site→ℕ) → R.ArchiveStep i O charge → Prop

def WordVisits (check : WordVisit F Pins) : {d l : ℕ}→{A : State d l}→(r : Run F A)→(h : r.plan.History)→
    Run.WordSteps Pins r→A.Words Pins→(C : r.Charges)→(O : A.ArchiveSites) → r.ArchivePath h C O→Prop
  | _,_,_,.done _,_,_,_,_,_,_=>True
  | _,_,_,.step R next,h,J,L,C,O,p=>
    let step:=J.1 L h.1
    check R h.1 L step O (C.1 h.1) p.1 ∧ (next h.1).WordVisits check (tailHistory R next h)
      (J.2 h.1) step.words (C.2 h.1) p.1.sites p.2

def childVisit : WordVisit F Pins := fun _ _ _ s _ _ row=>s.ChildOrder row

abbrev OrderedArchive {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O) :=
  r.WordVisits childVisit h J L C O path

theorem wordVisits_mono {d l : ℕ} {A : State d l} (r : Run F A) (S T : WordVisit F Pins)
    (incl : ∀{d l D m} {a : State d l} (R : Move F a D m) i L w O c p,S R i L w O c p→T R i L w O c p)
    (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (path : r.ArchivePath h C O) (facts : r.WordVisits S h J L C O path) : r.WordVisits T h J L C O path := by
  induction r with
  | done=>trivial
  | step R next ih=>exact ⟨incl _ _ _ _ _ _ _ facts.1,
      ih h.1 (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words (C.2 h.1) path.1.sites path.2 facts.2⟩

theorem wordVisits_cast {d l : ℕ} {A : State d l} (r : Run F A) (S : WordVisit F Pins) {h h' : r.plan.History}
    (e : h=h') (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (facts : r.WordVisits S h J L C O p) :
    r.WordVisits S h' J L C O (e ▸ p) := by cases e;exact facts

theorem joined_wordVisits {d l D m : ℕ} {A : State d l} (R : Move F A D m) (next : ∀i,Run F (R.next i))
    (S : WordVisit F Pins) (J : Run.WordSteps Pins (Run.step R next)) (L : A.Words Pins)
    (C : (Run.step R next).Charges) (O : A.ArchiveSites) (i : Fin R.rules.count) (h : (next i).plan.History)
    (row : R.ArchiveStep i O (C.1 i)) (path : (next i).ArchivePath h (C.2 i) row.sites)
    (actual : S R i L (J.1 L i) O (C.1 i) row)
    (tail : (next i).WordVisits S h (J.2 i) (J.1 L i).words (C.2 i) row.sites path) :
    (Run.step R next).WordVisits S (joinHistory R next i h) J L C O (joinArchivePath R next C O i h row path) :=
  ⟨actual,wordVisits_cast (next i) S (tailHistory_joinHistory R next i h).symm _ _ _ _ _ tail⟩

theorem joined_orderedArchive {d l D m : ℕ} {A : State d l} (R : Move F A D m) (next : ∀i,Run F (R.next i))
    (J : Run.WordSteps Pins (Run.step R next)) (L : A.Words Pins) (C : (Run.step R next).Charges)
    (O : A.ArchiveSites) (i : Fin R.rules.count) (h : (next i).plan.History)
    (row : R.ArchiveStep i O (C.1 i)) (path : (next i).ArchivePath h (C.2 i) row.sites)
    (actual : (J.1 L i).ChildOrder row)
    (tail : (next i).OrderedArchive h (J.2 i) (J.1 L i).words (C.2 i) row.sites path) :
    (Run.step R next).OrderedArchive (joinHistory R next i h) J L C O (joinArchivePath R next C O i h row path) :=
  joined_wordVisits R next childVisit J L C O i h row path actual tail

/-- Stage-local native receipts suffice for induction over all typed archive
nodes, with the exact forest and original external bit maps threaded by the run. -/
theorem nodeSteps_of_wordVisits {E : Type} (test : WordVisit F Pins) (Q : ℕ→SelectedNode F Pins E→Prop)
    (advance : ∀{d l D m : ℕ} {B : State d l} (R : Move F B D m) (i : Fin R.rules.count)
      (L : B.Words Pins) (w : R.WordStep Pins L i) (O : B.ArchiveSites)
      (c : (R.next i).Site→ℕ) (p : R.ArchiveStep i O c),test R i L w O c p →
      ∀ (N : Forest F L.ports.form) (orig : ∀u,Fin (L.ext u)→E) (v : (R.next i).Site),
      (∀j,Q (p.data.child (p.sites.ord v) j) (nodeOfSite L N orig (p.row.children v j).val)) →
      Q (p.sites.id v) (nodeOfSite w.words (w.nextForest N) (pushedOrigin w orig) v))
    {d l : ℕ} {B : State d l} (r : Run F B) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : B.Words Pins) (N : Forest F L.ports.form) (C : r.Charges) (O : B.ArchiveSites)
    (p : r.ArchivePath h C O) (orig : ∀u,Fin (L.ext u)→E) (receipts : r.WordVisits test h J L C O p) :
    r.NodeSteps Q h J L N C O p orig := by
  induction r with
  | done=>trivial
  | step R next ih=>
    let w:=J.1 L h.1
    exact ⟨advance R h.1 L w O (C.1 h.1) p.1 receipts.1 N orig,
      ih h.1 (tailHistory R next h) (J.2 h.1) w.words (w.nextForest N) (C.2 h.1) p.1.sites p.2
        (pushedOrigin w orig) receipts.2⟩

open RAM.NavigationNodeRows

theorem archive_contains_input {d l : ℕ} {B : State d l} (r : Run F B) (h : r.plan.History) (C : r.Charges)
    (O : B.ArchiveSites) (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    ∃q∈r.archiveList h C O p seed,q.layer=O.layer := by
  cases r <;> exact ⟨_,List.mem_cons_self ..,rfl⟩

/-- Directory membership accompanies the native receipt for every visited
output layer, including the final one. -/
def wordVisitLayer (rows : List NodeRow) : WordVisit F Pins :=
  fun _ _ _ _ _ _ out=>∃ q∈rows,q.layer=out.sites.layer

theorem wordVisits_layers {d l : ℕ} {B : State d l} (r : Run F B) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : B.Words Pins) (C : r.Charges) (O : B.ArchiveSites)
    (p : r.ArchivePath h C O) (seed : LayerData O.layer) :
    r.WordVisits (wordVisitLayer (r.archiveList h C O p seed)) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>
    let z:=h.1
    let g:=tailHistory R next h
    let xs:=(next z).archiveList g (C.2 z) p.1.sites p.2 p.1.data
    obtain ⟨a,ha,eq⟩:=(next z).archive_contains_input g (C.2 z) p.1.sites p.2 p.1.data
    refine ⟨⟨a,List.mem_cons_of_mem _ ha,eq⟩,?_⟩
    apply wordVisits_mono (next z) (wordVisitLayer xs) _ _ g (J.2 z) (J.1 L z).words (C.2 z)
      p.1.sites p.2 (ih z g (J.2 z) (J.1 L z).words (C.2 z) p.1.sites p.2 p.1.data)
    intro _ _ _ _ _ a j layout words old c row hit
    obtain ⟨q,hq,e⟩:=hit
    exact ⟨q,List.mem_cons_of_mem _ hq,e⟩

theorem wordVisits_pair {d l : ℕ} {B : State d l} (r : Run F B) (left right : WordVisit F Pins)
    (h : r.plan.History) (J : Run.WordSteps Pins r) (L : B.Words Pins) (C : r.Charges) (O : B.ArchiveSites)
    (p : r.ArchivePath h C O) (a : r.WordVisits left h J L C O p) (b : r.WordVisits right h J L C O p) :
    r.WordVisits (fun m j l w o c row=>left m j l w o c row ∧ right m j l w o c row) h J L C O p := by
  induction r with
  | done=>trivial
  | step R next ih=>exact ⟨⟨a.1,b.1⟩,ih h.1 (tailHistory R next h) (J.2 h.1) (J.1 L h.1).words
      (C.2 h.1) p.1.sites p.2 a.2 b.2⟩

end
end ThreeFlat.Diagonal.PhysicalStage.Run

end OAI
