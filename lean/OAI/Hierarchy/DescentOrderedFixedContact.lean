import OAI.Hierarchy.DescentOrderedContactRelay
import OAI.Hierarchy.DescentFixedNamedContact
import OAI.Hierarchy.DescentWireRelabel

namespace OAI
/-! # Sparse direct bit tests at the actual fixed-directory fallback router -/

namespace Hierarchy.DescentOrderedWords.Named
open Computability.BorderVNP.Crossing DescentContactTree DescentNamedContact
open scoped BigOperators Classical
noncomputable section
variable {I C : Type} [Fintype I] [Fintype C] {N h D : ℕ} (key : I↪Fin N)
  (book : C↪Node h) (contact : I→C) (wt : I→ℕ)

def fibreKey (c : C) : Fibre contact c↪Fin N := (Function.Embedding.subtype _).trans key

def wirePerm (e : Physical.Edge h) : Equiv.Perm (Fin ((DescentFixedNamedContact.network book contact wt D).width e)) :=
  permutation (Contact.cellKey key (DescentFixedNamedContact.code book contact) (e.1.val+1) e.2)
    (fun i=>wt i.val)

def pinPerm (p : Pin C) : Equiv.Perm (Fin (bits contact wt p)) := match p with
  | .inl _ => permutation key wt
  | .inr c => permutation (fibreKey key contact c) (fun i=>wt i.val)

def branchRead (p : Ports (bits contact wt)) (i : I) :=
  decode (fibreKey key contact (contact i)) (fun t=>wt t.val) (p (.inr (contact i))) ⟨i,rfl⟩

omit [Fintype C] in
theorem roots (p : Ports (bits contact wt)) :
    root contact wt (DescentWireRelabel.pins (pinPerm key contact wt) p)=decode key wt (p (.inl ())) :=
  (decode_eq key wt _).symm

omit [Fintype C] in
theorem branch (p : Ports (bits contact wt)) :
    branches contact wt (DescentWireRelabel.pins (pinPerm key contact wt) p)=branchRead key contact wt p := by
  funext i
  exact congrFun (decode_eq (fibreKey key contact (contact i))
    (fun z => wt z.val) (p (.inr (contact i)))).symm (⟨i, rfl⟩ : Fibre contact (contact i))

def tables {K : Type*} [CommSemiring K] := DescentWireRelabel.tables (DescentFixedNamedContact.network book contact wt D)
  (wirePerm (D:=D) key book contact wt) (pinPerm key contact wt) (DescentFixedNamedContact.tables (K:=K) book contact wt D)

omit [Fintype C] in
theorem read {K : Type*} [CommSemiring K] (a : (DescentFixedNamedContact.network book contact wt D).Assignment)
    (p : Ports (bits contact wt)) (q : Physical.Site h) :
    (DescentFixedNamedContact.network book contact wt D).read (tables (K:=K) key book contact wt) a p q=
    let d := DescentFixedNamedContact.code book contact
    let z := Contact.innerRows (D:=D) key d wt a
    if ∀i : Cell d q.1.val q.2,Physical.incoming wt (decode key wt (p (.inl ()))) z q.1 i.val=
      Physical.outgoing wt (branchRead key contact wt p) z q.1 i.val then 1 else 0 := by
  let d := DescentFixedNamedContact.code book contact
  let pins := DescentWireRelabel.pins (pinPerm key contact wt) p
  let edges := Contact.remapEdges (D:=D) key d wt a
  let expose := fun x : Ports (bits contact wt) =>
    Physical.exposed (h:=h) d wt (root contact wt x) (branches contact wt x)
  refine (DescentWireRelabel.read (DescentFixedNamedContact.network book contact wt D)
    (wirePerm (D:=D) key book contact wt) (pinPerm key contact wt)
    (DescentFixedNamedContact.tables (K:=K) book contact wt D) a p q).trans ?_
  refine (DescentLocalAdapters.read (DescentFixedNamedContact.paddedTree book contact wt D)
    (DescentFixedNamedContact.place book) (bits contact wt) (Physical.tables (K:=K) d wt)
    expose (DescentFixedNamedContact.at_terminals book contact wt D) edges pins q).trans ?_
  refine (DescentLocalTables.read (Physical.graph d wt D h)
    (Physical.relayFactor (K:=K) (D:=D) (h:=h) d wt) (Physical.supported d wt)
    edges (expose pins) q).trans ?_
  simp only [Physical.relayFactor,expose,Physical.top_exposed,Physical.ground_exposed,
    pins,roots,branch,edges,d]
  rw [Contact.inner_eq (D:=D) (h:=h) key (DescentFixedNamedContact.code book contact) wt a]

omit [Fintype C] in
theorem value {K : Type*} [CommSemiring K] (p : Ports (bits contact wt)) :
    (DescentFixedNamedContact.network book contact wt D).value (tables (K:=K) key book contact wt) p =
    if decode key wt (p (.inl ()))=branchRead key contact wt p then 1 else 0 := by
  let pins := DescentWireRelabel.pins (pinPerm key contact wt) p
  refine (DescentWireRelabel.value (DescentFixedNamedContact.network book contact wt D)
    (wirePerm (D:=D) key book contact wt) (pinPerm key contact wt)
    (DescentFixedNamedContact.tables (K:=K) book contact wt D) p).trans ?_
  simpa only [pins,roots,branch] using
    (DescentFixedNamedContact.value (K:=K) book contact wt D pins)

end
end Hierarchy.DescentOrderedWords.Named

end OAI
