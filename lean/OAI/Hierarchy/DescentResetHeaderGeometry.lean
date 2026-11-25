import OAI.Hierarchy.DescentNativeResetEdgeTape
import OAI.Hierarchy.DescentCommonHostEdges

namespace OAI
/-! # Raw header fields of the physical old stem, transfer trunk and public contact -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentResetAttachments DescentRouterBank Computability.BorderVNP.Crossing
open private mem_marked_core from OAI.Hierarchy.DescentTrunkWorld
open scoped Classical BigOperators
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (input : Bool→A.graph.Edge→Q) (flag : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth input w)) (tab : R.Tables F)
local notation "W" => install A home input flag same R tab
local notation "names" => installedNames A home input flag same R tab
local notation "wires" => installedWireNames A home input flag same R tab

structure RawFields (X : Type*) where
  src : X
  dst : X
  width : ℕ
  core : Bool

def physicalFields (e : (W).graph.Edge) : RawFields ((Bool×H)⊕R.Site) :=
  ⟨names ((W).graph.src e),names ((W).graph.dst e),(W).graph.width e,decide (e∈(W).core)⟩

def sourceFields : (Bool×A.graph.Edge)⊕(H⊕R.Edge)→RawFields ((Bool×H)⊕R.Site)
  | .inl (s,i)=>⟨.inl (s,home (ends A.graph s i)),.inr (R.attach (s,input s i)),A.graph.width i,
    s || !(flag (home (A.graph.src i)))⟩
  | .inr (.inl z)=>⟨.inl (false,z),.inl (true,z),DescentNamedContact.width (moved A.graph home) A.graph.width z,!(flag z)⟩
  | .inr (.inr e)=>⟨.inr (R.src e),.inr (R.dst e),R.width e,true⟩

omit [Fintype Q] in
theorem sourceFields_read (e : (W).graph.Edge) :
    physicalFields A home input flag same R tab e=sourceFields A home input flag R (wires e) := by
  subst w
  have coreRead (u : (world A home input R tab flag).graph.Edge) :
      decide (u∈(world A home input R tab flag).core) = marked A home input R flag u := by
    simp only [mem_marked_core A home input R tab flag,Bool.decide_coe]
  unfold physicalFields
  refine (congrArg (RawFields.mk _ _ _) (coreRead e)).trans ?_
  rcases e with ⟨(_|_),i⟩|z|e <;> rfl


end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentChosenRouter DescentCommonHost DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "p" => Z.placement
local notation "m" => T.commonDepth
local notation "lab" => fun t=>shortName m (T.code t)
local notation "X" => Node Z.V (Z.V×DescentContacts.Endpoint (2^Z.n))
  (Computability.BorderVNP.Crossing.Network.Site (DescentCommonPalette.rotor Z.graph))
local notation "view" => bankNode (p) Z.graph m T.code Z.positive Z.pay Z.circuit d
local notation "eqWidth" => funext (fun e=>Eq.symm (Z.allWidths e))
local notation "wires" => installedWireNames A T.home Z.placement.input T.hub eqWidth Z.bank Z.tables

/-- Physical transposition is invisible to these four local integer fields. -/
def cableFields (e : (W).graph.Edge) : RawFields X :=
  ⟨commonName Z T ((W).graph.src e),commonName Z T ((W).graph.dst e),
    (W).graph.width e,decide (e∈(W).core)⟩

theorem stemFields (s : Bool) (i : A.graph.Edge) :
    cableFields Z T ((wires).symm (.inl (s,i)))=
      ⟨.trunk s (lab (T.home (ends A.graph s i))),publicNode (p) Z.graph m T.code s ((p).input s i),
        Z.unit,s || !(T.hub (T.home (A.graph.src i)))⟩ := by
  let e:=(wires).symm (.inl (s,i))
  have h:=sourceFields_read A T.home (p).input T.hub eqWidth Z.bank Z.tables e
  dsimp only [e] at h
  rw [Equiv.apply_symm_apply] at h
  let project : RawFields ((Bool×Z.Fallback)⊕Z.bank.Site)→RawFields X := fun a=>
    let v:=Sum.elim (fun st : Bool×Z.Fallback=>Node.trunk st.1 (lab st.2)) view
    ⟨v a.src,v a.dst,a.width,a.core⟩
  apply (congrArg project h).trans
  simp only [project,sourceFields,Z.allWidths]
  exact congrArg (fun dst => RawFields.mk _ dst _ _)
    (publicNode_at (p) Z.graph m T.code Z.positive Z.pay Z.circuit d s ((p).input s i))

theorem trunkFields (t : Z.Fallback) :
    cableFields Z T ((wires).symm (.inr (.inl t)))=
      ⟨.trunk false (lab t),.trunk true (lab t),
       Fintype.card {i : A.graph.Edge // T.home (A.graph.dst i)=t} * Z.unit,!(T.hub t)⟩ := by
  have h:=sourceFields_read A T.home (p).input T.hub eqWidth Z.bank Z.tables ((wires).symm (.inr (.inl t)))
  rw [Equiv.apply_symm_apply] at h
  let project : RawFields ((Bool×Z.Fallback)⊕Z.bank.Site)→RawFields X := fun a=>
    let v:=Sum.elim (fun st : Bool×Z.Fallback=>Node.trunk st.1 (lab st.2)) view
    ⟨v a.src,v a.dst,a.width,a.core⟩
  apply (congrArg project h).trans
  simp [project,sourceFields,DescentNamedContact.width,Z.allWidths,moved]
  exact ⟨rfl,rfl⟩

theorem contactFields (c : (p).Contact) :
    cableFields Z T ((wires).symm (.inr (.inr (.inl c))))=
      ⟨direct Z.graph false (linkSocket (p) lab m false c),direct Z.graph true (linkSocket (p) lab m true c),
       Fintype.card {i : A.graph.Edge // (p).contact i=c} * Z.unit,true⟩ := by
  have h:=sourceFields_read A T.home (p).input T.hub eqWidth Z.bank Z.tables ((wires).symm (.inr (.inr (.inl c))))
  rw [Equiv.apply_symm_apply] at h
  let project : RawFields ((Bool×Z.Fallback)⊕Z.bank.Site)→RawFields X := fun a=>
    let v:=Sum.elim (fun st : Bool×Z.Fallback=>Node.trunk st.1 (lab st.2)) view
    ⟨v a.src,v a.dst,a.width,a.core⟩
  apply (congrArg project h).trans
  have left:=direct_at (p) Z.graph m T.code Z.positive Z.pay Z.circuit d false c
  have right:=direct_at (p) Z.graph m T.code Z.positive Z.pay Z.circuit d true c
  change RawFields.mk (view (Z.bank.src (.inl c))) (view (Z.bank.dst (.inl c)))
    (Z.bank.width (.inl c)) true=_
  have width : Z.bank.width (.inl c) = Fintype.card {i : A.graph.Edge // (p).contact i=c} * Z.unit := by
    change DescentNamedContact.width (p).contact (fun _ => Z.unit) c = _
    simp [DescentNamedContact.width]
    let rosterCount : Fintype {i : A.graph.Edge // (p).contact i = c} := inferInstance
    let fibreCount : Fintype {i : A.graph.Edge // (p).contact i = c} :=
      @Subtype.fintype A.graph.Edge (fun i => (p).contact i = c)
        (fun i => Classical.propDecidable ((p).contact i = c)) A.graph.finiteEdge
    exact Or.inl (@Fintype.card_congr _ _ fibreCount rosterCount (Equiv.refl _))
  have combine {a b a' b' : X} {k k' : ℕ} (l : a=a') (r : b=b') (eq : k=k') :
      RawFields.mk a b k true = RawFields.mk a' b' k' true := by
    cases l; cases r; cases eq; rfl
  exact combine left right width

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
