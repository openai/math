import OAI.Hierarchy.DescentResetHeaderGeometry
import OAI.Hierarchy.DescentIssuedTerminalId
import OAI.Hierarchy.DescentInstalledRotorHeader

namespace OAI
/-! # Sparse headers of the non-private wires on the true reset shelf -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentRelativeContacts DescentCommonHost DescentDenseHostOrder
open DescentChosenRouter DescentResetCableSlots
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "R" => Z.placement
local notation "X" => Node Z.V (Z.V×DescentContacts.Endpoint (2^Z.n)) (DescentCommonPalette.rotor Z.graph).Site
local notation "r" => Z.k-T.commonDepth
local notation "palette" => roster Z.graph r Ht
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "wires" => installedWireNames A T.home (R).input T.hub same Z.bank Z.tables
local notation "lab" => fun t=>shortName T.commonDepth (T.code t)
local notation "legal" => fun t=>(T.codeLegal t).2
variable {H M : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin M)

def codeHost (x : X) :=
  let localShape:=shape Z.graph x
  let localID:=if h : localShape∈palette then (localRank Z.graph r Ht ⟨localShape,h⟩).val else 0
  localID+(palette).card*(vertex (position Z.graph x)).val

theorem codeHost_at (u : (W).graph.Site) :
    codeHost Z T vertex (commonName Z T u)=(rawHostRank Z T vertex (placed Z T u)).val := by
  have inside : shape Z.graph (commonName Z T u) ∈ palette :=
    (localShape Z T (placed Z T u)).property
  rw [rawHostRank_read]
  change (if _ : shape Z.graph _∈palette then _ else 0)+_=_
  rw [dite_eq_left inside]
  rfl

def actualFields (wire : (W).graph.Edge) : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool :=
  ((installedResetOrdinal Z T vertex key wire).val,
   (rawHostRank Z T vertex (placed Z T ((W).graph.src wire))).val,
   (rawHostRank Z T vertex (placed Z T ((W).graph.dst wire))).val,
   (blockId Z T ((W).graph.src wire)).val,(blockId Z T ((W).graph.dst wire)).val,
   (W).graph.width wire,decide (wire∈(W).core))

private theorem fromFields (e : (W).graph.Edge) (a : RawFields X)
    (read : cableFields Z T e=a) {j loc : ℕ} (id : (installedResetOrdinal Z T vertex key e).val=j)
    (atBlock : (blockId Z T ((W).graph.src e)).val=loc) :
    actualFields Z T vertex key e=(j,codeHost Z T vertex a.src,codeHost Z T vertex a.dst,loc,loc,a.width,a.core) := by
  have ends:=congrArg Fin.val (block_edges Z T e)
  unfold actualFields
  rw [id,←codeHost_at,←codeHost_at,atBlock,←ends,atBlock]
  rw [show commonName Z T ((W).graph.src e)=a.src from congrArg RawFields.src read,
      show commonName Z T ((W).graph.dst e)=a.dst from congrArg RawFields.dst read,
      show (W).graph.width e=a.width from congrArg RawFields.width read,
      show decide (e∈(W).core)=a.core from congrArg RawFields.core read]

theorem stemArchive (s : Bool) (i : A.graph.Edge) :
    let t:=T.home (ends A.graph s i)
    let pos:=coarseName T.commonDepth (T.code t)
    actualFields Z T vertex key ((wires).symm (.inl (s,i)))=
      ((key i).val+M*(finTwoEquiv.symm s).val,codeHost Z T vertex (.trunk s (lab t)),
        codeHost Z T vertex (publicNode (R) Z.graph T.commonDepth T.code s ((R).input s i)),
        pos,pos,Z.unit,s || !(T.hub (T.home (A.graph.src i)))) := by
  apply fromFields Z T vertex key _ _ (stemFields Z T s i)
  · change ((DescentResetCableSlots.complete (R) vertex T.code legal Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key) ((wires) ((wires).symm _))).val=_
    rw [Equiv.apply_symm_apply];rfl
  · have data:=sourceFields_read A T.home (R).input T.hub same Z.bank Z.tables ((wires).symm (.inl (s,i)))
    rw [Equiv.apply_symm_apply] at data
    exact congrArg (DescentCommonHost.rawCoordinate (R) Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d)
      (congrArg RawFields.src data)

theorem trunkArchive (t : Z.Fallback) :
    let pos:=coarseName T.commonDepth (T.code t)
    actualFields Z T vertex key ((wires).symm (.inr (.inl t)))=
      (2*M+(terminal vertex T.code legal t).val,codeHost Z T vertex (.trunk false (lab t)),
        codeHost Z T vertex (.trunk true (lab t)),pos,pos,
        Fintype.card {i : A.graph.Edge // T.home (A.graph.dst i)=t}*Z.unit,!(T.hub t)) := by
  apply fromFields Z T vertex key _ _ (trunkFields Z T t)
  · change ((DescentResetCableSlots.complete (R) vertex T.code legal Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key) ((wires) ((wires).symm _))).val=_
    rw [Equiv.apply_symm_apply];rfl
  · have data:=sourceFields_read A T.home (R).input T.hub same Z.bank Z.tables ((wires).symm (.inr (.inl t)))
    rw [Equiv.apply_symm_apply] at data
    exact congrArg (DescentCommonHost.rawCoordinate (R) Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d)
      (congrArg RawFields.src data)

theorem contactArchive (c : (R).Contact) :
    let pos:=(R).siteGroup T.commonDepth T.code ((R).owner false c)
    actualFields Z T vertex key ((wires).symm (.inr (.inr (.inl c))))=
      (2*M+(H*(2^(Z.k+1)*(2^Z.n+1))+(contact (R) vertex T.code legal Ht T.bookHeight c).val),
       codeHost Z T vertex (direct Z.graph false (linkSocket (R) lab T.commonDepth false c)),
       codeHost Z T vertex (direct Z.graph true (linkSocket (R) lab T.commonDepth true c)),pos,pos,
       Fintype.card {i : A.graph.Edge // (R).contact i=c}*Z.unit,true) := by
  apply fromFields Z T vertex key _ _ (contactFields Z T c)
  · change ((DescentResetCableSlots.complete (R) vertex T.code legal Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key) ((wires) ((wires).symm _))).val=_
    rw [Equiv.apply_symm_apply];rfl
  · have data:=sourceFields_read A T.home (R).input T.hub same Z.bank Z.tables ((wires).symm (.inr (.inr (.inl c))))
    rw [Equiv.apply_symm_apply] at data
    exact congrArg (DescentCommonHost.rawCoordinate (R) Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d)
      (congrArg RawFields.src data)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
