import OAI.Hierarchy.DescentRotorPrivateFields
import OAI.Hierarchy.DescentResetHeaderGeometry
import OAI.Hierarchy.DescentReentryCommonBlocks

namespace OAI
/-! # Numerical private rotor headers on the genuine reentered graph -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentChosenRouter DescentCommonHost DescentRotorPrivateFields
open DescentRelativeContacts
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "p" => Z.placement
local notation "Q" => DescentCommonPalette.rotor Z.graph
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "wires" => installedWireNames A T.home (p).input T.hub same Z.bank Z.tables
local notation "levelsOf" => DescentChosenRouter.selectedRotorLayers (p) Z.graph Z.positive Z.pay Z.circuit
local notation "siteOf" => fun (s : Bool) (g : (p).Good) =>
  DescentCommonPalette.rotorSiteEquiv Z.graph d (levelsOf s g) C Z.width Z.unit
local notation "edgeOf" => fun (s : Bool) (g : (p).Good) =>
  DescentCommonPalette.rotorEdgeEquiv Z.graph d (levelsOf s g) C Z.width Z.unit

def rotorWireAt (s : Bool) (g : (p).Good) (e : (Q).Edge) : (W).graph.Edge :=
  (wires).symm (.inr (.inr (.inr ⟨(s,.inl g),(edgeOf s g) e⟩)))

def rotorSiteAt (s : Bool) (g : (p).Good) (v : (Q).Site) : (W).graph.Site :=
  (resetNames Z T).symm (.inr ⟨(s,.inl g),(siteOf s g) v⟩)

private theorem physicalRow_eq {X : Type*} {a b a' b' : X} {n n' : ℕ}
    (left : a=a') (right : b=b') (width : n=n') :
    RawFields.mk a b n true = RawFields.mk a' b' n' true := by
  cases left
  cases right
  cases width
  rfl

theorem rotorFields (s : Bool) (g : (p).Good) (e : (Q).Edge) :
    physicalFields A T.home (p).input T.hub same Z.bank Z.tables (rotorWireAt Z T s g e)=
      ⟨.inr ⟨(s,.inl g),(siteOf s g) ((Q).src e)⟩,.inr ⟨(s,.inl g),(siteOf s g) ((Q).dst e)⟩,
       (Z.circuit s g).layers*(Z.unit*DescentRotorPrivateFields.price Z.graph C Z.width e),true⟩ := by
  let name : (Bool × A.graph.Edge) ⊕ (Z.Fallback ⊕ Z.bank.Edge) :=
    .inr (.inr (.inr ⟨(s,.inl g),(edgeOf s g) e⟩))
  refine (sourceFields_read A T.home (p).input T.hub same Z.bank Z.tables ((wires).symm name)).trans ?_
  refine (congrArg (sourceFields A T.home (p).input T.hub Z.bank) ((wires).apply_symm_apply name)).trans ?_
  let H := DescentPhysicalSplit.graph (DescentRotor.Physical.host Z.graph.arcs d
    (levelsOf s g) C Z.width Z.unit)
  let wrap (v : H.Site) : (Bool × Z.Fallback) ⊕ Z.bank.Site := .inr ⟨(s,.inl g),v⟩
  exact physicalRow_eq
    (congrArg wrap (DescentCommonPalette.rotor_left Z.graph d (levelsOf s g) C Z.width Z.unit e))
    (congrArg wrap (DescentCommonPalette.rotor_right Z.graph d (levelsOf s g) C Z.width Z.unit e))
    ((edge_width Z.graph d (levelsOf s g) C Z.width Z.unit e).trans
      (congrArg (fun layers : ℕ => layers*(Z.unit*DescentRotorPrivateFields.price Z.graph C Z.width e))
        (DescentChosenRouter.selectedRotorLayers_eq (p) Z.graph Z.positive Z.pay Z.circuit s g)))

variable {H L : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin L)
def rotorHostId (s : Bool) (g : (p).Good) (v : (Q).Site) : ℕ :=
  (rawHostRank Z T vertex (placed Z T (rotorSiteAt Z T s g v))).val

/-- Both endpoint IDs, both common-block numbers, integral live width and the eligible mark
are projected from the physical parent at its real complete sparse cable ordinal. -/
theorem rotorArchive (s : Bool) (g : (p).Good) (e : (Q).Edge) :
    let wire:=rotorWireAt Z T s g e
    let source:=(W).graph.src wire
    let target:=(W).graph.dst wire
    let c:=(p).siteGroup T.commonDepth T.code (.inl g)
    ((installedResetOrdinal Z T vertex key wire).val,
      (rawHostRank Z T vertex (placed Z T source)).val,(rawHostRank Z T vertex (placed Z T target)).val,
      (blockId Z T source).val,(blockId Z T target).val,(W).graph.width wire,decide (wire∈(W).core))=
      (completePort (oldCap:=L) Z.graph (p) Ht vertex s g e,
        rotorHostId Z T vertex s g ((Q).src e),rotorHostId Z T vertex s g ((Q).dst e),
        c,c,(Z.circuit s g).layers*(Z.unit*DescentRotorPrivateFields.price Z.graph C Z.width e),true) := by
  let wire:=rotorWireAt Z T s g e
  have raw:=rotorFields Z T s g e
  have left : (resetNames Z T) ((W).graph.src wire)=.inr ⟨(s,.inl g),(siteOf s g) ((Q).src e)⟩ :=
    congrArg RawFields.src raw
  have right : (resetNames Z T) ((W).graph.dst wire)=.inr ⟨(s,.inl g),(siteOf s g) ((Q).dst e)⟩ :=
    congrArg RawFields.dst raw
  have sc : (W).graph.src wire=rotorSiteAt Z T s g ((Q).src e) := (Equiv.eq_symm_apply _).2 left
  have tc : (W).graph.dst wire=rotorSiteAt Z T s g ((Q).dst e) := (Equiv.eq_symm_apply _).2 right
  have pos (v : (Q).Site) : (blockId Z T (rotorSiteAt Z T s g v)).val=(p).siteGroup T.commonDepth T.code (.inl g) := by
    exact congrArg (DescentCommonHost.rawCoordinate (p) Z.graph T.commonDepth T.code Z.positive Z.pay Z.circuit d)
      ((resetNames Z T).apply_symm_apply (.inr ⟨(s,.inl g),(siteOf s g) v⟩))
  have id : (installedResetOrdinal Z T vertex key wire).val=completePort (oldCap:=L) Z.graph (p) Ht vertex s g e := by
    change (DescentResetCableSlots.complete (p) vertex T.code (fun t=>(T.codeLegal t).2) Ht T.bookHeight Z.graph
      Z.positive Z.pay Z.circuit d key ((wires) ((wires).symm _))).val=_
    rw [Equiv.apply_symm_apply]
    change completePort (oldCap:=L) Z.graph (p) Ht vertex s g ((edgeOf s g).symm ((edgeOf s g) e))=_
    rw [Equiv.symm_apply_apply]
  have width : (W).graph.width wire = (Z.circuit s g).layers *
      (Z.unit * DescentRotorPrivateFields.price Z.graph C Z.width e) := congrArg RawFields.width raw
  have core : decide (wire∈(W).core)=true := congrArg RawFields.core raw
  let host (v : (W).graph.Site) := (rawHostRank Z T vertex (placed Z T v)).val
  let block (v : (W).graph.Site) := (blockId Z T v).val
  exact Prod.ext id (Prod.ext (congrArg host sc) (Prod.ext (congrArg host tc)
    (Prod.ext ((congrArg block sc).trans (pos _)) (Prod.ext ((congrArg block tc).trans (pos _))
      (Prod.ext width core)))))

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
