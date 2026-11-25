import OAI.Hierarchy.DescentResetParentWindows
import OAI.Hierarchy.DescentPackedPrivateHardware
import OAI.Hierarchy.DescentInstalledPublicHeader

namespace OAI
/-! # Installed row identifiers and oriented fields on the actual named successor -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetCableSlots DescentRouterSlots DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentCommonHost DescentHostDirectory
open scoped Classical

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
  {H M : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin M)
local notation "W" => reenter Z T
local notation "R" => Z.placement
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "wires" => installedWireNames A T.home (R).input T.hub same Z.bank Z.tables
local notation "menu" => selected (R) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align (D:=d)
local notation "legal" => fun t=>(T.codeLegal t).2
local notation "layout" => DescentResetCableSlots.complete (R) vertex T.code legal Ht T.bookHeight
  Z.graph Z.positive Z.pay Z.circuit d key

/-- The separating sparse row address is carried by the row index, while
the first data column announces that the record is present. -/
def fieldColumns (a : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool) : Fin 7→ℕ :=
  let (_,src,dst,left,right,width,marked):=a
  ![1,src,dst,left,right,width,marked.toNat]

theorem fields_record (e : (W).graph.Edge) :
    fieldColumns (actualFields Z T vertex key e)=actualRecord Z T vertex e := by
  by_cases live : e∈(W).core <;> simp [fieldColumns,actualFields,actualRecord,live]

/-- The private lookup slot names this very installed wire, for either the
rotor or exceptional tree branch of the same catalog. -/
theorem private_row_id (s : Bool) (g : (R).Site) (e : (dev (menu s g)).Edge) :
    (actualFields Z T vertex key (privateWireAt Z T s g e)).1=
      (layout (.inr (.inr (.inr ⟨(s,g),e⟩)))).val :=
  congrArg Prod.fst (privateArchive Z T vertex key s g e)

/-- Attach the public sparse row index to all seven private data columns.
The row may be obtained directly from either of the native packed readers. -/
theorem private_stamped (s : Bool) (g : (R).Site) (e : (dev (menu s g)).Edge)
    (observed : Fin 7→ℕ) (read : observed=actualRecord Z T vertex (privateWireAt Z T s g e)) :
    let installed:=actualFields Z T vertex key (privateWireAt Z T s g e)
    ((layout (.inr (.inr (.inr ⟨(s,g),e⟩)))).val,observed)=(installed.1,fieldColumns installed) :=
  Prod.ext (private_row_id Z T vertex key s g e).symm
    (read.trans (fields_record Z T vertex key _).symm)

theorem contact_row (c : (R).Contact) :
    let e:=(wires).symm (.inr (.inr (.inl c)))
    let b:=(R).siteGroup T.commonDepth T.code ((R).owner false c)
    let lab:=fun t=>shortName T.commonDepth (T.code t)
    (actualFields Z T vertex key e).1=
        2*M+(H*(2^(Z.k+1)*(2^Z.n+1))+(contact (R) vertex T.code legal Ht T.bookHeight c).val) ∧
      actualRecord Z T vertex e=
        ![1,codeHost Z T vertex (direct Z.graph false (linkSocket (R) lab T.commonDepth false c)),
          codeHost Z T vertex (direct Z.graph true (linkSocket (R) lab T.commonDepth true c)),
          b,b,Fintype.card {i : A.graph.Edge // (R).contact i=c}*Z.unit,1] := by
  have issued:=contactArchive Z T vertex key c
  exact ⟨congrArg Prod.fst issued,
    (fields_record Z T vertex key _).symm.trans (congrArg fieldColumns issued)⟩

end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open scoped Classical

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "raw" => B.raw
local notation "A" => B.next.placement
local notation "groups" => S.groupCount (i+1)
local notation "dense" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "rawSite" => (raw).siteFrom (groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "board" => blocks B
local notation "installed" => (Z).actualRecord T vertex

theorem named_home (v : (coarse).graph.Site) :
    Stage.home A (hop v)=
      (((digits ((Z).blockId T v)).1,(Z).placed T v),(digits ((Z).blockId T v)).2) := by
  obtain ⟨p,b⟩ := B.rawGeometry
  change ((raw).pos ((hop).symm (hop v)),(raw).block ((hop).symm (hop v)))=_
  exact (congrArg (fun x => ((raw).pos x, (raw).block x)) ((hop).symm_apply_apply v)).trans
    (Prod.ext (congrFun p v) (congrFun b v))

/-- Read the actual seven columns at either end. The high and low digits
of the common block name locate that end on the next phase. The rectangular
host code compacts to the next host ordinal by counting earlier occupied hosts. -/
theorem signed_header (e : (coarse).graph.Edge) (side : Bool) :
    let row:=installed e
    let endpoint:=if side then (board).dst e else (board).src e
    let hostCode:=row (if side then 2 else 1)
    let coordinate:=row (if side then 4 else 3)
    (row 0=1) ∧ ((Z).rawHostRank T vertex endpoint.1.2).val=hostCode ∧
      endpoint.1.1.val=coordinate/2^k ∧ endpoint.2.val=coordinate%2^k ∧
      (B.next.vertex endpoint.1.2).val=
        (Finset.univ.filter (fun v=>(dense v)<hostCode)).card ∧
      row 5=(board).count e*(Z).unit ∧ row 6=(decide (e∈(coarse).core)).toNat := by
  have site (v : (coarse).graph.Site) :
      let t:=Stage.home A (hop v)
      let addr:=((Z).blockId T v).val
      ((Z).rawHostRank T vertex t.1.2).val=((Z).rawHostRank T vertex ((Z).placed T v)).val ∧
        t.1.1.val=addr/2^k ∧ t.2.val=addr%2^k ∧
        (B.next.vertex t.1.2).val=
          (Finset.univ.filter (fun u=>(dense u)<((Z).rawHostRank T vertex ((Z).placed T v)).val)).card := by
    dsimp only
    rw [named_home B v]
    exact ⟨rfl,rfl,rfl,(Z).denseHostRank_read T vertex _⟩
  have width : (coarse).graph.width e=(board).count e*(Z).unit := (weight_width B e).symm
  have mark : (if e∈(coarse).core then 1 else 0)=(decide (e∈(coarse).core)).toNat := by
    by_cases yes : e∈(coarse).core <;> simp [yes]
  cases side with
  | false =>
    have atSource:=site ((coarse).graph.src e)
    exact ⟨rfl,atSource.1,atSource.2.1,atSource.2.2.1,atSource.2.2.2,width,mark⟩
  | true =>
    have atTarget:=site ((coarse).graph.dst e)
    exact ⟨rfl,atTarget.1,atTarget.2.1,atTarget.2.2.1,atTarget.2.2.2,width,mark⟩

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
