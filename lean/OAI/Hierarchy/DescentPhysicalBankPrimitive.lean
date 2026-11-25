import OAI.Hierarchy.DescentResetNodeAdmission
import OAI.Hierarchy.DescentResetBankTagCases
import OAI.Hierarchy.DescentPrimitiveBankRoleFields
import OAI.Hierarchy.DescentBundleBank

namespace OAI
/-! # Every reached bank-local primitive from original rotation words and cable spans -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
set_option quotPrecheck false
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetActorClass DescentCommonHost
open Reached.NodeCells DescentColonies
open scoped Classical Fin.CommRing
variable [Fintype P] (stored : b.Recorded p) (token : a.bit.Tokenized cap.placement.records)
local notation "Y" => b.next
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)
local notation "prevRank" => (Y).vertex.trans (Fin.castLEEmb (Y).valid.host)
local notation "census" => Census.count (Y).placement (Equiv.refl _) prevRank
local notation "cell" => whereAt Y next order
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation "actorAt" => (fun rack : Fin H => (ClosedReset.Window.paidActorAt b rack).elim 0 (fun u=>DescentResetActorClass.indexed b.reset.graph res u.val))

open DescentPackedResetRotorRoles DescentResetMetadataInputs DescentBundleHistory
variable (layout : DescentPrimitiveBirth.Layout)
local notation "project" ty:arg ptr:arg => Fin.cast (congrArg (fun j : ℕ=>2^j) (Eq.symm ty)) (originClass b hp whole a (.inr (.inr ptr)))
local notation "program" => b.reset.laneProgram key m p hp fit
local notation "plan" => b.reset.laneShape key m p hp fit
local notation "rootSite" wing:arg g:arg v:arg => (⟨(wing,.inl g),⟨v,.inl false⟩⟩:b.reset.bank.Site)

set_option maxHeartbeats 3000000 in
omit [Fintype P] in
/-- The two original arrays used on a bank node are the guarded rotor rotation at its
physical layer and the F6 fields of its actual public/private argument slots. -/
theorem physical_bank_tag (typeClass : layout.classBits=indexBits b.reset.n res)
    (rootCount : 2*(2^res*2^b.reset.n)=layout.roots)
    (ptr : NodeOrder.Global prog) (n : Fin layout.nodes) (spans : Fin layout.arguments→Cell layout.spanBits)
    (words : Fin layout.roots→Cell layout.rootBits) (rank : n.val=(fresh ptr.1 ptr.2).val)
    (enough : ((plan ptr.1).recipe hp).arity ptr.2≤layout.arguments)
    (ranges : ∀j,(spans j).val=argumentSpan (plan ptr.1) ptr.2 j.val)
    (rotated : ∀side g v (op : (prog (rootSite side g v)).Node) (row : Fin layout.roots)
      (r : Fin (b.reset.circuit side g).layers),
      ptr=⟨rootSite side g v,op⟩→(originClass b hp whole a (.inr (.inr ptr))).val=6+row.val→
      n.val/m=r.val→words row=(rotorNumber ((b.reset.circuit side g).rotation r) v:Cell layout.rootBits)) :
    let cls : Cell layout.classBits:=project typeClass ptr
    (layout.rootId cls).elim (layout.tag cls (layout.extra spans)) words=
      (role ((prog ptr.1).tag ptr.2):Cell layout.rootBits):=by
  dsimp only
  rcases ptr with ⟨⟨⟨side,g|t⟩,site⟩,op⟩
  · rcases site with ⟨v,(_|_)|i⟩
    · obtain ⟨r,slot,tag⟩:=b.reset.good_root_row key m p hp fit side g v op
      let ptr : NodeOrder.Global prog:=⟨rootSite side g v,op⟩
      let cls : Cell layout.classBits:=project typeClass ptr
      obtain ⟨id,idx⟩ : ∃id:Fin (2*(2^res*2^b.reset.n)), cls.val=6+id.val:=by
        change ∃ id : Fin _, (DescentResetActorClass.rootIndex b.reset.n res side _ v).val=6+id.val
        exact ⟨_,rfl⟩
      let row:=id.cast rootCount
      have fitRow:layout.rootId cls=some row:=by
        have off:cls.val-6=row.val:=by rw [idx];simp [row]
        have h:6≤cls.val ∧ cls.val-6<layout.roots:=⟨by omega,off.symm ▸ row.isLt⟩
        rw [DescentPrimitiveBirth.Layout.rootId,dite_eq_left h]
        exact congrArg some (Fin.ext off)
      change (layout.rootId cls).elim _ words=_
      rw [fitRow,Option.elim_some,tag]
      exact rotated side g v op row r rfl idx (rank.symm ▸ slot)
    · exact ((b.reset.good_end_empty key m p hp fit side g v).false op).elim
    · let ptr : NodeOrder.Global prog:=⟨⟨(side,.inl g),⟨v,.inr i⟩⟩,op⟩
      let cls : Cell layout.classBits:=project typeClass ptr
      have idx:cls.val=4:=smallIndex 4 _ _ (by decide)
      obtain ⟨tag,arity⟩:=b.reset.good_tap_role key m p hp fit side g v i op
      have extra:layout.extra spans≠0 ↔ ((program ptr.1).op op).arity=2:=
        (layout.another_span (rec:=(program ptr.1).recipe) (plan ptr.1) op hp spans enough ranges).trans
          (DescentResetMetadataInputs.ofProgram_two _ (b.reset.laneWidth_eq m p fit ptr.1) hp (program ptr.1) op arity)
      change (layout.rootId cls).elim (layout.tag cls (layout.extra spans)) words=_
      rw [tag]
      by_cases active:layout.extra spans=0
      · have one:((program ptr.1).op op).arity≠2:=fun h=>(extra.mpr h) active
        dsimp only [ptr] at one
        simp [DescentPrimitiveBirth.Layout.rootId,DescentPrimitiveBirth.Layout.tag,idx,active,one]
      · have two:=extra.mp active
        dsimp only [ptr] at two
        simp [DescentPrimitiveBirth.Layout.rootId,DescentPrimitiveBirth.Layout.tag,idx,active,two]
  · let ptr : NodeOrder.Global prog:=⟨⟨(side,.inr t),site⟩,op⟩
    let cls : Cell layout.classBits:=project typeClass ptr
    have idx:cls.val=5:=smallIndex 5 _ _ (by decide)
    have tag:role ((prog ptr.1).tag op)=5:=(b.reset.fallback_role key m p hp fit side t site op).1
    change (layout.rootId cls).elim (layout.tag cls (layout.extra spans)) words=(role ((prog ptr.1).tag op):_)
    simp [DescentPrimitiveBirth.Layout.rootId,DescentPrimitiveBirth.Layout.tag,idx,tag]


include stored token in
/-- A zero-padded physical role word at any original output coordinate.  Its two
data dependencies are the actual previous root rotation packet and the complete F6
column at the same node, including all padded arguments. -/
theorem physical_birth_word (typeClass : layout.classBits=indexBits b.reset.n res)
    (rootCount : 2*(2^res*2^b.reset.n)=layout.roots)
    (fits : ∀v,((Y).placement.records v).length<2^layout.paidBits)
    (x : Block k) (n : Fin layout.nodes) (rack : Fin H) (group : Fin Groups)
    (spans : Fin layout.arguments→Cell layout.spanBits) (words : Fin layout.roots→Cell layout.rootBits)
    (measure : ∀atom (v : NodeOrder.Global prog),cell x n rack group=some atom→names atom=.inr (.inr v)→
      ((plan v.1).recipe hp).arity v.2≤layout.arguments ∧
      ∀j,(spans j).val=argumentSpan (plan v.1) v.2 j.val)
    (rootRead : ∀atom side g v (op : (prog (rootSite side g v)).Node) (row : Fin layout.roots)
      (r : Fin (b.reset.circuit side g).layers),cell x n rack group=some atom→
      names atom=.inr (.inr ⟨rootSite side g v,op⟩)→
      (originClass b hp whole a (.inr (.inr ⟨rootSite side g v,op⟩))).val=6+row.val→
      n.val/m=r.val→words row=(rotorNumber ((b.reset.circuit side g).rotation r) v:Cell layout.rootBits)) :
    let cls : Cell layout.classBits:=Fin.cast (congrArg (fun j : ℕ=>2^j) typeClass.symm) (actorAt rack)
    layout.raw n cls (census layout.paidBits rack group x) spans words=
      (cell x n rack group).elim 0 (fun atom=>match names atom with
        | .inl _=>0 | .inr (.inl _)=>0 | .inr (.inr v)=>(role ((prog v.1).tag v.2):Cell layout.rootBits)):=by
  dsimp only
  rw [born_at_slot b hp whole a earlier stored token layout typeClass fits]
  cases atNode:cell x n rack group with
  | none=>rfl
  | some atom=>
    simp only [Option.elim_some]
    cases origin:names atom with
    | inl old=>rfl
    | inr who=>
      rcases who with edge|v
      · rfl
      · have seat:=((whereAt_some (Y) next order x n rack group atom.1 atom.2).mp atNode).2
        have issued:=reached_node_rank b hp whole a earlier atom
        rw [origin] at issued
        have rank:n.val=(fresh v.1 v.2).val:=seat.trans issued
        obtain ⟨enough,ranges⟩:=measure atom v atNode origin
        apply physical_bank_tag b hp whole a layout typeClass rootCount v n spans words rank enough ranges
        intro side g v' op row r siteEq idx stamp
        subst v
        exact rootRead atom side g v' op row r atNode origin idx stamp

end
end Hierarchy.DescentPrimitivePalette

end OAI
