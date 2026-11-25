import OAI.Hierarchy.DescentRetainedMovedHeaders
import OAI.Hierarchy.DescentPhysicalRetainedCableRows
import OAI.Hierarchy.DescentResetRetainedNames

namespace OAI
/-! # The original node, donor and signed slot observed by the native retained operand -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentOperandStateBanks DescentKernelHistory DescentLocalPrivateNames DescentSIMDLookup DescentPackedZip DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
variable (which : C.seven.control.Targets) (X : C.seven.Packets) (panels : C.retained.Strips)
variable (t : Fin C.placement.shapes) (h : Fin C.retained.hosts) (g : Fin C.retained.grouped)
local notation "accept" => ownerAt C which X t h g
local notation "prior" => priorAt C X h g
local notation "before" => (L).site panels h g
local notation "out" => (L).routedWord accept prior before


/-- The sorting used to compact old nodes is undone in the donor register.
Its one-based digit is the original donor of the previously occupied node. -/
theorem decoded_original_donor (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (d : Fin (L).donors)
    (n : Fin (L).previousNodes) (active : accept d=true)
    (valid : n.val<(L).originalCount before d) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset out (order d)+n.val) (fits : (L).donors<2^(L).bits) :
    (C.seven.decoded which X panels ((L).donorID slot) t h g).val=d.val+1:=by
  have socket : C.seven.roster which X t h g=vector accept prior:=rfl
  have word_ : (L).site (C.seven.stripes which X panels t) h g=out:=by
    unfold DescentResetRetainedSetup.Layout.site DescentRetainedSeven.Chart.stripes
    simp only [socket]
    exact joined _ _ _ order rank _
  have occupied : n.val<(L).originalCount out (order d):=by
    simpa only [(L).routed_count accept prior order rank before d,active,ite_true] using valid
  have picked : ((L).donorDigit out slot.val).val=(order d).val+1:=by
    rw [number];exact (L).donor_read out _ _ occupied fits
  have unrank:=at_source accept prior order rank d
  simp only [active,ite_true] at unrank
  have index : (finSumFinEquiv.symm ((L).donorID slot) :
      Fin ((2*7*(L).args)*(L).nodes) ⊕ Fin (L).nodes) = .inr slot :=
    finSumFinEquiv.symm_apply_apply _
  unfold DescentRetainedSeven.Chart.decoded DescentResetRetainedSetup.Layout.function
  erw [index]
  change (C.seven.control.original ((L).donorDigit ((L).site (C.seven.stripes which X panels t) h g) slot.val)
     (C.seven.roster which X t h g)).val = d.val+1
  rw [word_,socket]
  unfold DescentRetainedControl.Layout.original
  have live : 0 < ((L).donorDigit out slot.val).val ∧ ((L).donorDigit out slot.val).val ≤ (L).donors := by
    rw [picked]
    exact ⟨Nat.zero_lt_succ _,Nat.succ_le_of_lt (order d).isLt⟩
  erw [dite_eq_left live]
  have atIndex : (⟨((L).donorDigit out slot.val).val-1,by omega⟩ : Fin (L).donors) = order d :=
    Fin.ext (by change ((L).donorDigit out slot.val).val-1=(order d).val; rw [picked,Nat.add_sub_cancel])
  erw [atIndex,unrank]
  exact Fin.val_cast_of_lt ((Nat.succ_le_of_lt d.isLt).trans_lt fits)

section PhysicalWord
variable {w U : ℕ} (base : ℕ) (s : C.Sources) (name : Fin U→Fin C.placement.sparse) (memory : Memory w)
variable (host : C.placement.oldHosts=C.retained.hosts) (group : C.placement.groups*C.placement.blocks=C.retained.grouped)
variable (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
local notation "Y" => fun z : Fin ((L).outputs*C.placement.shapes) =>
  let pair:=finProdFinEquiv.symm z
  reindexed host group (C.seven.decoded s.which X panels pair.1 pair.2)
variable (block : Fin C.placement.blocks) (rack : Fin C.placement.newHosts) (group_ : Fin C.placement.groups)
variable (alive : rack.val<U)
local notation "sparse" => name ⟨rack.val,alive⟩
local notation "shp" => C.placement.shape sparse
local notation "prev" => (C.placement.previous sparse).cast host
local notation "coordinate" => (finProdFinEquiv (group_,block)).cast group
local notation "take_" => ownerAt C s.which X shp prev coordinate
local notation "prior_" => priorAt C X prev coordinate
local notation "original" => (L).site panels prev coordinate
local notation "restored" => (L).routedWord take_ prior_ original


local notation "oldWord" i => DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y i block
local notation "retSpace" => Fin C.placement.newHosts→Fin C.placement.groups→Cell C.fieldBits
variable (hub : Fin C.placement.newHosts → Fin C.placement.groups → Cell C.fieldBits)
  (fee : Fin C.strip → Fin C.placement.newHosts → Fin C.placement.groups → Cell C.fieldBits)
local notation "carried" operand:max slot:max => C.carriedRow s name Y signed block operand slot hub fee rack group_

private theorem compact_original (o : Fin (L).outputs) (primary : s.primary shp=true) :
    (oldWord o) rack group_=C.seven.decoded s.which X panels o shp prev coordinate:=by
  simp only [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,
    alive,dite_eq_left,DescentRetainedTargetPlacement.Chart.selected,primary,reindexed]
  erw [ite_true,finProdFinEquiv.symm_apply_apply]
  rfl

/-- These five observed digits come from the old node and its original donor on
the actual compacted receiver. This includes the original pointer's chunk. -/
theorem carried_origin_fields (primary : s.primary shp=true) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior_ d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (arg : Fin (L).previousArgs) (active : take_ d=true) (valid : n.val<(L).originalCount original d)
    (present : arg.val<((L).entry original d n (L).arityField).val) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset restored (order d)+n.val)
    (operand : Fin (L).args) (same : operand.val=arg.val)
    (fits : (L).donors<2^(L).bits) (wide : (L).bits≤C.fieldBits) :
    (∀f:Fin 4,(C.cable.header (carried operand slot) f).val=
      ((L).entry original d n ((L).operandField ⟨f.val,f.isLt.trans (by decide)⟩ arg)).val) ∧
      (C.cable.donorCell (carried operand slot)).val=d.val+1:=by
  have space : 2^(L).bits≤2^C.fieldBits:=Nat.pow_le_pow_right (by decide) wide
  constructor
  · intro f
    let field : Fin 7:=⟨f.val,f.isLt.trans (by decide)⟩
    let o:=(L).outputID 0 field operand slot
    simp only [DescentResetRetainedCableLaw.Shape.header,DescentResetOperandSetup.Chart.carriedRow,dite_eq_left f.isLt]
    have p:=(compact_original C X panels s name host group block rack group_ alive o primary).trans
      (decoded_moved_field C s.which X panels shp prev coordinate 0 order rank d n arg active valid present slot number operand same field)
    simp only [Fin.val_zero,true_or,ite_true] at p
    change (((((oldWord o) rack group_).val:ℕ):Cell C.fieldBits)).val=_
    rw [p,Fin.val_cast_of_lt (((L).entry original d n ((L).operandField field arg)).isLt.trans_le space)]
  · have p:=congrArg Fin.val (compact_original C X panels s name host group block rack group_ alive ((L).donorID slot) primary)
    have source:=decoded_original_donor C s.which X panels shp prev coordinate order rank d n active valid slot number fits
    simp only [DescentResetRetainedCableLaw.Shape.donorCell,DescentResetOperandSetup.Chart.carriedRow,
      show ¬(4<4) by decide]
    change (((((oldWord ((L).donorID slot)) rack group_).val:ℕ):Cell C.fieldBits)).val=_
    rw [Fin.val_cast_of_lt (((oldWord ((L).donorID slot)) rack group_).isLt.trans_le space)]
    exact p.trans source


/-- The signed row and ticket are indexed by the *original* donor in both
arrays. These are the cells passed to the actually executed carried lookup. -/
theorem carried_faces_wide (node : Fin (L).nodes) (arg : Fin (L).args)
    (d : Fin (L).donors) (j : Fin (2*C.oldCap))
    (small : (signed (finProdFinEquiv (d,j)) (C.placement.previous (name ⟨rack.val,alive⟩))
      (finProdFinEquiv (group_,block))).val<2^C.fieldBits) :
    let k:=finProdFinEquiv (d,j)
    let actor:=name ⟨rack.val,alive⟩
    C.cable.row (carried arg node) d j=
      ((signed k (C.placement.previous actor) (finProdFinEquiv (group_,block))).val:
        Cell (DescentSignedCableCodec.width C.oldDegree C.oldCap)) ∧
    C.cable.ticket (carried arg node) d j=(fee k rack group_).val ∧
    C.cable.hubCell (carried arg node)=hub rack group_:=by
  intro k actor
  have short : 6+k.val<6+C.strip:=Nat.add_lt_add_left k.isLt _
  have hi : 6≤6+k.val:=Nat.le_add_right ..
  have second : 6+C.strip≤6+C.strip+k.val:=Nat.le_add_right ..
  have bank : (C.placement.compact C.signedFields (fun _=>true) name signed k block) rack group_=
      signed k (C.placement.previous actor) (finProdFinEquiv (group_,block)):=by
    simp only [DescentResetRetainedPlacement.Chart.compact,DescentResetDenseOperand.dense,alive,
      dite_eq_left,DescentResetRetainedPlacement.Chart.selected,actor]
    erw [ite_true]
  have first : (carried arg node) (C.cable.laneIndex false d j)=
      ((signed k (C.placement.previous actor) (finProdFinEquiv (group_,block))).val:Cell C.fieldBits):=by
    unfold DescentResetRetainedCableLaw.Shape.laneIndex DescentResetOperandSetup.Chart.carriedRow
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
    change (if a:6+k.val<4 then _ else if b:6+k.val=4 then _ else if c:6+k.val=5 then _ else
      if a:6+k.val<6+C.strip then _ else _)=_
    simp only [show ¬6+k.val<4 by omega,show ¬6+k.val=4 by omega,show ¬6+k.val=5 by omega,
      dite_eq_left short,Nat.add_sub_cancel_left]
    repeat' erw [dite_false]
    exact congrArg (fun x : Cell C.signedBits => (x.val : Cell C.fieldBits)) bank
  refine ⟨?_,?_,?_⟩
  · unfold DescentResetRetainedCableLaw.Shape.row
    rw [first,Fin.val_cast_of_lt small]
    rfl
  · unfold DescentResetRetainedCableLaw.Shape.ticket DescentResetRetainedCableLaw.Shape.laneIndex DescentResetOperandSetup.Chart.carriedRow
    simp only [ite_true]
    change ((if a:6+C.strip+k.val<4 then _ else if b:6+C.strip+k.val=4 then _ else if c:6+C.strip+k.val=5 then _ else
      if a:6+C.strip+k.val<6+C.strip then _ else _):Cell C.fieldBits).val=_
    simp only [show ¬6+C.strip+k.val<4 by omega,show ¬6+C.strip+k.val=4 by omega,show ¬6+C.strip+k.val=5 by omega,
      Nat.not_lt_of_ge second]
    repeat' erw [dite_false]
    apply congrArg (fun a : Fin C.strip => (fee a rack group_).val)
    apply Fin.ext
    change (6+C.strip+k.val)-(6+C.strip)=k.val
    omega
  · simp [DescentResetRetainedCableLaw.Shape.hubCell,DescentResetOperandSetup.Chart.carriedRow]
    rfl

theorem carried_faces (node : Fin (L).nodes) (arg : Fin (L).args)
    (d : Fin (L).donors) (j : Fin (2*C.oldCap))
    (width : C.signedBits=DescentSignedCableCodec.width C.oldDegree C.oldCap) (wide : C.signedBits≤C.fieldBits) :
    let k:=finProdFinEquiv (d,j)
    let actor:=name ⟨rack.val,alive⟩
    HEq (C.cable.row (carried arg node) d j)
      (signed k (C.placement.previous actor) (finProdFinEquiv (group_,block))) ∧
    C.cable.ticket (carried arg node) d j=(fee k rack group_).val ∧
    C.cable.hubCell (carried arg node)=hub rack group_:=by
  intro k actor
  have small : (signed k (C.placement.previous actor) (finProdFinEquiv (group_,block))).val<2^C.fieldBits :=
    (signed k _ _).isLt.trans_le (Nat.pow_le_pow_right (by decide) wide)
  have h:=carried_faces_wide (C:=C) (X:=X) (panels:=panels) (s:=s) (name:=name)
    (host:=host) (group:=group) (signed:=signed) (hub:=hub) (fee:=fee) (block:=block) (rack:=rack) (group_:=group_) (alive:=alive) node arg d j small
  refine ⟨?_,h.2⟩
  rw [h.1]
  generalize signed k (C.placement.previous actor) (finProdFinEquiv (group_,block))=q
  change HEq ((q.val:ℕ):Cell (DescentSignedCableCodec.width C.oldDegree C.oldCap)) q
  rw [←width]
  exact heq_of_eq (Fin.ext (Fin.val_cast_of_lt q.isLt))

end PhysicalWord
end
end Hierarchy.DescentRetainedRangeDigits

end OAI
