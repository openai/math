import OAI.Hierarchy.DescentReachedPointerCases
import OAI.Hierarchy.DescentOrdinaryRawOperandOrigin
import OAI.Hierarchy.DescentDatedSampledDenseTicket
import OAI.Hierarchy.DescentIssuedOperandKey
import OAI.Hierarchy.DescentReachedPointerVenue

namespace OAI
/-! The selected original private column, its true old first-use ordinal, and the reached donor rank. -/
namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
set_option quotPrecheck false
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "chart" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((chart).key he T c) (chart).hub T.k (gainExponent 20 T.Δ)
local notation "bk" => privateBooks ticket arch hp one pin sh unit
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation "source" => operandSource ticket arch
local notation "halo" => chartHalo (cap:=cap) (c:=c) chart
local notation "reaches" => chartHalo_members ticket chart
local notation "oldHidden" => fun v : (M).Site => ((baseShape v).recipe hp).UsedWord
local notation:max "srcArg" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2
  (sourceIndex ticket arch hp one pin sh unit x j)
local notation:max "sourceSite" x:arg => (source x).1
local notation "donors" => DescentBundleHistory.physicalDonor hp W arch.bit G (r).pick uni room prof sh.sites sh.edges pin whole
variable {K : ℕ} (slots : ∀ v, DescentLocalPrivateNames.Slot ((sh.sites v).recipe hp) ↪ Fin K)

private theorem hidden_of_map {α β γ : Type} {f : α → β} {a : α ⊕ γ} {h : γ}
    (mapped : a.map f id = .inr h) : a = .inr h := by
  cases a with
  | inl _ => contradiction
  | inr q => exact congrArg Sum.inr (Sum.inr.inj mapped)

private theorem original_hidden (v:(M).Site) (u:((baseShape v).recipe hp).Node)
    (j:Fin (((baseShape v).recipe hp).arity u)) (h:oldHidden v)
    (read:((baseShape v).recipe hp).operand u j=.inr h.val) :
    ∃(saved:NodeOrder.All arch.bit)(s:Fin (((sh.sites saved.1).recipe hp).arity saved.2))
      (t:((sh.sites saved.1).recipe hp).UsedWord),
      names ⟨v,u⟩=.inl saved ∧ s.val=j.val ∧
      ((sh.sites saved.1).recipe hp).operand saved.2 s=.inr t.val ∧
      donors ⟨v,h⟩=⟨saved.1,t⟩ :=by
  cases v with
  | inl v=>
    let previous:=DescentOrdinaryRawOperandOrigin.previousIndex W arch.bit G (r).pick uni room prof hp
      sh.sites sh.edges pin whole v u j
    let t:=((donors) ⟨.inl v,h⟩).2
    refine ⟨⟨v,u⟩,previous,t,rfl,rfl,?_,rfl⟩
    have seen:=((DescentOrdinaryRawOperandOrigin.raw_old_read W arch.bit G (r).pick uni room prof hp
      sh.sites sh.edges pin whole v u j).2).symm.trans read
    change (((sh.sites v).recipe hp).operand u previous).map _ id=Sum.inr h.val at seen
    have originalValue : t.val = h.val := rfl
    exact (hidden_of_map seen).trans (congrArg Sum.inr originalValue.symm)
  | inr i=>exact h.val.1.elim

private theorem raw_site (v:(M).Site) (h:oldHidden v) : v=Sum.inl ((donors) ⟨v,h⟩).1 :=by
  cases v with
  | inl v=>rfl
  | inr i=>exact h.val.1.elim

/-- A raw hidden input has an actual earlier scalar, exactly the same operand ordinal,
and the earlier positive alias tabulated on that scalar's own reached vertex. -/
theorem private_job_origin (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (h:oldHidden (sourceSite x)) (read:srcArg x j=.inr h.val) :
    ∃(saved:NodeOrder.All arch.bit)(s:Fin (((sh.sites saved.1).recipe hp).arity saved.2))
      (t:((sh.sites saved.1).recipe hp).UsedWord)
      (inside:saved.1∈(reachedHalo ticket).member (currentLabel ticket arch x.1 x.2)),
      roots ticket arch x=.inl saved ∧ s.val=j.val ∧
      ((sh.sites saved.1).recipe hp).operand saved.2 s=.inr t.val ∧
      carriedLabel ticket arch hp one pin sh unit slots (sourceSite x) h=
        Key.carried (((reachedHalo ticket).slot (currentLabel ticket arch x.1 x.2)) ⟨saved.1,inside⟩).val
          (DescentLocalPrivateNames.firstAlias ((sh.sites saved.1).recipe hp) (slots saved.1) t).val :=by
  obtain ⟨saved,s,t,origin,num,operand,mapped⟩:=original_hidden arch hp pin sh unit
    (sourceSite x) (source x).2 (sourceIndex ticket arch hp one pin sh unit x j) h read
  have link:=source_home ticket arch hp one pin sh unit x j
  let oldWord:=donors ⟨sourceSite x,h⟩
  have original:=raw_site (he:=he) (T:=T) (c:=c) arch hp pin sh unit (sourceSite x) h
  have inside:oldWord.1∈(halo).member ((bk).home x.1):=by
    rw [link,original]
    exact (reaches).2.1 oldWord.1
  have rawKey : carriedLabel ticket arch hp one pin sh unit slots (sourceSite x) h=
      Key.carried (((halo).slot ((bk).home x.1)) ⟨oldWord.1,inside⟩).val
        (DescentLocalPrivateNames.firstAlias ((sh.sites oldWord.1).recipe hp) (slots oldWord.1) oldWord.2).val :=by
    revert inside
    rw [link]
    intro inside
    rfl
  have address:=pointer_slot ticket arch hp one pin sh unit x.1 x.2 oldWord.1 inside
  have joined:=rawKey.trans (congrArg (fun d=>Key.carried (Fin.val d)
    (DescentLocalPrivateNames.firstAlias ((sh.sites oldWord.1).recipe hp) (slots oldWord.1) oldWord.2).val) address)
  change oldWord=⟨saved.1,t⟩ at mapped
  let claim (w:OccupiedWord W.graph arch.bit.recipe sh.sites hp):Prop:=
    ∃inside:w.1∈(reachedHalo ticket).member (currentLabel ticket arch x.1 x.2),
      carriedLabel ticket arch hp one pin sh unit slots (sourceSite x) h=
        Key.carried (((reachedHalo ticket).slot (currentLabel ticket arch x.1 x.2)) ⟨w.1,inside⟩).val
          (DescentLocalPrivateNames.firstAlias ((sh.sites w.1).recipe hp) (slots w.1) w.2).val
  have actual:claim oldWord:=⟨_,joined⟩
  rw [mapped] at actual
  obtain ⟨reached,eqn⟩:=actual
  exact ⟨saved,s,t,reached,((names).apply_symm_apply _).symm.trans origin,
    num.trans (sourceIndex_val ticket arch hp one pin sh unit x j),operand,eqn⟩

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
