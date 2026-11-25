import OAI.Hierarchy.TaggedWireNativeRoleSides
import OAI.Hierarchy.ProtocolRAMTurnAuthenticated
import OAI.Hierarchy.TaggedWireTerminalLive

namespace OAI
/-! # Both signed role operands read from the actual committed memory on live turns -/

noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMTurnStepOrder
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnItinerary
open ProtocolRAM.Calendar CoreRoute HistoryRoles RoleProgram
open scoped Classical

variable {h d k W attempts K w : ℕ} (S : PurchaseSampler) (board : RoleProgram.Board)
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K} (B : Mount (S:=S) π place board.edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)
local notation "L" => B.matrixLayout inj pad
local notation "P" => Public S h W k attempts
local notation "Count" => Fintype.card (Slots h d k)
local notation "Source" => ProtocolRAMTurnGeometry.Source board.edges h d k
local notation "occ" => board.edges+Count

/-- The observable is total as an integer. The representation of a
public port is required solely on its positive-width domain. -/
def liveCode {u : ℕ} (age : Bool) (width : Fin u→ℕ) (label : ∀i,0<width i→Bool→P)
    (i : Fin u) (b : Bool) := if on:0<width i then ProtocolRAMTurnOperands.printed S age (label i on) b false else 0

theorem native_live_roles
    (items : Fin board.old→Source) (i : Fin board.old)
    (old : Fin board.old→ℕ) (out : Fin board.edges→ℕ)
    (before : ∀a,0<old a→Bool→P) (after : ∀e,0<out e→Bool→P)
    (on : 0<old i) (used : ∀q : Fin (((L).steps (items i)).length),0<out (((L).steps (items i)).get q))
    (mem : Memory w) (key rank : Bank) (auth : board.LiveReads S old out before after mem)
    (stored : ∀a : Fin occ,mem (key.base+a.val)=(((L).nativeEdge (enum B o) a).val : Word w))
    (words : occ≤2^w) (keyRoom : occ≤key.size) (edges : board.edges≤2^w)
    (oldFits : ∀b,ProtocolRAMTurnOperands.printed S false (before i on) b false<2^w)
    (newFits : ∀e (pos : 0<out e) b,ProtocolRAMTurnOperands.printed S true (after e pos) b false<2^w)
    (siteFits : K≤2^w)
    (sp : Spine (rowGraph (L).edge) ((L).original (items i)).1.1 ((L).steps (items i)) ((L).original (items i)).1.2)
    (j : Fin (((L).steps (items i)).length+1)) (t : Turn)
    (it : t.item=i.val) (orig : t.origin=ProtocolRAMTurnGeometry.origin o (items i))
    (len : t.length=ProtocolRAMTurnGeometry.length (items i))
    (rev : t.reverse=reverse B inj pad (items i)) (pos : t.position=j.val) (loc : t.site=(sp.visit j).val)
    (physical : ∀q : Fin (((L).steps (items i)).length),let e:=((L).steps (items i)).get q
      ProtocolRAMTurnOperands.printed S true (after e (used q)) false true=((L).edge e).1.1.val) :
    let v:=ProtocolRAMTurnSnapshot.values (board.itinerary key rank) mem
    let ref:=refRole ((L).steps ∘ items) (liveCode S false old before) (liveCode S true out after) i
    t.role v false=ref (sp.sides (.inl false) (.inl true) 0 j).1 ∧
      t.role v true=ref (sp.sides (.inl false) (.inl true) 0 j).2 := by
  intro v ref
  let adr:=address B inj pad o (items i)
  have actualLen:=len.trans (step_count S board B inj pad (items i)).symm
  refine Spine.role_sides sp (fun e=>((L).edge e).property.ne) (.inl false) (.inl true) 0 j ref t v
    actualLen pos loc ?_ ?_ (fun q=>(adr q).val) (fun _=>false) ?_ ?_ ?_
  · simpa [v,ref,refRole,it,liveCode,on] using
      ProtocolRAMTurnSnapshot.original_role S board auth key rank i on false (oldFits false)
  · simpa [v,ref,refRole,it,liveCode,on] using
      ProtocolRAMTurnSnapshot.original_role S board auth key rank i on true (oldFits true)
  · intro q qeq
    dsimp only [adr]
    rw [previous t q.val (by rw [pos,←qeq];rfl) (q.isLt.trans_le actualLen.ge),orig,len,rev,address_val]
  · intro q qeq
    dsimp only [adr]
    rw [next t q.val (by rw [pos,←qeq];rfl) (q.isLt.trans_le actualLen.ge),orig,len,rev,address_val]
  · intro q
    let e:=((L).steps (items i)).get q
    have live : 0<out e:=used q
    have atKey:=ProtocolRAMTurnSnapshot.key_at board key rank (adr q) _ mem words keyRoom edges (stored (adr q))
    have hit : v.edge (adr q).val=e.val:=atKey.trans (congrArg Fin.val (actual_edge B inj pad o (items i) q))
    have bound : ProtocolRAMTurnOperands.printed S true (after e live) false true<2^w :=
      (physical q).trans_lt (((L).edge e).1.1.isLt.trans_le siteFits)
    have tail:=ProtocolRAMTurnSnapshot.reported_site S board auth key rank e live bound
    have low:=ProtocolRAMTurnSnapshot.reported_role S board auth key rank e live false (newFits e live false)
    have high:=ProtocolRAMTurnSnapshot.reported_role S board auth key rank e live true (newFits e live true)
    have readCode (side : Bool) : liveCode S true out after e side =
        ProtocolRAMTurnOperands.printed S true (after e live) side false := by
      unfold liveCode
      rw [dite_eq_left live]
    rw [hit]
    refine ⟨tail.trans (physical q),?_⟩
    simp only [ref,refRole,Nat.zero_add,Function.comp_apply,dite_eq_left q.isLt,Bool.not_false]
    exact ⟨low.trans (readCode false).symm,high.trans (readCode true).symm⟩

end Hierarchy.ProtocolRAMTurnStepOrder

namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Tagged WireTelescope
open scoped Classical
variable {h d k w R M den : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)

/-- The discharged `used` premise of the live role decoder in the original
public source numbering, including a fixed bundle or a repeated paid edge. -/
theorem named_live_uses_positive (z : ProtocolRAMTurnGeometry.Source Z.edges h d k)
    (positive : 0<SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used z) :
    ∀q : Fin ((L).steps z).length,0<(Z.rows (((L).steps z).get q)).width := by
  obtain ⟨i,rfl⟩:=SettledMatrix.Layout.numbered.surjective z
  exact fun q=>Z.live_uses_positive i q positive

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
