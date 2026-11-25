import OAI.Hierarchy.TaggedWireRoleSides
import OAI.Hierarchy.TaggedWireTurnData
import OAI.Hierarchy.ProtocolRAMTurnStepOrder
import OAI.Hierarchy.ProtocolRAMTurnOperands

namespace OAI
/-! # The signed role fields at the native core occurrence and its real printed link -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnStepOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnItinerary
open ProtocolRAM.Calendar CoreRoute HistoryRoles RoleProgram
open scoped Classical

variable {h d k W attempts K : ℕ} (S : PurchaseSampler) (board : RoleProgram.Board)
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K} (B : Mount (S:=S) π place board.edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)

local notation "L" => B.matrixLayout inj pad
local notation "Count" => Fintype.card (Slots h d k)
local notation "Source" => ProtocolRAMTurnGeometry.Source board.edges h d k

/-- The sorted role bank's first site is the chord's first site for either
raw endpoint enumeration (including the emitter's reverse convention). -/
theorem printed_tail (p : Bool→Public S h W k attempts) (e : Chord (siteLast h (2^W) k+1))
    (matchEnds : (name (HistoryRoles.site S (p false))=e.1.1 ∧ name (HistoryRoles.site S (p true))=e.1.2) ∨
      (name (HistoryRoles.site S (p false))=e.1.2 ∧ name (HistoryRoles.site S (p true))=e.1.1)) :
    ProtocolRAMTurnOperands.printed S true p false true=e.1.1.val := by
  rcases matchEnds with ⟨f,g⟩|⟨f,g⟩
  · have yes : name (HistoryRoles.site S (p false))<name (HistoryRoles.site S (p true)) := by
      simpa only [f,g] using e.property
    change (name (HistoryRoles.site S (p (if name (HistoryRoles.site S (p false)) <
      name (HistoryRoles.site S (p true)) then false else !false)))).val = _
    rw [ite_eq_left yes]
    exact congrArg Fin.val f
  · have no : ¬ name (HistoryRoles.site S (p false))<name (HistoryRoles.site S (p true)) := by
      simpa only [f,g] using (not_lt.mpr e.property.le)
    change (name (HistoryRoles.site S (p (if name (HistoryRoles.site S (p false)) <
      name (HistoryRoles.site S (p true)) then false else !false)))).val = _
    rw [ite_eq_right no]
    exact congrArg Fin.val g

theorem step_count (s : Source) : ((L).steps s).length=ProtocolRAMTurnGeometry.length s := by
  rcases s with e|i|c
  · rfl
  · change (oriented _ _ (B.ordinary i)).length=_
    unfold oriented
    split <;> simpa only [List.length_reverse] using ProtocolRAMTurnGeometry.length_ordinary B i
  · change (oriented _ _ (B.centers c)).length=_
    unfold oriented
    split <;> simpa only [List.length_reverse] using ProtocolRAMTurnGeometry.length_center B c

/-- The old item may be any physical numbering of the original sources. The
chronological slot, including a repeated occurrence of an edge, is recovered
by the actual native order. All three printed arrays are read at that edge. -/
theorem native_roles
    (items : Fin board.old→Source) (i : Fin board.old)
    (old : Fin board.old→Bool→Public S h W k attempts)
    (new : Fin board.edges→Bool→Public S h W k attempts) (width : Fin (board.edges+Count)→ℕ)
    (sp : Spine (rowGraph (L).edge) ((L).original (items i)).1.1 ((L).steps (items i)) ((L).original (items i)).1.2)
    (j : Fin (((L).steps (items i)).length+1)) (t : Turn)
    (it : t.item=i.val) (orig : t.origin=ProtocolRAMTurnGeometry.origin o (items i))
    (len : t.length=ProtocolRAMTurnGeometry.length (items i))
    (rev : t.reverse=reverse B inj pad (items i)) (pos : t.position=j.val) (loc : t.site=(sp.visit j).val)
    (physical : ∀q : Fin (((L).steps (items i)).length),let e:=((L).steps (items i)).get q
      ProtocolRAMTurnOperands.printed S true (new e) false true=((L).edge e).1.1.val) :
    let val := ProtocolRAMTurnOperands.values S board old new ((L).nativeEdge (enum B o)) width
    let ref := refRole ((L).steps ∘ items) (fun a b=>ProtocolRAMTurnOperands.printed S false (old a) b false)
      (fun a b=>ProtocolRAMTurnOperands.printed S true (new a) b false) i
    t.role val false=ref (sp.sides (.inl false) (.inl true) 0 j).1 ∧
      t.role val true=ref (sp.sides (.inl false) (.inl true) 0 j).2 := by
  intro val ref
  let adr := address B inj pad o (items i)
  have count := step_count S board B inj pad (items i)
  have actualLen : t.length=((L).steps (items i)).length := len.trans count.symm
  refine Spine.role_sides sp (fun e=>((L).edge e).property.ne) (.inl false) (.inl true) 0 j ref t val
    actualLen pos loc ?_ ?_ (fun q=>(adr q).val) (fun _=>false) ?_ ?_ ?_
  · simp [val,ref,it,ProtocolRAMTurnOperands.values,ProtocolRAMTurnOperands.total,i.isLt,refRole]
  · simp [val,ref,it,ProtocolRAMTurnOperands.values,ProtocolRAMTurnOperands.total,i.isLt,refRole]
  · intro q qeq
    dsimp only [adr]
    rw [previous t q.val (by rw [pos,←qeq];rfl) (q.isLt.trans_le actualLen.ge),
      orig,len,rev,address_val]
  · intro q qeq
    dsimp only [adr]
    rw [next t q.val (by rw [pos,←qeq];rfl) (q.isLt.trans_le actualLen.ge),
      orig,len,rev,address_val]
  · intro q
    let e := ((L).steps (items i)).get q
    have key : val.edge (adr q).val=e.val := by
      simpa only [val,ProtocolRAMTurnOperands.values,ProtocolRAMTurnOperands.total,
        dite_eq_left (adr q).isLt] using congrArg Fin.val (actual_edge B inj pad o (items i) q)
    simp only [key,Nat.zero_add,Bool.not_false]
    simp only [val,ProtocolRAMTurnOperands.values,ProtocolRAMTurnOperands.total,dite_eq_left e.isLt,
      ref,refRole,Function.comp_apply,dite_eq_left q.isLt]
    exact ⟨physical q,rfl,rfl⟩

end Hierarchy.ProtocolRAMTurnStepOrder

end
end OAI
