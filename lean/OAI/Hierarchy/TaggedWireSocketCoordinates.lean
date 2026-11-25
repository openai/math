import OAI.Hierarchy.TaggedWirePaidRoleRead

namespace OAI
/-! # Both numerical halves of the physical endpoint role -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets TaggedShorterSupergroups ProtocolRAM Calendar PurchaseCT
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing

variable {w h W k attempts K R H : ℕ} (S : PurchaseSampler)

def Coordinates (dir : Directory (reserved h W (copies k attempts)) H)
    (v : Socket) (m : Memory w) (row : Word w) (x : StageColumns h (2^W) × Role k attempts) : Prop :=
  v.group.eval m row=((packed dir x).1.val:Word w) ∧ v.slot.eval m row=((packed dir x).2.val:Word w)

def Header (dir : Directory (reserved h W (copies k attempts)) H) (start : ℕ)
    (groups : Fin K≃AllGroups h (2^W)) (m : Memory w) : Prop :=
  ∀g,let j:=((groups.symm g).val:Word w)
    (ProtocolRAMSupergroupDirectory.groupBank start K).read m j=((dir.group g).val:Word w) ∧
    (ProtocolRAMSupergroupDirectory.offsetBank start K).read m j=(dir.base g:Word w)

theorem packed_coordinates (dir : Directory (reserved h W (copies k attempts)) H) (start : ℕ)
    (groups : Fin K≃AllGroups h (2^W)) (m : Memory w) (row : Word w)
    (kind global group port tag : Expr) (x : StageColumns h (2^W)×Role k attempts)
    (header : Header dir start groups m)
    (grp : group.eval m row=((groups.symm (owner x.1)).val:Word w))
    (inp : port.eval m row=((socketPort x.1).val:Word w))
    (role : tag.eval m row=((socketTag x.1 x.2).val:Word w)) :
    Coordinates dir (packedSocket start K (copies k attempts) kind global group port tag) m row x := by
  constructor
  · simp only [packedSocket,Expr.eval,grp]
    exact (header (owner x.1)).1
  · simp only [packedSocket,addressExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,eval_scale,grp,inp,role,(header (owner x.1)).2]
    change _=(((dir.base (owner x.1)+(offset x.1 x.2).val):ℕ):Word w)
    rw [offset_val]
    push_cast
    ring

theorem core_coordinates (order : Fin R≃Edges S h (2^W) k) (base freeBase bits superStart groupStart M : ℕ)
    (groups : Fin K≃AllGroups h (2^W)) (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (m : Memory w) (i : Fin R) (t : StageAt h (2^W)) (p : Fin (2^h)) (l : ColumnLayer k) (side : Bool)
    (edge : order i=.inr ((p,t),l)) (head : CoreCatalogue.Header order base attempts groupStart M m)
    (geom : CoreCatalogue.Geometry π m (2^W)) (names : ReportGroupROM.Resident groupStart groups groupNumber m)
    (rowsFit : R≤2^w) (tileFit : 2^h≤2^w) (wide : 2^bits≤2^w)
    (ctEnd : Native.heapEnd h (2^W) Native.copies≤2^bits)
    (groupEnd : groupStart+ReportGroupROM.words h (2^W)≤2^bits) (super : Header dir superStart groups m) :
    Coordinates dir (coreInputs base freeBase R bits superStart K k attempts side) m (i.val:Word w)
      (locate S π depth marks unique (.inl ((t,p),l),side)) := by
  obtain ⟨grp,input,output,tagL,tagR⟩:=CoreCatalogue.operands order base bits attempts groupStart M groups π m
    head geom names rowsFit tileFit wide ctEnd groupEnd i t p l edge
  cases side
  · apply packed_coordinates dir superStart groups m _ _ _ _ _ _ _ super grp input tagL
  · apply packed_coordinates dir superStart groups m _ _ _ _ _ _ _ super grp output tagR

open ProbeStage.Native PurchaseFrozen in
theorem bought_coordinates (v : BoughtSockets.Directory attempts) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (groups : Fin K≃AllGroups h (2^W)) (num : ReportGroupROM.Numbering h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (m : Shelf.Mem h (2^W))
    (e : Bought S π depth marks) (side : Bool)
    (data : (v.shelf e.1).PortData S π depth (BoughtLocation.keyOf e.2) m)
    (ct : BoughtSockets.numberLoaded num π m) (remap : ReportGroupROM.Resident v.remapBase groups num m)
    (header : (v.header h (2^W) k S.degree depth).Loaded m)
    (keys : (StripDirectory.stratumHeader h (2^W) k S.degree depth v.keysBase).Loaded m)
    (super : Header dir v.superBase groups m)
    (attemptRoom : attempts≤2^wordBits h (2^W) Native.copies)
    (keyRoom : count h (2^W) k≤2^wordBits h (2^W) Native.copies)
    (tiles : (depth+1)*paths h S.degree depth≤2^wordBits h (2^W) Native.copies) :
    let i := (v.header h (2^W) k S.degree depth).enum ⟨e.1,BoughtLocation.relative e.2⟩
    Coordinates dir (boughtInputs v S h W k depth K side) m (i.val:Word _)
      (locate S π depth marks unique (.inr e,side)) := by
  have endpoint:=BoughtSockets.retained v.remapBase v.keysBase (v.shelf e.1) S π depth marks unique e.1 e.2
    groups num m ct remap data tiles keyRoom keys (BoughtLocation.localIndex e.2) (BoughtLocation.rows e.2) side
  have fields:=v.fields_read S depth m groups e.1 (BoughtLocation.relative e.2) side _ header attemptRoom endpoint
  exact packed_coordinates dir v.superBase groups m _ _ _ _ _ _ _ super fields.group fields.port fields.tag

theorem paid_coordinates_core (b : CatalogueRows.Board) (dir : Directory (reserved h W (copies k attempts)) H)
    (core bought : Bool→Socket) (m : Memory w) (r : Fin b.coreRows) (side : Bool) (x : StageColumns h (2^W) × Role k attempts)
    (fits : b.rows<2^w) (atRow : Coordinates dir (core side) m (r.val:Word w) x) :
    Coordinates dir (paidInputs b core bought side) m ((b.coreIndex r).val:Word w) x :=
  ⟨(b.select_core m _ _ r fits).trans atRow.1,(b.select_core m _ _ r fits).trans atRow.2⟩

theorem paid_coordinates_bought (b : CatalogueRows.Board) (dir : Directory (reserved h W (copies k attempts)) H)
    (core bought : Bool→Socket) (m : Memory w) (r : Fin b.boughtRows) (side : Bool) (x : StageColumns h (2^W) × Role k attempts)
    (fits : b.rows<2^w) (atRow : Coordinates dir (bought side) m (r.val:Word w) x) :
    Coordinates dir (paidInputs b core bought side) m ((b.boughtIndex r).val:Word w) x :=
  ⟨(b.select_bought m _ _ r fits).trans atRow.1,(b.select_bought m _ _ r fits).trans atRow.2⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
