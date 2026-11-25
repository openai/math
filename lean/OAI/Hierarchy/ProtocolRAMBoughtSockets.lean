import OAI.Hierarchy.ProtocolRAMStripColumnInputs
import OAI.Hierarchy.ProbePurchasedOccurrence
import OAI.Hierarchy.ProbeReportPlacement
import OAI.Hierarchy.ProtocolRAMReportGroupROM

namespace OAI
/-! # Source and target socket words for the actual purchased chains -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT ReportSockets
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {z d W k attempts K w : ℕ}

def position (depth : ℕ) : Bool → Fin (depth+1)
  | false => 0
  | true => Fin.last depth

/-- The zero-th row names the common group. A source uses its initial input
port, and a target uses its last output port. The two lookup addresses come
from the physically traversed DFS candidate, including when depth is zero. -/
def keyFields (groupBase : ℕ) (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k)
    (a : Fin attempts) (side : Bool) : Inputs :=
  let t := stage i
  let ct := banks t
  ⟨.lookup (ReportGroupROM.bank groupBase z d t) (.lookup ct.group (readTile sh S depth i 0)),
    .lookup (if side then ct.output else ct.input) (readTile sh S depth i (position depth side)),
    .lit ((Fintype.equivFin (Bool × Role k attempts)) (side,Sum.inr a)).val⟩

def event (groupBase keyBase : ℕ) (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ)
    (a : Fin attempts) (side : Bool) : Inputs :=
  let header:=StripDirectory.stratumHeader z d k S.degree depth keyBase
  let fields:=fun i : Key z d k=>keyFields groupBase sh S depth i a side
  ⟨select header (fun i=>(fields i).group),select header (fun i=>(fields i).port),
    .lit ((Fintype.equivFin (Bool × Role k attempts)) (side,Sum.inr a)).val⟩

def numberLoaded (num : ReportGroupROM.Numbering z d) (π : Equiv.Perm (Fin (2^z))) (m : Shelf.Mem z d) :=
  ∀ t : StageAt z d,Native.Resident (banks t).group m (fun r => (num t ((advisedStage z d π t).group r)).val)

theorem read_tile (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (i : Key z d k) (m : Shelf.Mem z d) (data : sh.PortData S π depth i m)
    (room : (depth+1)*paths z S.degree depth≤2^wordBits z d Native.copies)
    (r : PurchaseDirectory.Index (2^z) S.degree depth) (j : Fin (depth+1)) :
    (readTile sh S depth i j).eval m (r.val:Word (wordBits z d Native.copies))=
      ((Shelf.pathRows S π depth i r j).val:Word (wordBits z d Native.copies)) := by
  unfold readTile
  rw [show paths z S.degree depth=(PurchaseDFS.layout (2^z) S.degree depth).length by simp [paths]]
  apply StripDirectory.tile_read _ _ _ data.tiles _ _ r j
  · exact (ProtocolRAMPurchaseSampler.lt_span _).le
  · simpa [paths] using room

theorem local_read (groupBase : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (i : Key z d k) (a : Fin attempts) (side : Bool) (m : Shelf.Mem z d)
    (groups : Fin K ≃ AllGroups z d) (num : ReportGroupROM.Numbering z d)
    (geo : numberLoaded num π m) (rom : ReportGroupROM.Resident groupBase groups num m)
    (data : sh.PortData S π depth i m) (room : (depth+1)*paths z S.degree depth≤2^wordBits z d Native.copies)
    (r : PurchaseDirectory.Index (2^z) S.degree depth) (first chosen : Fin (2^z))
    (start : Shelf.pathRows S π depth i r 0=first.castSucc)
    (last : Shelf.pathRows S π depth i r (position depth side)=chosen.castSucc) :
    let t:=stage i; let p:=advisedStage z d π t; let fields:=keyFields groupBase sh S depth i a side
    let ρ:Word (wordBits z d Native.copies):=r.val
    fields.group.eval m ρ=((groups.symm ⟨t,p.group first⟩).val:Word _) ∧
      fields.port.eval m ρ=((if side then p.output chosen else p.input chosen).val:Word _) ∧
      fields.tag.eval m ρ=(((Fintype.equivFin (Bool × Role k attempts)) (side,Sum.inr a)).val:Word _) := by
  have initial := read_tile sh S π depth i m data room r 0
  have terminal := read_tile sh S π depth i m data room r (position depth side)
  rw [start] at initial
  rw [last] at terminal
  refine ⟨?_,?_,rfl⟩
  · simp only [keyFields,Expr.eval,initial,Fin.val_castSucc,geo (stage i) first]
    exact rom (stage i) ((advisedStage z d π (stage i)).group first)
  · cases side <;> simp only [keyFields,Expr.eval,terminal,Fin.val_castSucc,Bool.false_eq_true,ite_false,
      ite_true,data.inputSocket chosen,data.outputSocket chosen]

theorem event_read (groupBase keyBase : ℕ) (sh : Shelf) (S : PurchaseSampler) (depth : ℕ)
    (a : Fin attempts) (side : Bool) (m : Memory w) (i : Key z d k) (r : Fin (paths z S.degree depth))
    (keys : count z d k≤2^w) (loaded : (StripDirectory.stratumHeader z d k S.degree depth keyBase).Loaded m) :
    let header:=StripDirectory.stratumHeader z d k S.degree depth keyBase
    let ρ:Word w:=(header.enum ⟨i,r⟩).val; let x:Word w:=r.val
    let f:=event groupBase keyBase sh S z d k depth a side; let b:=keyFields groupBase sh S depth i a side
    f.group.eval m ρ=b.group.eval m x ∧ f.port.eval m ρ=b.port.eval m x ∧ f.tag.eval m ρ=b.tag.eval m x := by
  let header:=StripDirectory.stratumHeader z d k S.degree depth keyBase
  have split:=StripDirectory.header_pair header m loaded i r
  have small : i.val<2^w := i.isLt.trans_le keys
  have key : (header.ballTerm.eval m ((header.enum ⟨i,r⟩).val:Word w)).val=i.val := by
    rw [split.1,Fin.val_cast_of_lt small]
  exact ⟨select_read header _ m _ _ i keys key split.2,select_read header _ m _ _ i keys key split.2,rfl⟩

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
