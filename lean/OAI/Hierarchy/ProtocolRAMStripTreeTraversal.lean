import OAI.Hierarchy.ProtocolRAMStripNativeCost
import OAI.Hierarchy.ProtocolRAMCataloguePaidSupport
import OAI.Hierarchy.ProbeStripBroadcastTree

namespace OAI
/-! # Native broadcast over the horizontal and radial links of the real strip -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe BoughtSockets StockCommit
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical

variable {h d k n w : ℕ} {S : PurchaseSampler} {B : Type*}
local notation "Tree" => Strip.TreeLink n k
local notation "Ports" => StripPorts S h d k (Strip.TreeColumn n) (Fin n) B

def treeHeader (start rows n k : ℕ) : PortHeader := ⟨start,rows,Fintype.card (Strip.TreeLink n k)⟩

def treeTerm (p : Ports) (b : Board) (e : Tree) : Expr :=
  p.primary b (Strip.treeRole (Extra:=Empty⊕B) n k e)

/-- An invalid padded row broadcasts zero bits. Give it an in-range core
address to keep the public traversal rectangular, including dormant records. -/
def Board.treeEdge (b : Board) (term : Expr) : Expr :=
  .branch .lt term (.lit b.coreRows) term (.lit 0)

def stripTree (p : Ports) (b : Board) (start rows : ℕ) : Traversals :=
  let h:=treeHeader start rows n k
  let expr:=chooseField h.ports 0 (fun i=>((b.treeEdge (treeTerm p b ((Fintype.equivFin Tree).symm i))).atRow h.ballTerm)) h.fieldTerm
  ⟨h.count,h.owner,h.parity,expr,h.ballTerm,none⟩

/-- A physical core address supplied for a genuine tree link passes unchanged. -/
theorem Board.treeEdge_true (b : Board) (term : Expr) (m : Memory w) (r : Word w) (e : Fin b.coreRows)
    (fits : b.rows<2^w) (atEdge : (term.eval m r).val=e.val) : (b.treeEdge term).eval m r=term.eval m r := by
  have cap : b.coreRows<2^w := by unfold rows at fits;omega
  simp only [treeEdge,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt cap,atEdge,e.isLt,ite_true]

def treeTarget (p : Ports) (b : Board) (m : Memory w) (row : ℕ) (e : Tree) (pos : 0<b.coreRows) : Fin b.coreRows :=
  let t:=((treeTerm p b e).eval m (row:Word w)).val
  ⟨if t<b.coreRows then t else 0,by split <;> assumption⟩

theorem treeTarget_read (p : Ports) (b : Board) (m : Memory w) (j : ℕ) (e : Tree) (pos : 0<b.coreRows)
    (fits : b.rows<2^w) :
    ((b.treeEdge (treeTerm p b e)).eval m (j:Word w)).val=(treeTarget p b m j e pos).val := by
  have cap : b.coreRows<2^w := by unfold Board.rows at fits;omega
  simp only [Board.treeEdge,treeTarget,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt cap]
  split_ifs <;> rfl

def broadcastWalk (p : Ports) (b : Board) (m : Memory w) (j : ℕ) (pos : 0<b.coreRows) : List (Fin b.rows) :=
  List.ofFn (fun i : Fin (Fintype.card Tree)=>b.coreIndex (treeTarget p b m j ((Fintype.equivFin Tree).symm i) pos))

theorem stripTree_positions (p : Ports) (b : Board) (start rows : ℕ) :
    (stripTree p b start rows).positions=rows*(n+(n+1)*(k*2)) := by
  change rows*Fintype.card Tree=_
  rw [Strip.tree_card]

theorem stripTree_reads (p : Ports) (b : Board) (start rows : ℕ) (m : Memory w)
    (head : (treeHeader start rows n k).Loaded m) (fits : b.rows<2^w)
    (rowsFit : rows≤2^w) (linksFit : Fintype.card Tree≤2^w) (pos : 0<b.coreRows) :
    (stripTree p b start rows).Reads m (fun i : Fin rows=>broadcastWalk p b m i.val pos) := by
  let header:=treeHeader start rows n k
  let walk:=fun i : Fin rows=>broadcastWalk p b m i.val pos
  let cast : ∀i : Fin rows,Fin header.ports≃Fin (walk i).length:=fun i=>finCongr (by simp [walk,broadcastWalk,header,treeHeader])
  let enum:=header.enum.symm.trans (Equiv.sigmaCongrRight cast)
  have indexed (a : Fin header.rows) (j : Fin header.ports) :
      enum (header.enum ⟨a,j⟩) = ⟨a,cast a j⟩ := by
    change (Equiv.sigmaCongrRight cast) (header.enum.symm (header.enum ⟨a,j⟩)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨enum,?_,?_⟩
  · intro i
    obtain ⟨⟨a,j⟩,rfl⟩:=header.enum.surjective i
    let r : Word w:=(header.enum ⟨a,j⟩).val
    have pair:=StripDirectory.header_pair header m head a j
    have found := eval_chooseField header.ports 0 (fun f=>((b.treeEdge (treeTerm p b ((Fintype.equivFin Tree).symm f))).atRow header.ballTerm))
      header.fieldTerm m r j (by rw [Nat.zero_add]; exact linksFit)
      (by rw [pair.2,Fin.val_cast_of_lt (j.isLt.trans_le linksFit),Nat.zero_add])
    change ((chooseField _ _ _ _).eval m r).val=_
    rw [found,eval_atRow,pair.1,treeTarget_read p b m _ _ pos fits]
    let edgeAt (s : (a : Fin header.rows) × Fin (walk a).length) :=
      ((walk s.1)[s.2.val]'s.2.isLt).val
    refine Eq.trans ?_ (congrArg edgeAt (indexed a j)).symm
    simp [edgeAt,cast,walk,broadcastWalk,Board.coreIndex]; rfl
  · intro i
    obtain ⟨⟨a,j⟩,rfl⟩:=header.enum.surjective i
    have pair:=StripDirectory.header_pair header m head a j
    change (header.ballTerm.eval m _).val=_
    rw [pair.1,Fin.val_cast_of_lt (a.isLt.trans_le rowsFit)]
    exact (congrArg (fun s : (a : Fin header.rows) × Fin (walk a).length => s.1.val) (indexed a j)).symm

theorem stripTree_loaded (p : Ports) (b : Board) (start rows : ℕ) (m : Memory w)
    (space : (treeHeader start rows n k).stop<2^w) (wide : 0<w) :
    let h:=treeHeader start rows n k
    (stripTree p b start rows).owner=h.owner ∧ (stripTree p b start rows).parity=h.parity ∧ h.Loaded (h.load m) :=
  ⟨rfl,rfl,(treeHeader start rows n k).load_ok m wide space⟩

theorem treeTarget_true (p : Ports) (b : Board) (m : Memory w) (j : ℕ) (e : Tree) (phys : Fin b.coreRows)
    (pos : 0<b.coreRows) (read : ((treeTerm p b e).eval m (j:Word w)).val=phys.val) :
    treeTarget p b m j e pos=phys := by
  apply Fin.ext
  change (if _ then _ else 0)=_
  simp only [read,phys.isLt,ite_true]

/-- All broadcast positions, including every fallback position of a padded
inactive source, are genuine core addresses. The eligibility guard leaves each
one unchanged, as does attaching the extra catalyst radius to this traversal. -/
theorem stripTree_guard_reads (p : Ports) (b : Board) (start rows : ℕ) (m : Memory w)
    (data : Option (Expr×Expr)) (head : (treeHeader start rows n k).Loaded m) (fits : b.rows<2^w)
    (rowsFit : rows≤2^w) (linksFit : Fintype.card Tree≤2^w) (pos : 0<b.coreRows) :
    (b.guardWalk {(stripTree p b start rows) with catalystMate:=data}).Reads m (fun i : Fin rows=>broadcastWalk p b m i.val pos) := by
  have raw:=stripTree_reads p b start rows m head fits rowsFit linksFit pos
  refine ⟨raw.enum,?_,raw.ownerAt⟩
  intro i
  let entry:=raw.enum i
  let phys:=treeTarget p b m entry.1.val ((Fintype.equivFin Tree).symm
    (⟨entry.2.val,by simpa [broadcastWalk] using entry.2.isLt⟩ : Fin (Fintype.card Tree))) pos
  have hit : ((stripTree p b start rows).edge.eval m (i.val:Word w)).val=phys.val := by
    simpa [phys,entry,broadcastWalk,Board.coreIndex] using raw.edgeAt i
  have trueID:=b.checked_core (stripTree p b start rows).edge m (i.val:Word w) phys fits hit
  have range : phys.val<2^w := by have bound:=phys.isLt;unfold Board.rows at fits;omega
  change ((b.checkedEdge (stripTree p b start rows).edge).eval m _).val=_
  rw [trueID,Fin.val_cast_of_lt range,←hit]
  exact raw.edgeAt i

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
