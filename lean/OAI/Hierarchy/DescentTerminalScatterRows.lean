import OAI.Hierarchy.DescentTerminalHeaderScatter
import OAI.Hierarchy.DescentTerminalExteriorHeaders
import OAI.Hierarchy.DescentTerminalSparseHeader

namespace OAI
/-! # Actual source and destination row addresses at both ends of a clipped cable -/
namespace Hierarchy.DescentTerminalScatterRows
open DescentKernelHistory hiding Word
open DescentTerminalChipSource DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalHeaderGroups DescentTerminalDenseHeader DescentTerminalDenseWindow
open DescentTerminalDenseGraphRead DescentTerminalCableOrder DescentTerminalPorts DescentTerminalPublicGroup
open Computability.BorderVNP.Crossing ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {P Tag : Type} [Fintype P] {D S p W q rawRows : ℕ} {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (hp : 0<p)
    (birth : ∀v,(r v).Node ↪ ℕ) (wp : 0<W) (qp : 0<q)
local notation "L" => order N home native p external nodes ops
local notation "sites" => DescentTerminalBundleRows.site L r hp birth
local notation "Inst" => GroupRow (q:=q) sites
local notation "gOf" => fun (a : Inst)=>(Order.groups L a.1).symm a.2.1
local notation "ipt" => DescentTerminalHeaderGroups.stream (p:=p) N home native external nodes ops q hp
local notation "ept" => DescentTerminalExteriorHeaders.stream (p:=p) (q:=q) N home native external nodes ops
local notation "idx" => DescentTerminalScalarInput.index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth
local notation "fmt" => DescentTerminalScalarInput.control N home native external nodes ops r hp birth qp
def firstLocal (a : Inst) := ProtocolRAMPortRanks.«prefix» ((sites a.1).chunks q) Fin.val a.2.1
theorem destination (a : Inst) : (rowAddress sites wp a).val=
    DescentTerminalBinPack.first W (counts (q:=q) sites) a.1+firstLocal N home native external nodes ops r hp birth a+a.2.2.val := by
  exact (Nat.add_assoc _ _ _).symm

def srcStart (a : Inst) : ℕ := match (gOf a).val with
  | some j=>(ipt (pair a.1 j)).length
  | none=>(ept a.1.val).length

theorem pref_eq {m n : ℕ} (a : Fin m→ℕ) (b : Fin n→ℕ) (eq : ∀j,lengthAt a j=lengthAt b j) (k : ℕ) :
    pref a k=pref b k := by induction k with | zero=>rfl | succ k ih=>rw [pref,pref,ih,eq]
theorem form_eq {m n : ℕ} (a : Fin m→ℕ) (b : Fin n→ℕ) (eq : ∀j,lengthAt a j=lengthAt b j)
    (ha : ∀i,a i≤p) (hb : ∀i,b i≤p) (pos:0<q*p) (base r : ℕ) :
    format a pos ha base r=format b pos hb base r := by
  funext j
  apply Prod.ext <;> apply Fin.ext
  · simp only [DescentTerminalDenseWindow.format,DescentTerminalDenseWindow.first,
      DescentTerminalDenseWindow.begin,pref_eq a b eq]
  · exact eq _

theorem positive (a : Inst) (j : Fin S) (near : (gOf a).val=some j) :
    0<pairMass N home (pair a.1 j) := by
  obtain ⟨nm,used,other⟩:=(gOf a).property
  rcases e:nm with ⟨edge,k⟩|⟨pin,k⟩
  · have both : Order.Used L a.1 (.inl ⟨edge,k⟩) ∧ Order.neighbor L a.1 (.inl ⟨edge,k⟩)=some j:=⟨e ▸ used,e ▸ other.trans near⟩
    exact (DescentTerminalSparseHeader.positive_iff N home _).2 ⟨edge,(Nat.zero_le _).trans_lt (piece_used hp k),
      (between_iff N p L a.1 j edge k).mp both⟩
  · simp [e,Order.neighbor] at other
    cases other.trans near

theorem interior {bw : ℕ} (a : Inst) (other : Fin S) (near : (gOf a).val=some other) (m : Memory bw)
    (layout : DescentTerminalDenseHeaderRAM.Layout) (limit : ℕ) (hit : pair a.1 other<limit)
    (stores : ∀(t : ℕ) (_:t<limit) (live:0<pairMass N home t),
      let g:=selected N home native external nodes ops hp t live
      ∀k : Fin (poolBatchCount (Fintype.card (Order.At L g.site g.group)) q),
        let z : DescentTerminalDenseCableFetch.Packet N L q:=⟨g.site,g.other,g.group,g.near,k⟩
        m (layout.index.base+((ipt t).length+k.val))=(DescentTerminalDenseCableFetch.index N home native external nodes ops z:Word bw) ∧
        m (layout.control.base+((ipt t).length+k.val))=((formatIndex q p (DescentTerminalDenseCableFetch.fmt N home native external nodes ops (Nat.mul_pos qp hp) z)).val:Word bw)) :
    let head:=srcStart N home native external nodes ops r hp birth a+a.2.2.val
    let name:=anchor sites qp a
    m (layout.index.base+head)=(idx name:Word bw) ∧ m (layout.control.base+head)=((formatIndex q p (fmt name)).val:Word bw) := by
  intro head name
  let g : GroupBlock N L:=⟨a.1,other,gOf a,near⟩
  have live:=positive N home native external nodes ops r hp birth a other near
  let h:=selected N home native external nodes ops hp g.tag live
  have tag : h.tag=g.tag:=selected_tag N home native external nodes ops hp g.tag live
  obtain ⟨size,atBit⟩:=DescentTerminalSparseHeader.sides N h g tag
  let k : Fin (poolBatchCount (Fintype.card (Order.At L h.site h.group)) q):=⟨a.2.2.val,by
    rw [size]
    change a.2.2.val < (sites a.1).chunks q a.2.1
    exact a.2.2.isLt⟩
  obtain ⟨index,control⟩:=stores g.tag hit live k
  have sameBase : pairBase N home h.site h.other=pairBase N home g.site g.other:=congrArg (beforePair N home) tag
  have firstEq : DescentTerminalDenseWindow.first h.lengths q (pairBase N home h.site h.other) k.val=
      DescentTerminalDenseWindow.first g.lengths q (pairBase N home g.site g.other) a.2.2.val := by
    simp only [DescentTerminalDenseWindow.first,sameBase,pref_eq h.lengths g.lengths atBit,k]
  have formatEq : DescentTerminalDenseWindow.format h.lengths (Nat.mul_pos qp hp) h.small (pairBase N home h.site h.other) k.val=
      DescentTerminalDenseWindow.format g.lengths (Nat.mul_pos qp hp) g.small (pairBase N home g.site g.other) a.2.2.val := by
    rw [sameBase]
    exact form_eq h.lengths g.lengths atBit _ _ _ _ _
  have headAt : head=(ipt g.tag).length+k.val := by
    simp only [head,srcStart,near,g,GroupBlock.tag,k]
  have idxAt : idx name=DescentTerminalDenseWindow.first g.lengths q (pairBase N home g.site g.other) a.2.2.val/(q*p) := by
    change (if (gOf a).val.isSome then 0 else rawRows+2)+
      DescentTerminalDenseWindow.first g.lengths q
        ((gOf a).val.elim (siteBase N home a.1) (pairBase N home a.1)) (a.2.2.val*q/q)/(q*p)=_
    simp [near,Nat.mul_div_cancel _ qp,g]
  have fmtAt : fmt name=DescentTerminalDenseWindow.format g.lengths (Nat.mul_pos qp hp) g.small
      (pairBase N home g.site g.other) a.2.2.val := by
    change DescentTerminalDenseWindow.format g.lengths (Nat.mul_pos qp hp) g.small
      ((gOf a).val.elim (siteBase N home a.1) (pairBase N home a.1)) (a.2.2.val*q/q)=_
    simp [near,Nat.mul_div_cancel _ qp,g]
  rw [headAt,idxAt,fmtAt,←firstEq,←formatEq]
  exact ⟨index,control⟩

theorem exterior {bw : ℕ} (a : Inst) (ext : (gOf a).val=none) (m : Memory bw) (layout : DescentTerminalDenseHeaderRAM.Layout)
    (stores : ∀(i : Fin S) (g : Order.Group L i) (_ : g.val=none) (k : Fin (poolBatchCount (Fintype.card (Order.At L i g)) q)),
      let len:=groupLengths N L i g
      let small : ∀z,len z≤p:=fun z=>by dsimp [len,groupLengths];cases ((Order.inGroup L i g).symm z).val <;> exact Nat.min_le_left ..
      m (layout.index.base+((ept i.val).length+k.val))=((DescentTerminalDenseWindow.first len q (siteBase N home i) k.val/(q*p):ℕ):Computability.VPVNP.BurstRAM.Word bw) ∧
      m (layout.control.base+((ept i.val).length+k.val))=((formatIndex q p (format len (Nat.mul_pos qp hp) small (siteBase N home i) k.val)).val:Computability.VPVNP.BurstRAM.Word bw)) :
    let head:=srcStart N home native external nodes ops r hp birth a+a.2.2.val
    let name:=anchor sites qp a
    ((rawRows+2:ℕ):Computability.VPVNP.BurstRAM.Word bw)+m (layout.index.base+head)=(idx name:Computability.VPVNP.BurstRAM.Word bw) ∧
      m (layout.control.base+head)=((formatIndex q p (fmt name)).val:Computability.VPVNP.BurstRAM.Word bw) := by
  intro head name
  obtain ⟨index,control⟩:=stores a.1 (gOf a) ext a.2.2
  have headEq : head=(ept a.1.val).length+a.2.2.val := by simp only [head,srcStart,ext]
  have groupEq : (DescentTerminalScalarInput.group N home native external nodes ops r hp birth name.2).val=none := ext
  have rowEq : DescentTerminalScalarInput.localRow (q:=q) N home native external nodes ops r hp birth name.2=a.2.2.val :=
    Nat.mul_div_cancel a.2.2.val qp
  have baseEq : DescentTerminalScalarInput.base N home native external nodes ops r hp birth name.2=siteBase N home a.1 := by
    simp only [DescentTerminalScalarInput.base,groupEq,Option.elim_none]
    rfl

  have bankEq : DescentTerminalScalarInput.bankOffset N home native external nodes ops r hp birth name.2 rawRows=rawRows+2 := by
    simp only [DescentTerminalScalarInput.bankOffset,groupEq,Option.isSome_none,Bool.false_eq_true,ite_false]
  rw [headEq]
  constructor
  · have firstAt : DescentTerminalDenseWindow.first
        (DescentTerminalScalarInput.lengths N home native external nodes ops r hp birth name.2) q
        (siteBase N home a.1) a.2.2.val =
        DescentTerminalDenseWindow.first (groupLengths N L a.1 (gOf a)) q (siteBase N home a.1) a.2.2.val := rfl
    rw [DescentTerminalScalarInput.index,bankEq,baseEq,rowEq,firstAt]
    simpa only [Nat.cast_add] using
      congrArg (fun x : Computability.VPVNP.BurstRAM.Word bw=>((rawRows+2:ℕ):Computability.VPVNP.BurstRAM.Word bw)+x) index
  · rw [DescentTerminalScalarInput.control,baseEq,rowEq]
    exact control

end
end Hierarchy.DescentTerminalScatterRows

end OAI
