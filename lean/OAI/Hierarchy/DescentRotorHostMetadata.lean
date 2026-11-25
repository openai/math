import OAI.Hierarchy.DescentRotorWindowArchive
import OAI.Hierarchy.DescentGroupPeerOrder

namespace OAI
/-! # Short rotor reservation operands indexed by the real predecessor host roster -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentGroupPeerOrder DescentGL DescentColonies DescentSIMDLookup DescentShortReservationPeer DescentChosenRouter
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "hs" => hostRoster A ids
local notation "r" => Z.k-T.commonDepth
local notation "Y" => (2^Z.n:ℕ)
local notation "book" => T.columns

def peerData (v : V) (query across : Fin A.degree) (fieldIndex : Fin 6) : Cell a :=
  match hs v query,hs v across with
  | some dest,some u=>
    let box:=DescentShortReservationPeer.compare (2^r) (vertex u).val (vertex dest).val
    (![Z.placement.b (frm.host u)-T.commonDepth,
      min (T.columns.size (frm.host v) (frm.host u)) Y,box.first,box.second,box.less.toNat,box.same.toNat] fieldIndex:ℕ)
  | _,_=>0

variable (f B wire K : ℕ) (traffic : V→V→Block m→ℕ) (weight : V→Block m→ℕ)
variable (roster : ResetInput.SourceFrame.Roster Z T (fun u : W.graph.Site => (A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g frm (vertex.trans Fin.valEmbedding) A.near Z.n f B wire K (fun v z i=>(traffic v z i:ℝ)) A.degree weight)

def previousPeers (v : V) : T.columns.near (frm.host v)↪Fin A.degree where
  toFun p:=hostSlot A ids v ⟨frm.host.symm p.val,(roster.2.1 v (frm.host.symm p.val)).mp (by simp)⟩
  inj':=by
    intro p t same
    apply Subtype.ext
    apply frm.host.symm.injective
    exact congrArg Subtype.val ((hostSlot A ids v).injective same)

local notation "slots" => previousPeers A S ready digits Z T frm vertex f B wire K traffic weight roster

theorem previousPeers_read (v : V) (u : T.columns.near (frm.host v)) :
    hs v (slots v u)=some (frm.host.symm u.val) := at_host A ids v _

theorem previousPeers_empty (v : V) (j : Fin A.degree) (ghost : ∀u : T.columns.near (frm.host v),slots v u≠j) :
    hs v j=none := by
  unfold hostRoster
  split
  · rename_i live
    let z:=live.choose
    let u : T.columns.near (frm.host v):=⟨frm.host z.val,(roster.2.1 v z.val).mpr z.property⟩
    have point : slots v u=hostSlot A ids v z := by
      apply congrArg (hostSlot A ids v)
      exact Subtype.ext (frm.host.symm_apply_apply _)
    exact (ghost u (point.trans live.choose_spec)).elim
  · rfl

theorem peerData_read (v : V) (dest : V) (p : Fin A.degree) (arrived : hs v p=some dest)
    (u : T.columns.near (frm.host v)) (fieldIndex : Fin 6) (room : max (max r Y) (2^r)<2^a) :
    (peerData (a:=a) A S ready digits Z T frm vertex v p (slots v u) fieldIndex).val=
      let box:=DescentShortReservationPeer.compare (2^r) (T.columns.host u.val) (T.columns.host (frm.host dest))
      ![Z.placement.b u.val-T.commonDepth,min (T.columns.size (frm.host v) u.val) Y,
        box.first,box.second,box.less.toNat,box.same.toNat] fieldIndex := by
  have head:=roster.1 (frm.host.symm u.val)
  rw [frm.host.apply_symm_apply] at head
  simp only [peerData,arrived,previousPeers_read,frm.host.apply_symm_apply,head,roster.1]
  let box:=DescentShortReservationPeer.compare (2^r) (ids (frm.host.symm u.val)) (ids dest)
  have depth:Z.placement.b u.val-T.commonDepth≤r:=Nat.sub_le_sub_right (Z.placement.depth _) _
  have width : min (T.columns.size (frm.host v) u.val) Y≤Y:=min_le_right _ _
  have l : box.first≤2^r:=min_le_right _ _
  have b : box.second≤2^r:=min_le_right _ _
  have one : 0<2^r:=Nat.two_pow_pos _
  have bl (z : Bool) : z.toNat≤1:=by cases z <;> decide
  have depthRoom : r < 2^a := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt room)
  have widthRoom : Y < 2^a := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt room)
  have pairRoom : 2^r < 2^a := (le_max_right _ _).trans_lt room
  apply Fin.val_cast_of_lt
  fin_cases fieldIndex
  · exact depth.trans_lt depthRoom
  · exact width.trans_lt widthRoom
  · exact l.trans_lt pairRoom
  · exact b.trans_lt pairRoom
  · exact (bl _).trans_lt ((show 1 ≤ 2^r from one).trans_lt pairRoom)
  · exact (bl _).trans_lt ((show 1 ≤ 2^r from one).trans_lt pairRoom)

theorem peerData_empty (v : V) (p j : Fin A.degree) (ghost : ∀u : T.columns.near (frm.host v),slots v u≠j) :
    (peerData (a:=a) A S ready digits Z T frm vertex v p j 1).val=0 := by
  simp [peerData,previousPeers_empty A S ready digits Z T frm vertex f B wire K traffic weight roster v j ghost]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
