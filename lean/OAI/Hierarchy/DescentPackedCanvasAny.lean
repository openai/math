import OAI.Hierarchy.DescentCanvasFrameBasics
import OAI.Hierarchy.DescentPackedCanvasStaging
import OAI.Hierarchy.DescentPackedCanvasProgram
import OAI.Hierarchy.DescentPackedCanvasRoom
import OAI.Hierarchy.DescentCanvasUnsignedPasses
import OAI.Hierarchy.DescentPackedWalshPassAny

namespace OAI
/-! # Unconditional physical time for the complete packed census and rectangle publication -/
namespace Hierarchy
open DescentSIMDLookup DescentPackedWalsh DescentPackedColony DescentPackedFlowPublication
open DescentPackedSingletonDepth ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace DescentPackedFlowPublication.Book

theorem install_any {w : ℕ} (base bits D r b d grain J M : ℕ) (mem : Memory w)
    (limit : base+gateWords D r b d M+indexWords D bits<2^w) :
    (install w base bits D r b d grain J M).Exec mem (image base bits D r b d grain J M mem)
      (charge D r b d M bits) := by
  let head:=base+gateWords D r b d M
  let gates:=gate D r b d grain
  let mid:=DescentPackedZip.Book.image gates (width b r d) M base mem
  have front:=@DescentStaticWordColumn.mount w base (gateWords D r b d M)
    (DescentPackedZip.Book.data gates (width b r d) M) mem (by omega : head<2^w)
  have back:=@DescentStaticWordColumn.mount w head (indexWords D bits) (indexData D (chunks J M) bits) mid limit
  rw [charge,show 8+10*(gateWords D r b d M+indexWords D bits)=
    (4+10*gateWords D r b d M)+(4+10*indexWords D bits) by omega]
  intro labels regs slots
  exact Procedure.Exec.then front back
end DescentPackedFlowPublication.Book

namespace DescentSixParty.PackedFlow.Canvas.Setup
variable {k c : ℕ} (tokens : Tokens k c) (roster src count : Bank)
  (HP D R u l b short M floor f B K grain δ w : ℕ)
local notation "C" => core tokens roster HP D u l b short M floor f B K grain
local notation "p" => plan tokens roster HP D u l b short M floor f B K grain
local notation "G" => staticGeometry HP D u l b floor f B K
local notation "pb" => Book.pitchBits HP u
local notation "N" => HP*((u+l)+1)+HP*D
local notation "n" => HP*chunks R M

theorem setup_any_framed (mem : Memory w) (batch : chunks R M=2^u)
    (safe : src.base+src.size≤floor) (lim : (p).endAddress<2^w) :
    ∃dst,(prep tokens roster HP D u l b short M floor f B K grain src R w).Exec mem dst
      (ticks HP D u l b short M floor f B K k R) ∧
      ∀i,i<floor ∨ (p).endAddress≤ i→dst i=mem i := by
  obtain ⟨one,two,three,four⟩:=areas tokens roster HP D u l b short M floor f B K grain
  obtain ⟨_,s,t,rr,v,x,y⟩:=(p).stops
  have pp:page HP u≤(u+l+1)*page HP u:=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  change (p).first+(u+l+1)*page HP u≤(p).totals at s
  have lo:floor≤(p).first:=by omega
  have step : n≤page HP u:=by rw [batch];exact rows_le HP u
  let e : Expr:=.lookup src .row
  let mid:=ProtocolRAM.image (p).first n e mem
  have expr:e.Fits w (p).first:=⟨Placement.fitsOf _ (safe.trans lo) (by omega),trivial⟩
  have copyExec : (copy w (p).first n src).Exec mem mid (4+18*n):=by
    have clock : 4+n*(2*e.work+4)=4+18*n := by change 4+n*18=4+18*n; rw [Nat.mul_comm n 18]
    rw [←clock]
    exact @scan_exec w (p).first n e mem expr (by omega)
  let I:=(G).image (w:=w)
  obtain ⟨imageExec,_,_,_,_⟩ := Geometry.run G mid (by omega)
  have last : (G).stop+Book.gateWords D (2^k) b short M+Book.indexWords D pb<2^w:=
    show (C).first<2^w by omega
  have bookExec:=@Book.install_any w (G).stop pb D (2^k) b short grain R M (I.output mid) last
  have geoLength:(G).stop-floor=I.length:=rfl
  refine ⟨Book.image (G).stop pb D (2^k) b short grain R M (I.output mid),?_,?_⟩
  · intro labels regs slots
    exact Procedure.Exec.then (Procedure.Exec.then copyExec imageExec) bookExec
  · intro i hi
    have lastEnd : (G).stop+Book.gateWords D (2^k) b short M+Book.indexWords D pb=(C).first:=rfl
    apply (DescentStaticWordColumn.frame ((G).stop+Book.gateWords D (2^k) b short M) (Book.indexWords D pb) _ _ i (by omega)).trans
    apply (DescentStaticWordColumn.frame (G).stop (Book.gateWords D (2^k) b short M) _ _ i (by omega)).trans
    apply ((Geometry.run G mid (by omega : (G).stop<2^w)).2.2.2.2 i (by change i<floor ∨ (G).stop≤ i;omega)).trans
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)



theorem setup_any (mem : Memory w) (batch : chunks R M=2^u)
    (safe : src.base+src.size≤floor) (lim : (p).endAddress<2^w) :
    ∃dst,(prep tokens roster HP D u l b short M floor f B K grain src R w).Exec mem dst
      (ticks HP D u l b short M floor f B K k R) := by
  obtain ⟨dst,run,_⟩:=setup_any_framed tokens roster src HP D R u l b short M floor f B K grain w mem batch safe lim
  exact ⟨dst,run⟩

theorem prepare_any_framed (out : ℕ) (mem : Memory w) (batch : chunks R M=2^u)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ n≤(tokens t).size)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (oldCount : count.base+count.size≤floor)
    (smooth : DescentBaseProfile.decayExponent δ<2^w) (dim : u+l<2^w)
    (spanOut : (p).endAddress≤out) (word : out+N*2^u<2^w) :
    ∃dst,((p).prepare C count k δ R M w out).Exec mem dst ((p).prepareTicks C k δ R M w) ∧
      ∀i,i<floor ∨ out+N*2^u≤ i→dst i=mem i := by
  have bounded:(p).endAddress<2^w:=spanOut.trans_lt ((Nat.le_add_right ..).trans_lt word)
  obtain ⟨one,two,three,four⟩:=areas tokens roster HP D u l b short M floor f B K grain
  have cuts : (C).middle+D*(C).pitch≤(p).first ∧
      (p).first+(u+l+1)*page HP u≤(p).totals ∧ (p).totals+HP≤(p).scratch ∧
      (p).scratch+(u+l+2)*Placement.pad HP≤(p).headerBase ∧
      (p).headerBase+3*N≤(p).depthPage ∧ (p).depthPage+N≤(p).gainPage ∧
      (p).gainPage+N≤(p).endAddress := (p).stops
  have pst:(G).stop≤(p).middle:=two.trans three
  have width : HP*2^u≤(C).pitch:=Book.pitch_room HP u
  have rows : n≤2^pb:=by rw [batch];exact width
  have host : HP≤2^pb:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans width
  have fr : (C).first≤(p).first:=by omega
  have top : (C).middle+D*(C).pitch<2^w:=by omega
  have room:=Book.room tokens roster (G).stop pb D b short grain M (J:=R) rows host
    (fun q'=>⟨(oldTokens q').1.trans one,(oldTokens q').2⟩) (oldRoster.trans one) slots top
  obtain ⟨m₁,flow,flowKeep⟩:=DescentPackedFlowPublication.execute_any_framed C room mem
  have fwt:=@DescentPackedWalsh.after_any w floor (p).first HP u l b m₁
    (show (G).meta≤(p).first from ((show (G).meta≤(G).stop from (Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans pst).trans (Nat.le_add_right ..))
    (show (p).first+(u+l+1)*page HP u<2^w by have h:=cuts.2.1;change (p).first+(u+l+1)*page HP u≤(p).totals at h;omega)
  let m₂:=DescentPackedWalsh.after floor (p).first HP u l b 0 (axesList u l) m₁
  let data_:=transformBank (p).first HP u l
  let L:=(p).depth C k δ
  let T:=(p).metaTape C k δ
  have edgeBase:(C).peers.roster.base≤(p).first:=((Nat.le_add_right ..).trans room.nearBelow).trans fr
  have «meta»:=(p).header_room pst (C).peers.roster.base edgeBase bounded
  have gather:=(p).gather_room pst width out spanOut word
  have smoothing:=(p).measured_room (C).peers.roster.base δ k (room.nearBelow.trans fr) bounded smooth dim
  obtain ⟨ptr,raw,_⟩:=(p).tap_rooms pst bounded
  have fit : (expr data_ (p).zeroPtr b).Fits w (p).totals:=by
    simp [expr,firstTotal,Expr.Fits,ptr,data_]
    exact raw
  have read : (tap data_ (p).zeroPtr b (p).totals HP w).Exec m₂ (runMem data_ (p).zeroPtr b (p).totals HP m₂) (4+HP*32):=by
    have clock : 4+HP*(2*(expr data_ (p).zeroPtr b).work+4)=4+HP*32 := by rw [tap_cost]
    rw [←clock]
    have inside : (p).totals+HP≤(p).scratch := cuts.2.2.1
    exact @scan_exec w (p).totals HP (expr data_ (p).zeroPtr b) m₂ fit (by omega)
  let temp:=runMem data_ (p).zeroPtr b (p).totals HP m₂
  have shape : (L.cpu w L.M).Exec temp (L.output temp L.M) (L.clocks w L.M) := L.execute temp smoothing L.M le_rfl
  obtain ⟨m₃,publish,pubKeep⟩:=DescentPackedRectangle.execute_any_framed (H:=HP) (u:=u) (l:=l) (D:=D) T (p).pullTape (L.output temp L.M) «meta» (by omega) gather (by omega)
  have countFit:count.base+count.size≤(p).headerBase:=by omega
  have banks:=(p).masks_room pst count countFit bounded
    (⟨L.base (L.M+1),Nat.clog 2 HP⟩:Bank) (⟨(C).peers.roster.base,Nat.clog 2 (HP*D)⟩:Bank)
  obtain ⟨m₄,mask,maskKeep⟩:=DescentPackedRectangle.Canvas.masks_any_framed (owners:=T.owner) (count:=count)
    (depth:=⟨(p).headerBase+N,Nat.clog 2 N⟩) (gain:=⟨(p).headerBase+2*N,Nat.clog 2 N⟩)
    (head:=(p).depthPage) (tail:=(p).gainPage) (H:=HP) (k:=u+l) (D:=D) m₃ banks (by omega) (by omega)
  refine ⟨m₄,Procedure.Exec.then flow (Procedure.Exec.then (Procedure.Exec.then fwt
    (Procedure.Exec.then read shape)) (Procedure.Exec.then publish mask)),?_⟩
  intro i hi
  have flowLow : floor≤(C).first:=one.trans two
  have startLow : (C).first≤(p).first:=fr
  have firstEnd : (p).first+(u+l+1)*page HP u≤(p).totals:=cuts.2.1
  have smoothEnd : L.base (L.M+2)≤(p).headerBase:=by
    change (p).scratch+(u+l-f+2)*Placement.pad HP≤(p).headerBase
    have h:=Nat.mul_le_mul_right (Placement.pad HP) (show u+l-f+2≤u+l+2 by omega)
    exact (Nat.add_le_add_left h _).trans cuts.2.2.2.1
  apply (maskKeep i (by omega)).trans
  have pubFrame : i < (p).headerBase ∨ out + N * 2 ^ u ≤ i := by omega
  apply (pubKeep i pubFrame).trans
  apply (L.output_frame temp L.M i smoothing.sites (by change i<(p).scratch ∨ L.base (L.M+2)≤ i;omega)).trans
  apply (ProtocolRAMGeneratedWrite.frame_image (p).totals HP _ m₂ i (by omega)).trans
  apply (DescentPackedWalsh.after_frame floor (p).first HP u l b m₁ i (by omega)).trans
  exact flowKeep i (by omega)



theorem prepare_any (out : ℕ) (mem : Memory w) (batch : chunks R M=2^u)
    (oldTokens : ∀t,(tokens t).base+(tokens t).size≤floor ∧ n≤(tokens t).size)
    (oldRoster : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (oldCount : count.base+count.size≤floor)
    (smooth : DescentBaseProfile.decayExponent δ<2^w) (dim : u+l<2^w)
    (spanOut : (p).endAddress≤out) (word : out+N*2^u<2^w) :
    ∃dst,((p).prepare C count k δ R M w out).Exec mem dst ((p).prepareTicks C k δ R M w) := by
  obtain ⟨dst,run,_⟩:=prepare_any_framed tokens roster count HP D R u l b short M floor f B K grain δ w out
    mem batch oldTokens oldRoster slots oldCount smooth dim spanOut word
  exact ⟨dst,run⟩

end DescentSixParty.PackedFlow.Canvas.Setup
end
end Hierarchy

end OAI
