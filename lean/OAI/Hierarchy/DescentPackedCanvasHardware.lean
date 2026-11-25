import OAI.Hierarchy.DescentPackedCanvasTariff

namespace OAI
/-! # Cheap native code and instruction text for the complete reset prelude -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentSIMDLookup DescentPackedFlowPublication DescentPackedFlowBatch
open DescentBaseProfile DescentMeasuredHeader DescentPackedRectangle DescentPackedSingletonDepth DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

private theorem batch_text (w base rows pitch start count n : ℕ) (e : ℕ→Expr)
    (small : ∀j,start≤j→j<start+n→(e j).work≤count) :
    let cpu:=ProtocolRAM.program w (passes base rows pitch e start n)
    CheapCode cpu ∧ names cpu≤15+n*(11+4*count) := by
  induction n generalizing start with
  | zero=>exact ⟨@scan_cheap _ _ _ _,by rw [passes,ProtocolRAM.program,names_scan]; simp only [Nat.zero_mul,Nat.add_zero]; decide⟩
  | succ n ih=>
    obtain ⟨old,tail⟩:=ih (start+1) (fun j lo hi=>small _ (by omega) (by omega))
    refine ⟨cheap_seq (@scan_cheap _ _ _ _) old,?_⟩
    change names ((scan w (base+start*pitch) rows (e start)).seq _ )≤_
    rw [names_seq,names_scan]
    have countSucc : (n+1)*(11+4*count) = n*(11+4*count)+(11+4*count) := Nat.succ_mul ..
    have work:=small start le_rfl (by omega)
    omega

def flowSize (D r c : ℕ) :=
    (15+D*(11+4*(1+18*(r*c))))+(15+D*(11+4*(7+121*D)))

theorem flow_hardware {D r c : ℕ} (A : Layout D r c) (w H J M : ℕ) :
    CheapCode (procedure A H J M w) ∧ names (procedure A H J M w)≤flowSize D r c := by
  obtain ⟨a,sa⟩:=batch_text w A.first (H*chunks J M) A.pitch 0 (1+18*(r*c)) D A.front
    (fun j _ bound=>by
      have hj : j < D := by omega
      simp [Layout.front,hj,DescentPackedFlowRAM.work])
  obtain ⟨b,sb⟩:=batch_text w A.middle (H*chunks J M) A.pitch 0 (7+121*D) D (A.both H)
    (fun j _ bound=>by
      have hj : j < D := by omega
      simpa [Layout.both,hj] using DescentPackedFlowPair.cost A.header A.peers A.issued A.add H ⟨j,hj⟩)
  exact ⟨cheap_seq a b,(names_seq ..).le.trans (Nat.add_le_add sa sb)⟩

private theorem headers_text (T : Tape) (w H m D base : ℕ) :
    CheapCode (headerProgram T w base H m D) ∧ names (headerProgram T w base H m D)≤3*(11+4*128) := by
  have a:=column_cost T H m .live;have b:=column_cost T H m .depth;have c:=column_cost T H m .gain
  refine ⟨cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)) (@scan_cheap _ _ _ _),?_⟩
  simp only [headerProgram,names_seq,names_scan]
  omega

private theorem join_hardware {w : ℕ} (left right : Procedure w) {x y : ℕ}
    (hl : CheapCode left ∧ names left ≤ x) (hr : CheapCode right ∧ names right ≤ y) :
    CheapCode (left.seq right) ∧ names (left.seq right) ≤ x+y :=
  ⟨cheap_seq (A:=left) (B:=right) hl.1 hr.1,
    (names_seq left right).le.trans (Nat.add_le_add hl.2 hr.2)⟩

private theorem scan_hardware (w dest rows : ℕ) (e : Expr) (cost : ℕ) (h : e.work=cost) :
    CheapCode (scan w dest rows e) ∧ names (scan w dest rows e) ≤ 11+4*cost := by
  refine ⟨scan_cheap w dest rows e,?_⟩
  rw [names_scan,h]

private theorem read_hardware (T : Tape) (A : Gather) (w base out H u l D : ℕ) :
    let read := DescentPackedRectangle.code T A w base out H u l D
    CheapCode read ∧ names read ≤ 3*(11+4*128)+(11+4*48) := by
  dsimp only [DescentPackedRectangle.code]
  exact join_hardware (headerProgram T w base H (u+l) D)
    (scan w out ((H*((u+l)+1)+H*D)*2^u) (expression A))
    (headers_text T w H (u+l) D base)
    (scan_hardware w out ((H*((u+l)+1)+H*D)*2^u) (expression A) 48 rfl)

private theorem masks_hardware (owner count a b : Bank) (outD outG P m D w : ℕ) :
    let mask := DescentPackedRectangle.Canvas.masks owner count a b outD outG P m D w
    CheapCode mask ∧ names mask ≤ 2*(11+4*22) := by
  have maskWork (old : Bank) : (DescentPackedRectangle.Canvas.masked owner count old).work = 22 := rfl
  refine ⟨cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _),?_⟩
  simp only [DescentPackedRectangle.Canvas.masks,names_seq,names_scan,maskWork]
  try decide

def text (HP D r c u l : ℕ) :=
    flowSize D r c + (19+183*(u+l)) + (11+4*14) + 4*depthCost HP D (u+l) +
    3*(11+4*128) + (11+4*48) + 2*(11+4*22)

set_option maxHeartbeats 1600000 in
theorem work_hardware {k c : ℕ} (tokens : Tokens k c) (roster count : Bank)
    (HP D R u l b short M floor f B K grain δ w out : ℕ) :
    let C:=core tokens roster HP D u l b short M floor f B K grain
    let p:=plan tokens roster HP D u l b short M floor f B K grain
    let cpu:=p.prepare C count k δ R M w out
    CheapCode cpu ∧ names cpu≤text HP D (2^k) c u l := by
  intro C p cpu
  let L:=p.depth C k δ
  let T:=p.metaTape C k δ
  let N:=HP*(u+l+1)+HP*D
  let front:=procedure C HP R M w
  let walsh:=DescentPackedWalsh.code w floor p.first HP u l b 0 (axesList u l)
  let gather:=DescentPackedRectangle.code T p.pullTape w p.headerBase out HP u l D
  let masks:=DescentPackedRectangle.Canvas.masks T.owner count ⟨p.headerBase+N,Nat.clog 2 N⟩
    ⟨p.headerBase+2*N,Nat.clog 2 N⟩ p.depthPage p.gainPage HP (u+l) D w
  let tapper:=tap (transformBank p.first HP u l) p.zeroPtr b p.totals HP w
  let depthCpu:=L.cpu w L.M
  have hw:=pass_text floor p.first HP b w 0 (axesList u l)
  have hwSize : (axesList u l).length=u+l:=by simp [axesList]
  rw [hwSize] at hw
  have ht := scan_hardware w p.totals HP (expr (transformBank p.first HP u l) p.zeroPtr b)
    14 (tap_cost ..)
  have base:=DepthRAM.Layout.hardware L w L.M
  have hd : CheapCode depthCpu ∧ names depthCpu ≤ 4*depthCost HP D (u+l) :=
    ⟨base.cheap,base.size.trans (Nat.mul_le_mul_left 4
      (depth_time HP D (u+l) k f B p.totals C.peers.roster.base p.scratch δ w))⟩
  have pre:=join_hardware walsh (tapper.seq depthCpu) hw (join_hardware tapper depthCpu ht hd)
  have post:=join_hardware gather masks (read_hardware T p.pullTape w p.headerBase out HP u l D)
    (masks_hardware T.owner count _ _ p.depthPage p.gainPage HP (u+l) D w)
  have body:=join_hardware front ((walsh.seq (tapper.seq depthCpu)).seq (gather.seq masks))
    (flow_hardware C w HP R M) (join_hardware (walsh.seq (tapper.seq depthCpu)) (gather.seq masks) pre post)
  have cost : flowSize D (2^k) c + ((19+183*(u+l) + ((11+4*14)+4*depthCost HP D (u+l)))+
        ((3*(11+4*128)+(11+4*48))+2*(11+4*22))) = text HP D (2^k) c u l := by
    unfold text
    omega
  rw [cost] at body
  exact body

def allText (HP D u l b short M k c : ℕ) :=
  39+15*(inputWords HP D u l b+1)+15*(Book.gateWords D (2^k) b short M+
    Book.indexWords D (Book.pitchBits HP u)+2)+text HP D (2^k) c u l

theorem full_hardware {k c : ℕ} (tokens : Tokens k c) (roster src count : Bank)
    (HP D R u l b short M floor f B K grain δ w out : ℕ) :
    let C:=core tokens roster HP D u l b short M floor f B K grain
    let p:=plan tokens roster HP D u l b short M floor f B K grain
    let cpu:=(prep tokens roster HP D u l b short M floor f B K grain src R w).seq
      (p.prepare C count k δ R M w out)
    CheapCode cpu ∧ names cpu≤allText HP D u l b short M k c := by
  intro C p cpu
  let Q:=staticGeometry HP D u l b floor f B K
  obtain ⟨work,bound⟩:=work_hardware tokens roster count HP D R u l b short M floor f B K grain δ w out
  have source:=(Q.image (w:=w)).hardware
  have installed:=Book.names w Q.stop (Book.pitchBits HP u) D (2^k) b short grain R M
  have length:(Q.image (w:=w)).length=inputWords HP D u l b:=by
    simp [Q,Geometry.image,DescentPackedColony.Phase.Arena.Image.length,Geometry.stop,Geometry.pointers,
      Geometry.meta,staticGeometry,inputWords,Nat.add_assoc]
  refine ⟨cheap_seq (cheap_seq (cheap_seq (@scan_cheap _ _ _ _) source.1)
    (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _))) work,?_⟩
  have stored:names (copy w p.first (HP*chunks R M) src)=39:=by rw [copy,names_scan];rfl
  change names ((((copy w p.first (HP*chunks R M) src).seq (Q.image (w:=w)).program).seq
    (Book.install w Q.stop (Book.pitchBits HP u) D (2^k) b short grain R M)).seq
    (p.prepare C count k δ R M w out)) ≤ _
  change names (p.prepare C count k δ R M w out) ≤ text HP D (2^k) c u l at bound
  rw [names_seq,names_seq,names_seq,stored,source.2,installed,length]
  unfold allText
  omega

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
