import OAI.Hierarchy.DescentPackedCanvasSetup
import OAI.Hierarchy.DescentPackedCanvasSources

namespace OAI
/-! # Copy, literal installation, sorted roster and raw witness on a single real RAM image -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentSIMDLookup DescentPackedColony DescentPackedWalsh DescentPackedFlowPublication
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
theorem Geometry.Resident.keep (G : Geometry.Plan) {w} (before out : Memory w) (prev : G.Resident before)
    (saved : ∀a,G.origin≤a→a<G.stop→ out a=before a) : G.Resident out := by
  have bounds:G.origin≤G.meta ∧ G.meta≤G.pointers ∧ G.pointers≤G.stop:=
    ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
  constructor
  · intro a
    apply mounted_resident G.hosts G.bits G.origin (a+1) ((axesList G.high G.low).map axis) before before out
      (fun i _=>prev.walsh i) ?_ a (by omega)
    intro z lo hi
    have hi':z<G.meta:=by simpa [Geometry.meta,axesList] using hi
    exact saved z lo ((hi'.trans_le bounds.2.1).trans_le bounds.2.2)
  · intro a lo hi;exact (saved _ (bounds.1.trans lo) (hi.trans_le bounds.2.2)).trans (prev.sparse _ lo hi)
  · intro v;exact (saved _ ((bounds.1.trans bounds.2.1).trans (Nat.le_add_right ..))
      (Nat.add_lt_add_left v.isLt _)).trans (prev.keys v)

namespace Setup
variable {k c HP D R u l b short M w : ℕ} (tokens : Tokens k c) (roster src count : Bank)
    (floor f B K grain : ℕ)
local notation "p" => plan tokens roster HP D u l b short M floor f B K grain
local notation "C" => core tokens roster HP D u l b short M floor f B K grain
local notation "G" => staticGeometry HP D u l b floor f B K
local notation "pb" => Book.pitchBits HP u
local notation "n" => HP*chunks R M

structure Snapshot (N : ℕ) (next : Fin HP→Fin D→Option (Fin HP)) (X : Fin HP→Fin R→Cell (b*2^k))
    (tags : Fin HP→Fin R→DescentPackedFlowRAM.Slot (2^k) c→Cell short) (mem : Memory w) : Prop where
  room : Room C HP R M short b w
  tokens (t) : Reads ((C).tokens t) (fun v g=>tags v g t) M mem
  insert (j : Fin D) (x : Fin (2^k)) : DescentPackedZip.Static ((C).inserts j x)
    (DescentPackedFlowRAM.insert (b:=b) (d:=short) grain j.val x) M mem
  added : DescentPackedZip.Static (C).add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem
  ports : Mounted (C).peers next mem R M
  range : DescentPackedFlowReturn.Header (C).header (C).middle mem D HP R M
  census (q : Row HP R M) : mem ((p).first+(row HP R M q).val)=((data X q).val:Word w)
  retained : (G).Resident mem
  countRead : mem count.base=(N:Word w)

theorem stage (H : ℕ) (next : Fin HP→Fin D→Option (Fin HP)) (X : Fin HP→Fin R→Cell (b*2^k))
    (tags : Fin HP→Fin R→DescentPackedFlowRAM.Slot (2^k) c→Cell short) (mem : Memory w)
    (size : 2^(u+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M)
    (safe : src.base+src.size≤floor) (capacity : n≤ src.size) (raw : Reads src X M mem)
    (old : ∀t,(tokens t).base+(tokens t).size≤floor ∧ n≤(tokens t).size)
    (inputs : ∀t,Reads (tokens t) (fun v g=>tags v g t) M mem)
    (prior : roster.base+roster.size≤floor) (slots : HP*D≤roster.size)
    (ranks : ∀v:Fin HP,∀j:Fin D,mem (roster.base+(v.val*D+j.val))=(target (next v j):Word w))
    (lowCount : count.base+count.size≤floor) (observed : mem count.base=(H:Word w))
    (word : (p).endAddress<2^w) :
    ∃out, (prep tokens roster HP D u l b short M floor f B K grain src R w).Exec mem out
      (ticks HP D u l b short M floor f B K k R) ∧
      Snapshot (M:=M) (u:=u) (l:=l) tokens roster count floor f B K grain H next X tags out ∧
      ∀a<floor,out a=mem a := by
  obtain ⟨start,book_,front,cap⟩:=areas tokens roster HP D u l b short M floor f B K grain
  have bound:=(p).stops
  have lo : floor≤(p).first:=by omega
  have upper : (p).first+page HP u≤(p).totals:=by
    have pay:page HP u≤(u+l+1)*page HP u:=by rw [Nat.succ_mul];omega
    exact (Nat.add_le_add_left pay (p).first).trans bound.2.1
  have lanes':chunks R M=2^u:=original_chunks size lanes hm
  have total:n≤page HP u:=by rw [lanes'];exact rows_le HP u
  have place : src.Fits w (p).first:=Placement.fitsOf _ (safe.trans lo) (by omega)
  obtain ⟨copied,write,cheap,census,keepCopy⟩:=copy_original src (p).first X mem place capacity (by omega) raw
  let I:=(G).image (w:=w)
  obtain ⟨header,realGeo,hw,hwc,keepHeader⟩:=Geometry.run G copied (by omega)
  let priorImage:=I.output copied
  have same (a : ℕ) (z:a<floor): priorImage a=mem a:=(keepHeader _ (.inl z)).trans (keepCopy _ (.inl (z.trans_le lo)))
  have terminals (t) : (tokens t).base+(tokens t).size≤(G).stop ∧ n≤(tokens t).size:=
    ⟨(old t).1.trans start,(old t).2⟩
  have ord (v:Fin HP) (j:Fin D) : priorImage (roster.base+(v.val*D+j.val))=(target (next v j):Word w):=by
    have t:=Nat.mul_le_mul_right D v.isLt;rw [Nat.succ_mul] at t
    have end_:(v.val*D+j.val)<roster.size:=by have:=j.isLt;omega
    exact (same _ ((Nat.add_lt_add_left end_ _).trans_le prior)).trans (ranks v j)
  have np:n≤2^pb:=by rw [lanes'];exact Book.pitch_room HP u
  have hp:HP≤2^pb:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos u)).trans (Book.pitch_room HP u)
  obtain ⟨ran,room,ins,add,ports,index,keepBook,_⟩:=Book.execute tokens roster (G).stop pb D b short grain M
    priorImage next np hp terminals (prior.trans start) slots ord (by change (C).middle+D*(C).pitch<2^w; omega)
  let dst:=Book.image (G).stop pb D (2^k) b short grain R M priorImage
  have oldLow (a : ℕ) (h:a<floor) : dst a=mem a:=(keepBook _ (.inl (h.trans_le start))).trans (same _ h)
  have tagRead (t) : Reads ((C).tokens t) (fun v g=>tags v g t) M dst:=by
    intro q;exact (oldLow _ ((Nat.add_lt_add_left ((row HP R M q).isLt.trans_le (old t).2) _).trans_le (old t).1)).trans (inputs t q)
  have fullCount : dst count.base=(H:Word w):=(oldLow _ (by have:0<count.size:=Nat.two_pow_pos _;omega)).trans observed
  have resident:=Geometry.Resident.keep G priorImage dst realGeo (fun a _ hi=>keepBook _ (.inl hi))
  have totalRead (q : Row HP R M) : dst ((p).first+(row HP R M q).val)=((data X q).val:Word w):=by
    have frontBound : (C).first≤(p).first+(row HP R M q).val := by omega
    have headerBound : (G).stop≤(p).first+(row HP R M q).val := by omega
    exact (keepBook _ (.inr frontBound)).trans ((keepHeader _ (.inr headerBound)).trans (census q))
  have lenI:I.length=(G).stop-floor:=rfl
  refine ⟨dst,?_,⟨room,tagRead,ins,add,ports,index,totalRead,resident,fullCount⟩,oldLow⟩
  intro labels regs slots
  exact Procedure.Exec.then (Procedure.Exec.then write header) ran

end Setup
end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
