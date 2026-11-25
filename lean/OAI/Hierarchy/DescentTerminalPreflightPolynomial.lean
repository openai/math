import OAI.Hierarchy.DescentTerminalPreflightCalibration
import OAI.Hierarchy.DescentTerminalBookBitPrice
import OAI.Hierarchy.DescentTerminalRouteInvoice
import OAI.Hierarchy.DescentTerminalMaskChannels

namespace OAI
/-! # Scalar placement uses short archived data; scan counts use only the socket and node capacities -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalLocalPortBook DescentTerminalGrainProfiles DescentSIMDLookup
noncomputable section
variable (x:Spec)

/-- Independent original widths and finite geometry sizes, before any ROM or working
storage has been allocated. Numeric fields indexed by selectors do not occur here. -/
def shortFields : List ℕ :=
  [x.frozenBits,x.cohortBits,2^x.cohortBits,x.groups,x.paidLanes,x.actorLanes,x.paidBits,x.externalBits,
   x.scalar.blocks,x.scalar.columns,x.scalar.pointerBits,x.scalar.countBits,x.degree,x.cap,
   x.cableCellBits,x.grainsPerCable,x.publicGrains,x.printBits,x.vertices,x.arguments,x.binSize,x.pageBits]

private theorem chunks_le (g m:ℕ) : chunks g m≤g+m :=
  (Nat.div_le_self (g+m-1) m).trans (Nat.sub_le ..)

/-- The packed signed input has one word per drawn predecessor block and register,
regardless of the number of old replica groups contained in that word. -/
theorem scan_original {k n:ℕ} (pos:0<n) (pitch:x.signedLanes=x.groups) (groups:0<x.groups)
    (b:x.scalar.blocks≤k) (degree:x.degree≤3) (cap:x.cap≤n) (nodes:x.scalar.columns≤n)
    (cohorts:2^x.cohortBits≤n) (positive:0<k) : x.scanScale≤64*(k*n) := by
  have kn:k≤k*n:=Nat.le_mul_of_pos_right _ pos
  have nk:n≤k*n:=Nat.le_mul_of_pos_left _ positive
  have bc:x.scalar.blocks*x.cap≤k*n:=Nat.mul_le_mul b cap
  have bn:x.scalar.blocks*x.scalar.columns≤k*n:=Nat.mul_le_mul b nodes
  have cols:x.widthColumns=1+x.scalar.blocks*(2*x.cap):=by
    unfold widthColumns Counter.columns
    rw [pitch,DescentTerminalVertexFields.whole_groups groups,Nat.mul_one]
  simp only [scanScale,max_le_iff]
  refine ⟨by omega,?_,?_,?_,by omega⟩
  · rw [Nat.add_mul,Nat.mul_comm x.scalar.columns x.scalar.blocks];omega
  · unfold strips;rw [Nat.mul_add];rw [Nat.mul_left_comm x.scalar.blocks 2];omega
  · rw [cols]
    calc
      _ ≤ (1+x.scalar.blocks*(2*x.cap)+1)*3 := Nat.mul_le_mul_left _ degree
      _ ≤ _ := by rw [Nat.mul_left_comm x.scalar.blocks 2];omega

set_option maxHeartbeats 1000000 in
theorem register_original (n:ℕ) (pos:0<n) (sizes:∀z∈x.shortFields,z≤n)
    (pitch:x.signedLanes=x.groups) (groups:0<x.groups) :
    x.registerBits≤2048*n^6 := by
  simp only [shortFields,List.forall_mem_cons] at sizes
  obtain ⟨fr,cb,band,g,pay,actor,data_,ext,b,col,ptr,cnt,d,c,cell,grain,pub,draw,v,a,win,page,_⟩:=sizes
  have lift (z:ℕ) : Nat.clog 2 z≤z:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have two:n≤n^2:=by simpa [pow_two] using Nat.le_mul_of_pos_right n pos
  have powmono {j l:ℕ} (e:j≤l) : n^j≤n^l:=Nat.pow_le_pow_right pos e
  have power₂:n^2≤n^6:=powmono (by decide)
  have power₃:n^3≤n^6:=powmono (by decide)
  have power₄:n^4≤n^6:=powmono (by decide)
  have small:n≤n^6:=two.trans power₂
  have one:0<n^6:=Nat.pow_pos pos
  have sq (x y:ℕ) (xx:x≤n) (yy:y≤n) : x*y≤n^2:=by simpa only [pow_two] using Nat.mul_le_mul xx yy
  have bc:=sq _ _ b c
  have strip:x.strips≤5*n^2:=by
    unfold strips;rw [Nat.mul_add,Nat.mul_left_comm x.scalar.blocks 2];omega
  have cols:x.widthColumns≤3*n^2:=by
    unfold widthColumns Counter.columns;rw [pitch,DescentTerminalVertexFields.whole_groups groups,Nat.mul_one,
      Nat.mul_left_comm x.scalar.blocks 2];omega
  have mul₃ (z y K:ℕ) (zz:z≤n) (yy:y≤K*n^2) : z*y≤K*n^3:=by
    have h:=Nat.mul_le_mul zz yy;convert h using 1
    ring
  have xy:=sq _ _ ptr col
  have drawn:=mul₃ _ _ _ draw strip
  have signed:=mul₃ _ _ _ cell cols
  have paidWidth:=sq _ _ data_ pay
  have clp:chunks x.groups x.paidLanes≤2*n:=by have:=chunks_le x.groups x.paidLanes;omega
  have cla:chunks x.groups x.actorLanes≤2*n:=by have:=chunks_le x.groups x.actorLanes;omega
  have aslots:x.scalar.blocks*chunks x.groups x.actorLanes≤2*n^2:=by
    have h:=Nat.mul_le_mul b cla;convert h using 1
    ring
  have overlap:x.cableCap≤n^4:=by
    unfold cableCap
    exact (Nat.mul_le_mul (Nat.mul_le_mul g bc) grain).trans_eq (by ring)
  have pubRows:=sq _ _ band pub
  have arities:=sq _ _ v a
  have book:=Book.bytes_envelope x.vertices x.arguments (n^2) (v.trans two) arities (a.trans two) (Nat.pow_pos pos)
  have bytes:Nat.clog 2 x.controlBytes≤64*n^6:=by
    have h:=Nat.clog_le_of_le_pow book
    change Nat.clog 2 x.controlBytes≤60*((n^2)*(n^2)) at h
    have l:60*(n^2*n^2)=60*n^4:=by ring
    rw [l] at h;omega
  have w:=Book.WeightShelf.words_le x.vertices x.arguments 0 0
  have f:=Book.fixed_envelope x.vertices x.arguments 0 0 (n^2) (v.trans two) arities (a.trans two)
    (Nat.zero_le _) (Nat.zero_le _) (Nat.pow_pos pos)
  have weights:Nat.clog 2 (Book.WeightShelf.words x.vertices x.arguments)≤256*n^6:=by
    have h:=Nat.clog_le_of_le_pow (w.trans f);convert h using 1
    ring
  have shift:Nat.clog 2 x.controlShape.limit≤2*n:=by
    apply Nat.clog_le_of_le_pow
    simp only [controlShape,DescentTerminalControlROM.Shape.limit,max_le_iff]
    have big:2*n≤2^(2*n):=Nat.lt_two_pow_self.le
    exact ⟨⟨by omega,by omega⟩,⟨by omega,Nat.pow_le_pow_right (by decide) (by omega)⟩⟩
  have hcol:=lift (x.scalar.columns+1);have hbook:=lift (x.strips+1);have hw:=lift (x.widthColumns+1)
  have hpr:=lift (x.cableCap+1);have hpu:=lift (2^x.cohortBits*x.publicGrains+1)
  have hc:=lift (chunks x.groups x.paidLanes);have ha:=lift (x.scalar.blocks*chunks x.groups x.actorLanes)
  have half:x.halfBits≤512*n^6:=by
    simp only [halfBits,max_le_iff];omega
  have quarter:x.quarterBits≤512*n^6:=by
    simp only [quarterBits,max_le_iff];omega
  simp only [registerBits,max_le_iff];omega

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
