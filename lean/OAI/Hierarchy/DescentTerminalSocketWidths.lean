import OAI.Hierarchy.DescentTerminalHeaderSockets

namespace OAI
/-! # Source row and size read directly from the issued cable and exterior prefix words -/
namespace Hierarchy.DescentTerminalHeaderSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentPackedColony DescentTerminalWidthRowsRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {w:ℕ} (m:Memory w) (r:Word w)
def source {n:ℕ} (f:ℕ→ℕ) (z:Option (Fin n)) := z.elim 0 (fun i=>f i.val)
def finish {n:ℕ} (f:ℕ→ℕ) (z:Option (Fin n)) := z.elim 0 (fun i=>f (i.val+1))
variable {n:ℕ} (tab:Bank) (f:ℕ→ℕ) (boot:f 0=0) (wide:2<2^w) (cap:n<2^w)
  (words:∀i:Fin n,tab.read m (i.val:Word w)=(f (i.val+1):Word w))
include boot wide cap words in
theorem window (key:Expr) (z:Option (Fin n)) (hk:key.eval m r=(code z:Word w)) :
    (starts tab key).eval m r=(source f z:Word w) ∧ (ends tab key).eval m r=(finish f z:Word w) := by
  cases z with
  | none=>
    simp [starts,ends,hk,code,source,finish,Expr.eval,DescriptorExpr.Comparison.test,
      Fin.lt_def,Nat.mod_eq_of_lt wide]
  | some i=>
    have fits:i.val+1<2^w:=by have:=i.isLt;omega
    have pos : 0 < i.val+1:=by omega
    have off : ((i.val+1:ℕ):Word w)≠0:=by
      intro eqn
      have eqv:=congrArg Fin.val eqn
      rw [Fin.val_cast_of_lt fits,Fin.val_zero] at eqv
      omega
    have last : (((i.val+1:ℕ):Word w)-(1:Word w))=(i.val:Word w):=by simp
    refine ⟨?_,?_⟩
    · by_cases zero:i.val=0
      · simp [starts,hk,code,source,zero,Expr.eval,DescriptorExpr.Comparison.test,Fin.lt_def,
          Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt (by omega : 1<2^w),boot]
      · have ge : ¬i.val+1<2:=by omega
        let prev:Fin n:=⟨i.val-1,by have:=i.isLt;omega⟩
        have prevEq:prev.val+1=i.val:=by dsimp [prev];omega
        have castPrev:((i.val+1:ℕ):Word w)-((2:ℕ):Word w)=(prev.val:Word w):=by
          have sub:2≤ i.val+1:=by omega
          rw [←Nat.cast_sub (R:=Word w) sub]
          exact congrArg (fun k : ℕ => (k : Word w)) (by dsimp [prev];omega)
        simp only [starts,Expr.eval,DescriptorExpr.Comparison.test,hk,code,Option.elim,decide_eq_true_eq,Fin.lt_def,
          Fin.val_cast_of_lt fits,Fin.val_cast_of_lt wide,ite_eq_right ge,RowOp.opcode,BinaryOp.eval,castPrev,words,prevEq,source]
    · simp only [ends,Expr.eval,hk,code,Option.elim,DescriptorExpr.Comparison.test,beq_iff_eq,
        Nat.cast_zero,Nat.cast_one,ite_eq_right off,RowOp.opcode,BinaryOp.eval,last,words,finish]

/-- An inclusive prefix exposed by the actual native width writer, ready to be used for endpoint reads. -/
theorem prefix_reads (L:DescentTerminalWidthRowsRAM.Layout) (q p:ℕ) (counts:Fin L.groups→ℕ)
    (cap:∀j,counts j≤L.cap) (rows:(tape q p counts).length≤L.rows) (fit:L.source.Fits w L.origin)
    (input:L.groups≤L.source.size) (room:L.stop<2^w)
    (read:∀j:Fin L.groups,m (L.source.base+j.val)=(counts j:Word w)) (j:Fin L.groups) :
    L.prefix.read (L.finalMem q p w m) (j.val:Word w)=((passed q p counts (j.val+1)).length:Word w) := by
  have ran:=DescentTerminalWidthRowsRAM.run L q p counts m cap rows fit input room read
  have can:=L.fits q p w fit room
  rw [DescentPackedZip.bank_read L.prefix _ (j.isLt.trans_le (Nat.le_pow_clog (by decide) _)) can.prefix]
  exact ran.2.2.2.1 j

variable {H D:ℕ} (L:Layout) (R:Fin H→Fin D→Option (Fin H)) (v:Fin H) (x:Expr)
  (hx:x.eval m r=(v.val:Word w)) (high:H<2^w) (area:H*D<2^w)
  (physical:∀(v:Fin H) (j:Fin D),L.roster.read m ((v.val*D+j.val:ℕ):Word w)=(target (R v j):Word w))
  (cf pf:ℕ→ℕ) (c₀:cf 0=0) (p₀:pf 0=0)
  (cable:∀j:Fin (H*D),L.cablePrefix.read m (j.val:Word w)=(cf (j.val+1):Word w))
  (ext:∀j:Fin H,L.publicPrefix.read m (j.val:Word w)=(pf (j.val+1):Word w))
def origin (j:Fin (D+1)) : ℕ := Fin.cases (motive:=fun _=>ℕ) (pf v.val) (fun t=>source cf (ordinal R v t)) j
def endAt (j:Fin (D+1)) : ℕ := Fin.cases (motive:=fun _=>ℕ) (pf (v.val+1)) (fun t=>finish cf (ordinal R v t)) j

include hx wide high area physical c₀ p₀ cable ext in
theorem read_socket (j:Fin (D+1)) (mono:Monotone cf) (pubMono:Monotone pf) :
    (head L H D x j).eval m r=(origin R v cf pf j:Word w) ∧
    (amount L H D x j).eval m r=((endAt R v cf pf j-origin R v cf pf j:ℕ):Word w) := by
  refine Fin.cases ?_ (fun t=>?_) j
  · have key:(successor x).eval m r=(code (some v):Word w):=by simp [successor,Expr.eval,hx,code,RowOp.opcode,BinaryOp.eval,Nat.cast_add]
    have both:=window m r L.publicPrefix pf p₀ wide high ext (successor x) (some v) key
    refine ⟨both.1,?_⟩
    change (ends L.publicPrefix (successor x)).eval m r - (starts L.publicPrefix (successor x)).eval m r =
      ((pf (v.val+1) - pf v.val : ℕ) : Word w)
    rw [both.2,both.1]
    exact (Nat.cast_sub (R:=Word w) (pubMono (Nat.le_succ v.val))).symm
  · let z:=ordinal R v t
    have key:=canonical_read L R m r high physical v x hx t
    have both:=window m r L.cablePrefix cf c₀ wide area cable (canonical L x H D t.val) z key
    have le_ : source cf z≤finish cf z := by cases z with | none=>exact le_rfl | some s=>exact mono (Nat.le_succ _)
    refine ⟨both.1,?_⟩
    change (ends L.cablePrefix (canonical L x H D t.val)).eval m r -
      (starts L.cablePrefix (canonical L x H D t.val)).eval m r = ((finish cf z - source cf z : ℕ) : Word w)
    rw [both.2,both.1]
    exact (Nat.cast_sub (R:=Word w) le_).symm


end
end Hierarchy.DescentTerminalHeaderSockets

end OAI
