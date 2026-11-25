import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Hierarchy.ProtocolRAMRepairOrdinal
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Static row and port lookup words for every occurrence -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w : ℕ}

/-- The first two columns decode a physical occurrence into its actual ball and
local port. The last two decode an interleaved scatter source word. -/
structure PortHeader where
  start : ℕ
  rows : ℕ
  ports : ℕ

def PortHeader.count (h : PortHeader) := h.rows*h.ports
def PortHeader.small (h : PortHeader) := ProtocolRAMPurchaseSampler.span h.count
def PortHeader.large (h : PortHeader) := ProtocolRAMPurchaseSampler.span (2*h.count)
def PortHeader.ball (h : PortHeader) : Bank := ⟨h.start,ProtocolRAMPurchaseSampler.bits h.count⟩
def PortHeader.field (h : PortHeader) : Bank := ⟨h.start+h.small,ProtocolRAMPurchaseSampler.bits h.count⟩
def PortHeader.owner (h : PortHeader) : Bank := ⟨h.start+2*h.small,ProtocolRAMPurchaseSampler.bits (2*h.count)⟩
def PortHeader.parity (h : PortHeader) : Bank := ⟨h.owner.base+h.large,ProtocolRAMPurchaseSampler.bits (2*h.count)⟩
def PortHeader.stop (h : PortHeader) := h.parity.base+h.large

theorem PortHeader.span (h : PortHeader) : h.stop≤ h.start+12*h.count+8 := by
  have small := ProtocolRAMPurchaseSampler.span_le h.count
  have large := ProtocolRAMPurchaseSampler.span_le (2*h.count)
  dsimp only [stop,parity,owner,PortHeader.small,PortHeader.large]
  omega

def PortHeader.stub (h : PortHeader) : Columns := ⟨h.owner,h.parity,.row,.row,.row⟩
def PortHeader.ballTerm (h : PortHeader) := Expr.lookup h.ball .row
def PortHeader.fieldTerm (h : PortHeader) := Expr.lookup h.field .row

def PortHeader.load (h : PortHeader) (m : Memory w) :=
  pairAdvice h.stub h.count (fillSegment h.field.base h.count (fun x => (((x-h.field.base)%h.ports:ℕ):Word w))
    (fillSegment h.ball.base h.count (fun x => (((x-h.ball.base)/h.ports:ℕ):Word w)) m))

theorem PortHeader.load_frame (h : PortHeader) (m : Memory w) (x : ℕ) (away : x< h.start ∨ h.stop≤ x) :
    h.load m x=m x := by
  have sm := ProtocolRAMPurchaseSampler.lt_span h.count
  have lg := ProtocolRAMPurchaseSampler.lt_span (2*h.count)
  change h.count< h.small at sm
  change 2*h.count< h.large at lg
  have left : ¬(h.ball.base≤ x ∧ x< h.ball.base+h.count) := by
    dsimp only [stop,parity,owner,ball] at *;omega
  have right : ¬(h.field.base≤ x ∧ x< h.field.base+h.count) := by
    dsimp only [stop,parity,owner,field] at *;omega
  have tag : ¬(h.parity.base≤ x ∧ x< h.parity.base+2*h.count) := by
    dsimp only [stop,parity,owner] at *;omega
  have index : ¬(h.owner.base≤ x ∧ x< h.owner.base+2*h.count) := by
    dsimp only [stop,parity,owner] at *;omega
  simp only [load,pairAdvice,stub,fillSegment,left,right,tag,index,ite_false]

structure PortHeader.Loaded (h : PortHeader) (m : Memory w) : Prop where
  first : ∀ e : Fin h.count,h.ball.read m (e.val:Word w) = ((e.val/h.ports:ℕ):Word w)
  second : ∀ e : Fin h.count,h.field.read m (e.val:Word w) = ((e.val%h.ports:ℕ):Word w)
  pair : PairDirectory h.stub m h.count

theorem PortHeader.load_ok (h : PortHeader) (m : Memory w) (wide : 0< w) (room : h.stop<2^w) :
    h.Loaded (h.load m) := by
  have small : h.count< h.small := ProtocolRAMPurchaseSampler.lt_span _
  have large : 2*h.count< h.large := ProtocolRAMPurchaseSampler.lt_span _
  have row : h.ball.base+h.small=h.field.base := rfl
  have field : h.field.base+h.small=h.owner.base := by simp [field,owner,two_mul,add_assoc]
  have owner : h.owner.base+h.large=h.parity.base := rfl
  have endBank : h.parity.base+h.large=h.stop := rfl
  have size : h.ball.size=h.small ∧ h.field.size=h.small ∧ h.owner.size=h.large ∧ h.parity.size=h.large := ⟨rfl,rfl,rfl,rfl⟩
  refine ⟨?_,?_,pairAdvice_correct h.stub h.count _ (by omega) (by change 2*h.count≤ h.owner.size;omega)
    (by change 2*h.count≤ h.parity.size;omega) (by change h.owner.base+2*h.count≤ h.parity.base;omega) wide⟩
  · intro e
    have lt := e.isLt
    simp [Bank.read,Fin.val_cast_of_lt (show e.val<2^w by omega),Nat.mod_eq_of_lt (show e.val< h.ball.size by omega),load,
      pairAdvice,stub,fillSegment,show ¬(h.parity.base≤ h.ball.base+e.val ∧ h.ball.base+e.val< h.parity.base+2*h.count) by omega,
      show ¬(h.owner.base≤ h.ball.base+e.val ∧ h.ball.base+e.val< h.owner.base+2*h.count) by omega,
      show ¬(h.field.base≤ h.ball.base+e.val ∧ h.ball.base+e.val< h.field.base+h.count) by omega,
      show h.ball.base≤ h.ball.base+e.val ∧ h.ball.base+e.val< h.ball.base+h.count by omega]
  · intro e
    have lt := e.isLt
    simp [Bank.read,Fin.val_cast_of_lt (show e.val<2^w by omega),Nat.mod_eq_of_lt (show e.val< h.field.size by omega),load,
      pairAdvice,stub,fillSegment,show ¬(h.parity.base≤ h.field.base+e.val ∧ h.field.base+e.val< h.parity.base+2*h.count) by omega,
      show ¬(h.owner.base≤ h.field.base+e.val ∧ h.field.base+e.val< h.owner.base+2*h.count) by omega,
      show h.field.base≤ h.field.base+e.val ∧ h.field.base+e.val< h.field.base+h.count by omega]

theorem PortHeader.Loaded.frame {h : PortHeader} {m after : Memory w} (loaded : h.Loaded m)
    (same : ∀ x,h.start≤ x → x< h.stop → after x=m x) : h.Loaded after := by
  have all (b : Bank) (start : h.start≤ b.base) (finish : b.base+b.size≤ h.stop) (i : Word w) : b.read after i=b.read m i := by
    have bound := Nat.mod_lt i.val (Nat.two_pow_pos b.bits)
    change i.val%b.size< b.size at bound
    exact same _ (by omega) (by omega)
  have ballRead (i : Word w) := all h.ball (by rfl) (by
    change h.start+h.small≤ h.start+2*h.small+h.large+h.large;omega) i
  have fieldRead (i : Word w) := all h.field (by change h.start≤ h.start+h.small;omega) (by
    change h.start+h.small+h.small≤ h.start+2*h.small+h.large+h.large;omega) i
  have ownerRead (i : Word w) := all h.owner (by change h.start≤ h.start+2*h.small;omega) (by
    change h.start+2*h.small+h.large≤ h.start+2*h.small+h.large+h.large;omega) i
  have parityRead (i : Word w) := all h.parity (by dsimp [parity,owner];omega) (by rfl) i
  exact ⟨fun e => (ballRead _).trans (loaded.first e),fun e => (fieldRead _).trans (loaded.second e),
    fun e => (parityRead _).trans (loaded.pair.first e),fun e => (parityRead _).trans_ne (loaded.pair.second e),
    fun e => (ownerRead _).trans (loaded.pair.firstRow e),fun e => (ownerRead _).trans (loaded.pair.secondRow e)⟩

def PortHeader.enum (h : PortHeader) : (Σ _ : Fin h.rows,Fin h.ports) ≃ Fin h.count :=
  (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv

end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
