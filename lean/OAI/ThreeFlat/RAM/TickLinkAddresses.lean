import OAI.ThreeFlat.RAM.TickLinkRows
import OAI.ThreeFlat.Collapse.TickLinkScan

namespace OAI
/-! # Address and payload of every native predecessor-link write -/

namespace ThreeFlat.RAM.TickLinkRows

open Computability.VPVNP.BurstRAM PrivateRAM Collapse.TickLinkScan
open scoped Fin.CommRing
variable {w : ℕ}

def Plan.slot (P : Plan) (i : ℕ) := P.rawBase + (11*(i/3)+i%3)

structure Plan.Fits (P : Plan) (w : ℕ) : Prop where
  literal : 11 < 2^w
  raw : P.rawBase+11*P.cells ≤ P.lastBase
  last : P.lastBase+P.sources ≤ P.prevBase
  prev : P.prevBase+P.sockets ≤ P.dstBase
  dst : P.dstBase+P.sources+P.sockets < 2^w
  sites : P.cells+P.sources+P.sockets+P.sources ≤ 2^w

def Plan.written (P : Plan) (a : ℕ) : Prop :=
  (P.lastBase ≤ a ∧ a < P.lastBase+P.sources) ∨
  (P.prevBase ≤ a ∧ a < P.prevBase+P.sockets) ∨
  (P.dstBase ≤ a ∧ a < P.dstBase+P.sources+P.sockets)

theorem Plan.slot_lt (P : Plan) {i : ℕ} (h : i < P.sockets) :
    P.slot i < P.rawBase+11*P.cells := by
  unfold Plan.sockets at h
  unfold Plan.slot
  omega

theorem Plan.slot_unwritten (P : Plan) (fit : P.Fits w) {i : ℕ} (h : i < P.sockets) :
    ¬ P.written (P.slot i) := by
  obtain ⟨_,a,b,c,_,_⟩ := fit
  have bound := P.slot_lt h
  unfold Plan.written
  omega

def putNat (m : Memory w) (a v : ℕ) (x : ℕ) : Word w := if x = a then (v : Word w) else m x

private theorem write_nat (m : Memory w) (a v : ℕ) (fit : a < 2^w) :
    writeMemory m (a : Word w) (v : Word w) = putNat m a v := by
  funext x
  simp only [writeMemory, putNat, Fin.val_cast_of_lt fit]

theorem action_init (P : Plan) (fit : P.Fits w) (m : Memory w) {s : ℕ} (hs : s < P.sources) :
    action .init (P.data w) (s : Word w) m = putNat m (P.lastBase+s) s := by
  obtain ⟨_,_,hl,hp,hd,_⟩ := fit
  change writeMemory m ((P.lastBase : Word w) + (s : Word w)) (s : Word w) = _
  rw [← Nat.cast_add]
  exact write_nat _ _ _ (by omega)

theorem action_socket (P : Plan) (fit : P.Fits w) (m : Memory w) {i s old : ℕ}
    (hi : i < P.sockets) (hs : s < P.sources) (ho : old < P.sources+P.sockets)
    (read : m (P.slot i) = (s : Word w)) (live : m (P.lastBase+s) = (old : Word w)) :
    action .socket (P.data w) (i : Word w) m =
      putNat (putNat (putNat m (P.prevBase+i) old) (P.dstBase+old) (middleSite P.cells P.sources i))
        (P.lastBase+s) (P.sources+i) := by
  obtain ⟨digits,rawFit,lastFit,prevFit,dstFit,_⟩ := fit
  let raw := (P.rawBase : Word w) + (11 * BinaryOp.eval .div (i : Word w) 3 +
    BinaryOp.eval .mod (i : Word w) 3)
  have rawEq : raw = (P.slot i : Word w) := by
    simp [raw,Plan.slot,BinaryOp.eval, Nat.mod_eq_of_lt (by omega : 3 < 2^w),
      Fin.val_cast_of_lt (by omega : i < 2^w)]
  have source : m raw.val = (s : Word w) := by
    rw [rawEq, Fin.val_cast_of_lt (lt_of_lt_of_le (P.slot_lt hi) (by omega))]
    exact read
  let ptr := (P.lastBase : Word w) + m raw.val
  have ptrEq : ptr = ((P.lastBase+s : ℕ) : Word w) := by simp [ptr,source]
  have oldEq : m ptr.val = (old : Word w) := by
    rw [ptrEq,Fin.val_cast_of_lt (by omega : P.lastBase+s < 2^w)]
    exact live
  change writeMemory (writeMemory (writeMemory m ((P.prevBase : Word w)+(i : Word w)) (m ptr.val))
    ((P.dstBase : Word w)+m ptr.val) (((P.cells+P.sources : ℕ) : Word w)+(i : Word w)))
      ptr ((P.sources : Word w)+(i : Word w)) = _
  rw [oldEq,ptrEq]
  simp only [← Nat.cast_add, middleSite, write_nat (w:=w) _ (P.prevBase+i) _ (by omega),
    write_nat (w:=w) _ (P.dstBase+old) _ (by omega), write_nat (w:=w) _ (P.lastBase+s) _ (by omega)]

theorem action_tail (P : Plan) (fit : P.Fits w) (m : Memory w) {s old : ℕ}
    (hs : s < P.sources) (ho : old < P.sources+P.sockets)
    (live : m (P.lastBase+s) = (old : Word w)) :
    action .tail (P.data w) (s : Word w) m =
      putNat m (P.dstBase+old) (tailSite P.cells P.sources P.sockets s) := by
  obtain ⟨_,_,lastFit,prevFit,dstFit,_⟩ := fit
  change writeMemory m ((P.dstBase : Word w)+m ((P.lastBase : Word w)+(s : Word w)).val)
    (((P.cells+P.sources+P.sockets : ℕ) : Word w)+(s : Word w)) = _
  rw [← Nat.cast_add,Fin.val_cast_of_lt (by omega : P.lastBase+s < 2^w),live]
  simp only [← Nat.cast_add, tailSite, write_nat _ _ _ (by omega : P.dstBase+old < 2^w)]

end ThreeFlat.RAM.TickLinkRows

end OAI
