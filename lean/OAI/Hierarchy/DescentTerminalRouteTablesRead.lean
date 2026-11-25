import OAI.Hierarchy.DescentTerminalRouteSources
import OAI.Hierarchy.DescentTerminalReachedBooks

namespace OAI
/-! # Read the eight actual table domains used to request a terminal route -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources
open DescentTerminalEmitter.Compact DescentTerminalLocalPortBook DescentTerminalRowArena
open DescentTerminalRouteRows DescentTerminalRouteLedger Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
namespace Tables
variable {w:ℕ} (T:Tables) (A:Arena) (other:Columns) (prior:Fin 43→ℕ→ℕ)
variable (source:Fin 43→Bank) (mem:Memory w)

def Reads := ∀(j:Fin 43), 29≤j.val → j.val≤36 →
  ∀u:Fin (need (T.columns A other j)), (source j).read mem (u.val:Word w)=(T.value prior j u.val:Word w)

theorem books (read_:T.Reads A other prior source mem) (g:Gather)
    (one:g.low=source 29) (two:g.high=source 30) (three:g.menu=source 31) :
    DescentTerminalRowPlan.Fixed (G:=T.groups) (V:=T.vertices) (M:=T.maximum) (A:=T.arity)
      (a:=T.tokenBits) (W:=T.width) (q:=T.lanes) g mem := by
  constructor
  · intro r
    rw [one]
    exact read_ 29 (by decide) (by decide) r
  · intro r
    rw [two]
    exact read_ 30 (by decide) (by decide) r
  · intro i
    rw [three]
    have val:=read_ 31 (by decide) (by decide) i
    have small:i.val<T.menuSize:=i.isLt
    refine val.trans (congrArg (fun x : ℕ => (x : Word w)) ?_)
    change (if h : i.val<T.menuSize then (Book.menu (G:=T.groups) (V:=T.vertices)
      (M:=T.maximum) (A:=T.arity) (a:=T.tokenBits) T.lanes (⟨i.val,h⟩ : Fin T.menuSize)).val else 0) = _
    rw [dite_eq_left small]
    exact congrArg (fun j : Fin T.menuSize =>
      (Book.menu (G:=T.groups) (V:=T.vertices) (M:=T.maximum) (A:=T.arity)
        (a:=T.tokenBits) (W:=T.width) T.lanes j).val)
      (show (⟨i.val,small⟩ : Fin T.menuSize) = i from Fin.ext rfl)

theorem routes (read_:T.Reads A other prior source mem) (L:DescentTerminalRouteIssue.Layout)
    (rows:Fin T.extent→Row T.lanes T.nameWidth)
    (aliases:L.offset=source 32 ∧ L.phase=source 33 ∧ L.update=source 34 ∧
      L.lastRow=source 35 ∧ L.decode=source 36)
    (names:∀i:Fin T.extent,L.names.read mem (i.val:Word w)=((pack (rows i)).val:Word w)) :
    DescentTerminalRouteIssue.Reads (K:=T.bins) (W:=T.width) L rows mem := by
  obtain ⟨e32,e33,e34,e35,e36⟩:=aliases
  refine ⟨names,?_,?_,?_,?_,?_⟩
  · intro i
    rw [e32]
    exact read_ 32 (by decide) (by decide) i
  · intro i
    rw [e33]
    exact (read_ 33 (by decide) (by decide) i).trans
      (congrArg (fun x : ℕ => (x : Word w)) (T.phase prior i))
  · intro i
    rw [e34]
    have small : i.val < radix T.width T.line := i.isLt
    refine (read_ 34 (by decide) (by decide) i).trans (congrArg (fun x : ℕ => (x : Word w)) ?_)
    change (if h : i.val < radix T.width T.line then (stepROM (W:=T.width) (c:=T.line) ⟨i.val,h⟩).val else 0) = _
    rw [dite_eq_left small]
    exact congrArg (fun j : Fin (radix T.width T.line) =>
      (stepROM (W:=T.width) (c:=T.line) j).val)
      (show (⟨i.val,small⟩ : Fin (radix T.width T.line)) = i from Fin.ext rfl)
  · intro i
    rw [e35]
    let j:Fin (3*T.extent):=⟨3*i.val,Nat.mul_lt_mul_of_pos_left i.isLt (by decide)⟩
    have val:=read_ 35 (by decide) (by decide) j
    exact val.trans (congrArg (fun x : ℕ => (x : Word w)) (T.last prior i))
  · intro i
    rw [e36]
    have small : i.val < 2^T.buffer := i.isLt
    refine (read_ 36 (by decide) (by decide) i).trans (congrArg (fun x : ℕ => (x : Word w)) ?_)
    change (if h : i.val < 2^T.buffer then (lookup (W:=T.width) (q:=T.lanes) (a:=T.nameWidth) ⟨i.val,h⟩).val else 0) = _
    rw [dite_eq_left small]

end Tables
end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.RouteSources

end OAI
