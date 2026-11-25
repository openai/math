import OAI.Hierarchy.DescentTerminalPeerCounterRead
import OAI.Hierarchy.DescentTerminalNeighborSlots
import OAI.Hierarchy.DescentMountedSortedRoster
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Ticket and source expressions on the attained sorted host-neighbor table -/
namespace Hierarchy.DescentTerminalGrainProfiles.Counter
open DescentSIMDLookup DescentPackedColony DescentStaticWordColumn Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

structure Sockets where
  origin : ℕ
  roster : Bank

namespace Sockets
variable (C:Sockets) (H D:ℕ) {w : ℕ}
def home:Bank:=⟨C.origin,Nat.clog 2 (H*D)⟩
def lane:Bank:=⟨C.origin+(C.home H D).size,Nat.clog 2 (H*D)⟩
def head:Bank:=⟨C.origin+2*(C.home H D).size,Nat.clog 2 (H*D)⟩
def stop:=C.origin+3*(C.home H D).size

private def literals (chunks:ℕ) (index:ℕ) :=
  let n:=(C.home H D).size
  let i:=index%n
  if index<n then i/D else if index<2*n then i%D+1 else i/D*chunks
def prepare (w chunks:ℕ):=DescentStaticWordColumn.program w C.origin (C.literals H D chunks) (3*(C.home H D).size)
def ready (chunks:ℕ) (m:Memory w):=DescentStaticWordColumn.image C.origin (C.literals H D chunks) m (3*(C.home H D).size)
def ticket:Expr :=
  let neighbor:=Expr.lookup C.roster .row
  .branch .lt neighbor (.lit H) (.branch .lt neighbor (.lookup (C.home H D) .row) (.lit 0) (.lookup (C.lane H D) .row)) (.lit 0)
def first:Expr:=.lookup (C.head H D) .row

def gate {H D : ℕ} (R:Fin H→Fin D→Option (Fin H)) (h:Fin H) (j:Fin D):ℕ :=
  match R h j with
  | none=>0
  | some u=>if h≤u then j.val+1 else 0

theorem mount (chunks:ℕ) (m:Memory w) (limit:C.stop H D<2^w) :
    (C.prepare H D w chunks).Exec m (C.ready H D chunks m) (4+10*(3*(C.home H D).size)) ∧
      CheapCode (C.prepare H D w chunks) ∧ ∀a,a<C.origin→C.ready H D chunks m a=m a := by
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ limit,DescentStaticWordColumn.cheap _ _ _ _,?_⟩
  exact fun a h=>DescentStaticWordColumn.frame _ _ _ _ _ (.inl h)

theorem measured (R:Fin H→Fin D→Option (Fin H)) (m:Memory w) (c:ℕ)
    (_space:C.stop H D<2^w) (graph:H<2^w)
    (fit:C.roster.Fits w C.origin) (cap:H*D≤C.roster.size)
    (roster:∀h j,m (C.roster.base+(h.val*D+j.val))=(target (R h j):Word w))
    (h:Fin H) (j:Fin D) :
    let i:=finProdFinEquiv (h,j)
    (C.first H D).eval (C.ready H D c m) (i.val:Word w)=((h.val*c:ℕ):Word w) ∧
    (C.ticket H D).eval (C.ready H D c m) (i.val:Word w)=(gate R h j:Word w) := by
  let n:=(C.home H D).size
  let a:=h.val*D+j.val
  have order:(finProdFinEquiv (h,j)).val=a:=by simp [a,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have aH:a<H*D:=order ▸ (finProdFinEquiv (h,j)).isLt
  have slots:H*D≤n:=Nat.le_pow_clog (by decide) _
  have small:a<n:=aH.trans_le slots
  have word:a<2^w:=aH.trans (cap.trans_lt fit.2.1)
  have Dpos:0<D:=Nat.zero_lt_of_lt j.isLt
  have div:a/D=h.val:=by simp [a,Nat.add_comm _ j.val,Nat.add_mul_div_right _ _ Dpos,Nat.div_eq_of_lt j.isLt]
  have mod_:a%D=j.val:=by simp [a,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  let boot:=C.ready H D c m
  have take (offset:ℕ) (low:offset<3*n) : boot (C.origin+offset)=(C.literals H D c offset:Word w):=
    DescentStaticWordColumn.read _ _ _ _ low
  have keep (addr : ℕ) (low : addr < C.origin) : boot addr = m addr :=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl low)
  have h0:(C.home H D).read boot (a:Word w)=(h.val:Word w):=by
    change boot (C.origin+(a:Word w).val%n)=_
    rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt small,take a (by omega)]
    simp [literals,n,small,div,Nat.mod_eq_of_lt small]
  have h1:(C.lane H D).read boot (a:Word w)=((j.val+1:ℕ):Word w):=by
    change boot (C.origin+n+(a:Word w).val%n)=_
    rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt small,Nat.add_assoc,take (n+a) (by omega)]
    simp [literals,n,show ¬n+a<n by omega,show n+a<2*n by omega,Nat.mod_eq_of_lt small,mod_]
  have h2:(C.head H D).read boot (a:Word w)=((h.val*c:ℕ):Word w):=by
    change boot (C.origin+2*n+(a:Word w).val%n)=_
    rw [Fin.val_cast_of_lt word,Nat.mod_eq_of_lt small,Nat.add_assoc,take (2*n+a) (by omega)]
    simp [literals,n,show ¬2*n+a<n by omega,show ¬2*n+a<2*n by omega,Nat.add_mod,Nat.mod_eq_of_lt small,div]
  have native:C.roster.read boot (a:Word w)=(target (R h j):Word w):=by
    rw [Bank.read,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt (aH.trans_le cap)]
    rw [keep (C.roster.base + a) (by have:=fit.2.2; omega)]
    exact roster h j
  dsimp only
  rw [order]
  refine ⟨h2,?_⟩
  change (C.ticket H D).eval boot (a:Word w)=_
  simp only [ticket,Expr.eval,native,h0,h1,Comparison.test]
  cases phys:R h j with
  | none=>simp [target,gate,phys]
  | some u=>
    have uh:=u.isLt.trans graph
    have hh:=h.isLt.trans graph
    have inside : (u.val : Word w) < (H : Word w) := by
      change ((u.val : Word w).val) < (H : Word w).val
      rw [Fin.val_cast_of_lt uh, Fin.val_cast_of_lt graph]
      exact u.isLt
    have below : (u.val : Word w) < (h.val : Word w) ↔ u < h := by
      change ((u.val : Word w).val) < (h.val : Word w).val ↔ u.val < h.val
      rw [Fin.val_cast_of_lt uh, Fin.val_cast_of_lt hh]
    by_cases forward : h ≤ u
    · simp [target, gate, phys, inside, below, forward, not_lt.mpr forward]
    · simp [target, gate, phys, inside, below, forward, lt_of_not_ge forward]

end Sockets
end
end Hierarchy.DescentTerminalGrainProfiles.Counter

end OAI
