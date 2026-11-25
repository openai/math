import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Read a packed key through a single runtime post-to-pre actor directory -/
namespace Hierarchy.DescentResetStemKeyReindex
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def size (H₀ H₁ G M : ℕ) := span H₀ + 2*span (H₁*chunks G M)
def offsets (base H₀ : ℕ) : Bank := ⟨base, Nat.clog 2 H₀⟩
def actors (base H₀ n : ℕ) : Bank := ⟨base+span H₀, Nat.clog 2 n⟩
def chunkIDs (base H₀ n : ℕ) : Bank := ⟨base+span H₀+span n, Nat.clog 2 n⟩
def pointers (ptr H₁ : ℕ) : Bank := ⟨ptr,Nat.clog 2 H₁⟩

def keyExpr (old : Bank) (base ptr H₀ H₁ G M : ℕ) : Expr :=
  let n := H₁*chunks G M
  let p := Expr.lookup (pointers ptr H₁) (.lookup (actors base H₀ n) .row)
  .lookup old (.op .add (.lookup (chunkIDs base H₀ n) .row) (.lookup (offsets base H₀) p))

theorem work (old : Bank) (base ptr H₀ H₁ G M : ℕ) :
    (keyExpr old base ptr H₀ H₁ G M).work=30 := rfl

private def atFin {n : ℕ} (f : Fin n→ℕ) (i : ℕ) : ℕ :=
  if hi : i < n then f ⟨i,hi⟩ else 0

def literals (H₀ H₁ G M i : ℕ) : ℕ :=
  let n := H₁*chunks G M
  if i < span H₀ then chunks G M*i
  else if i < span H₀+span n then
    atFin (fun q : Fin n => ((row H₁ G M).symm q).1.val) (i-span H₀)
  else atFin (fun q : Fin n => ((row H₁ G M).symm q).2.val) (i-(span H₀+span n))

def phase (w base H₀ H₁ G M : ℕ) : NativePhase w :=
  let n := size H₀ H₁ G M
  let words := literals H₀ H₁ G M
  ⟨DescentStaticWordColumn.program w base words n,4+10*n,
    fun m=>DescentStaticWordColumn.image base words m n,@DescentStaticWordColumn.cheap w base words n⟩

theorem tariff (w base H₀ H₁ G M : ℕ) :
    (phase w base H₀ H₁ G M).ticks = 4+10*(span H₀+2*span (H₁*chunks G M)) := rfl

theorem names (w base H₀ H₁ G M : ℕ) :
    DescentStaticWordColumn.names (phase w base H₀ H₁ G M).program = 15*(size H₀ H₁ G M+1) :=
  DescentStaticWordColumn.names_mount w base (literals H₀ H₁ G M) (size H₀ H₁ G M)

theorem size_le (H₀ H₁ G M : ℕ) : size H₀ H₁ G M ≤ 2*H₀+4*(H₁*chunks G M)+3 := by
  have h := span_le H₀
  have n := span_le (H₁*chunks G M)
  unfold size
  omega

structure Fixed {w : ℕ} (base H₀ H₁ G M : ℕ) (m : Memory w) : Prop where
  offset : ∀ u : Fin H₀,m ((offsets base H₀).base+u.val) = ((chunks G M*u.val : ℕ) : Word w)
  actor : ∀ p : Row H₁ G M,m ((actors base H₀ (H₁*chunks G M)).base+(row H₁ G M p).val)=(p.1.val : Word w)
  chunk : ∀ p : Row H₁ G M,m ((chunkIDs base H₀ (H₁*chunks G M)).base+(row H₁ G M p).val)=(p.2.val : Word w)

theorem run {w base H₀ H₁ G M : ℕ} (m : Memory w) (room : base+size H₀ H₁ G M < 2^w) :
    let p := phase w base H₀ H₁ G M
    p.Runs m ∧ Fixed base H₀ H₁ G M (p.image m) ∧
      ∀ a, a < base ∨ base+size H₀ H₁ G M ≤ a → p.image m a=m a := by
  let n := H₁*chunks G M
  have sn := span_ge n
  refine ⟨?_, ⟨?_, ?_, ?_⟩,
    fun a h => DescentStaticWordColumn.frame base (size H₀ H₁ G M) (literals H₀ H₁ G M) m a h⟩
  · intro P R K machine
    exact DescentStaticWordColumn.mount base (size H₀ H₁ G M) (literals H₀ H₁ G M) m room machine
  · intro u
    have hu := u.isLt.trans_le (span_ge H₀)
    have loc : u.val < size H₀ H₁ G M := by change u.val < span H₀+2*span n;omega
    change DescentStaticWordColumn.image base (literals H₀ H₁ G M) m _ (base+u.val)=_
    rw [DescentStaticWordColumn.read _ _ _ _ loc]
    simp only [literals,ite_eq_left hu]
  · intro p
    let u : Fin n := row H₁ G M p
    have hu := u.isLt
    have loc : span H₀+u.val < size H₀ H₁ G M := by change span H₀+u.val < span H₀+2*span n;omega
    change DescentStaticWordColumn.image base (literals H₀ H₁ G M) m _ (base+span H₀+u.val)=_
    rw [Nat.add_assoc, DescentStaticWordColumn.read _ _ _ _ loc]
    simp [literals,n,atFin,u,(row H₁ G M p).isLt,show ¬span H₀+u.val < span H₀ by omega,
      show span H₀+u.val < span H₀+span n by omega]
  · intro p
    let u : Fin n := row H₁ G M p
    have hu := u.isLt
    have loc : span H₀+span n+u.val < size H₀ H₁ G M := by
      change span H₀+span n+u.val < span H₀+2*span n;omega
    change DescentStaticWordColumn.image base (literals H₀ H₁ G M) m _ (base+span H₀+span n+u.val)=_
    rw [show base+span H₀+span n+u.val=base+(span H₀+span n+u.val) by omega,
      DescentStaticWordColumn.read _ _ _ _ loc]
    simp [literals,n,atFin,u,(row H₁ G M p).isLt,show ¬span H₀+span n+u.val < span H₀ by omega,
      show ¬span H₀+span n+u.val < span H₀+span n by omega]

def Directory {w H₀ H₁ : ℕ} (ptr : ℕ) (owner : Fin H₁→Fin H₀) (m : Memory w) : Prop :=
  ∀ v, m (ptr+v.val)=((owner v).val : Word w)

theorem fits {w H₀ H₁ G M base ptr : ℕ} (old : Bank)
    (oldFit : old.Fits w base) (ptrRoom : ptr+span H₁ ≤ base)
    (room : base+size H₀ H₁ G M < 2^w) :
    (keyExpr old base ptr H₀ H₁ G M).Fits w (base+size H₀ H₁ G M) := by
  let n := H₁*chunks G M
  let endAddr := base+size H₀ H₁ G M
  have top : endAddr=base+(span H₀+2*span n) := rfl
  have upper : endAddr < 2^w := room
  have before : base ≤ endAddr := Nat.le_add_right ..
  have oFit : old.Fits w endAddr := ⟨oldFit.1,oldFit.2.1,oldFit.2.2.trans before⟩
  have pFit : (pointers ptr H₁).Fits w endAddr := by
    change 0 < span H₁ ∧ span H₁ < 2^w ∧ ptr+span H₁ ≤ endAddr
    exact ⟨span_pos _,by omega,by omega⟩
  have aFit : (actors base H₀ n).Fits w endAddr := by
    change 0 < span n ∧ span n < 2^w ∧ base+span H₀+span n ≤ endAddr
    exact ⟨span_pos _,by omega,by omega⟩
  have sFit : (offsets base H₀).Fits w endAddr := by
    change 0 < span H₀ ∧ span H₀ < 2^w ∧ base+span H₀ ≤ endAddr
    exact ⟨span_pos _,by omega,by omega⟩
  have cFit : (chunkIDs base H₀ n).Fits w endAddr := by
    change 0 < span n ∧ span n < 2^w ∧ base+span H₀+span n+span n ≤ endAddr
    exact ⟨span_pos _,by omega,by omega⟩
  exact ⟨oFit,⟨cFit,trivial⟩,sFit,pFit,aFit,trivial⟩

/-- The same physical pointer and fixed geometry serve every key bank. Neither
the program nor the shape literals contain the runtime actor mapping. -/
theorem source {w H₀ H₁ G M b base ptr : ℕ} (old : Bank) (key : Fin H₀→Fin G→Cell b)
    (owner : Fin H₁→Fin H₀) (m : Memory w) (read : Reads old key M m) (directory : Directory ptr owner m)
    (oldFit : old.Fits w base) (capacity : H₀*chunks G M ≤ old.size) (ptrRoom : ptr+span H₁ ≤ base)
    (room : base+size H₀ H₁ G M < 2^w) :
    let p := phase w base H₀ H₁ G M
    (keyExpr old base ptr H₀ H₁ G M).Fits w (base+size H₀ H₁ G M) ∧
      DescentPackedZip.Source (keyExpr old base ptr H₀ H₁ G M) (fun h g=>key (owner h) g) M (p.image m) := by
  let n := H₁*chunks G M
  let out := (phase w base H₀ H₁ G M).image m
  have geom := fits old oldFit ptrRoom room
  refine ⟨geom,?_⟩
  obtain ⟨oFit,⟨cFit,_⟩,sFit,pFit,aFit,_⟩ := geom
  obtain ⟨_,fixed,frame⟩ := run m room
  intro p
  let k : Fin n := row H₁ G M p
  have within := k.isLt.trans_le (span_ge n)
  have a := (DescentPackedZip.bank_read (actors base H₀ n) out within aFit).trans (fixed.actor p)
  have c := (DescentPackedZip.bank_read (chunkIDs base H₀ n) out within cFit).trans (fixed.chunk p)
  have pr : (pointers ptr H₁).read out (p.1.val : Word w)=((owner p.1).val : Word w) := by
    have h := p.1.isLt.trans_le (span_ge H₁)
    exact (DescentPackedZip.bank_read (pointers ptr H₁) out h pFit).trans
      ((frame (ptr+p.1.val) (.inl (by omega))).trans (directory p.1))
  have s := (DescentPackedZip.bank_read (offsets base H₀) out ((owner p.1).isLt.trans_le (span_ge H₀)) sFit).trans (fixed.offset _)
  let oldRow := row H₀ G M (owner p.1,p.2)
  have oldRead := DescentPackedZip.bank_read old out (oldRow.isLt.trans_le capacity) oFit
  have addr : oldRow.val=p.2.val+chunks G M*(owner p.1).val := rfl
  have keep : out (old.base+oldRow.val)=m (old.base+oldRow.val) :=
    frame _ (.inl (by have h := oldRow.isLt.trans_le capacity;have f := oldFit.2.2;omega))
  change old.read out (BinaryOp.add.eval
    ((chunkIDs base H₀ n).read out (k.val : Word w))
    ((offsets base H₀).read out ((pointers ptr H₁).read out ((actors base H₀ n).read out (k.val : Word w))))) = _
  rw [a,c,pr,s]
  change old.read out ((p.2.val : Word w)+((chunks G M*(owner p.1).val : ℕ) : Word w))=_
  rw [←Nat.cast_add,←addr,oldRead,keep]
  exact read (owner p.1,p.2)

end
end Hierarchy.DescentResetStemKeyReindex

end OAI
