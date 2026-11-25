import OAI.Hierarchy.ProtocolRAMReservePrefixReplay
import OAI.Hierarchy.ProtocolRAMCatalystArchiveDirectory

namespace OAI
/-! # Reusing the literal chronological owner and amount pointers after settlement -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixReserve
open Computability.VPVNP.BurstRAM PrivateRAM CatalystArchive
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {W count N : ℕ}

private theorem read_shared (b : Bank) (m u : Memory W) (j : ℕ)
    (room : j<2^W) (inside : j<b.size) (eq : u (b.base+j)=m (b.base+j)) :
    b.read u (j:Word W)=b.read m (j:Word W) := by
  simpa only [Bank.read,Fin.val_cast_of_lt room,Nat.mod_eq_of_lt inside] using eq

/-- Inverting the actual word read by the reserve scatter gives the two
original memory reads. The physical destination base cancels in the word ring. -/
theorem Directory.of_native (a : ReserveUse.Archive) (b : RouteSettlement.Banks)
    (reserveAmount : ℕ) (physical : Fin N→Fin count) (amount : Fin N→ℕ) (m : Memory W)
    (mounted : ReserveUse.Mounted a b reserveAmount physical amount m)
    (kind : ∀i : Fin N, a.kind.read m ((2*i.val:ℕ):Word W)=0 ∧
      a.kind.read m ((2*i.val+1:ℕ):Word W)≠0) :
    Directory a physical amount m := by
  refine ⟨kind,?_,?_⟩
  · intro i
    have even := (kind i).1
    simp only [Nat.cast_mul,Nat.cast_ofNat] at even
    have eq := (mounted.loaded i).1
    simpa [ReserveUse.word,ReserveUse.address,Expr.eval,DescriptorExpr.Comparison.test,RowOp.opcode,BinaryOp.eval,
      even,Nat.cast_add] using eq
  · intro i
    have odd := (kind i).2
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at odd
    simpa [ReserveUse.word,Expr.eval,DescriptorExpr.Comparison.test,RowOp.opcode,BinaryOp.eval,odd]
      using (mounted.loaded i).2

/-- The width counter may rewrite other words in the large history bank. We
only use the two immutable pointers for each occurrence and their actual cells. -/
theorem Directory.after_write (a : ReserveUse.Archive) (scratch : ℕ) (b : RouteSettlement.Banks)
    (reserveAmount : ℕ) (physical : Fin N→Fin count) (amount : Fin N→ℕ)
    (id amt : Fin N→ℕ) (raw m final : Memory W)
    (mounted : ReserveUse.Mounted a b reserveAmount physical amount m)
    (ordered : a.kind.base+2*N≤a.pointer.base) (ks : 2*N≤a.kind.size)
    (ps : 2*N≤a.pointer.size) (word : 2*N≤2^W)
    (origin : ∀ j, j<2*N→
      m (a.kind.base+j)=mount a id amt raw (a.kind.base+j) ∧
      m (a.pointer.base+j)=mount a id amt raw (a.pointer.base+j))
    (tags : ∀j,j<2*N→final (a.kind.base+j)=m (a.kind.base+j) ∧
      final (a.pointer.base+j)=m (a.pointer.base+j))
    (owners : ∀i,id i<a.history.size ∧ id i<2^W ∧
      final (a.history.base+id i)=m (a.history.base+id i))
    (amounts : ∀i,amt i<a.history.size ∧ amt i<2^W ∧
      final (a.history.base+amt i)=m (a.history.base+amt i)) :
    Directory {a with scratch:=scratch} physical amount final := by
  have original (j : ℕ) (hj : j<2*N) :
      a.kind.read m (j:Word W)=a.kind.read (mount a id amt raw) (j:Word W) ∧
      a.pointer.read m (j:Word W)=a.pointer.read (mount a id amt raw) (j:Word W) :=
    ⟨read_shared _ _ _ _ (hj.trans_le word) (hj.trans_le ks) (origin j hj).1,
      read_shared _ _ _ _ (hj.trans_le word) (hj.trans_le ps) (origin j hj).2⟩
  have even (i : Fin N) : 2*i.val<2*N := by have:=i.isLt; omega
  have odd (i : Fin N) : 2*i.val+1<2*N := by have:=i.isLt; omega
  have key (i : Fin N) := CatalystArchive.directory a id amt raw ordered ks ps word i
  have prior := Directory.of_native a b reserveAmount physical amount m mounted (fun i=>
    ⟨(original _ (even i)).1.trans (key i).1.1, (original _ (odd i)).1.trans_ne (key i).1.2⟩)
  have finalOrigin (j : ℕ) (hj : j<2*N) :=
    And.intro ((tags j hj).1.trans (origin j hj).1) ((tags j hj).2.trans (origin j hj).2)
  obtain ⟨kind,owner,amountAt⟩:=CatalystArchive.observed_fields a id amt raw final physical amount
    ordered ks ps word finalOrigin (by
      intro i
      refine ⟨(owners i).1,(owners i).2.1,(owners i).2.2.trans ?_⟩
      have atPort:=prior.owner i
      rw [(original _ (even i)).2,(key i).2.1] at atPort
      simpa only [Bank.read,Fin.val_cast_of_lt (owners i).2.1,Nat.mod_eq_of_lt (owners i).1] using atPort)
    (by
      intro i
      refine ⟨(amounts i).1,(amounts i).2.1,(amounts i).2.2.trans ?_⟩
      have atPort:=prior.amount i
      rw [(original _ (odd i)).2,(key i).2.2] at atPort
      simpa only [Bank.read,Fin.val_cast_of_lt (amounts i).2.1,Nat.mod_eq_of_lt (amounts i).1] using atPort)
  exact ⟨kind,owner,amountAt⟩

end Hierarchy.ProtocolRAM.Calendar.PrefixReserve
end

end OAI
