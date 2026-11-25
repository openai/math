import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Immutable ordinal and parity words for sparse repair occurrences -/

namespace Hierarchy.ProtocolRAM.RepairHistogram
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
variable {w : ℕ}

/-- `destination` reads the actual measured incidence. The installer directs every
uncharged physical edge to a separate scratch word outside the commodity range. -/
structure Columns where
  occurrence : Bank
  isData : Bank
  destination : Expr
  credit : Expr
  charge : Expr

structure PairDirectory (p : Columns) (m : Memory w) (n : ℕ) : Prop where
  first : ∀ i : Fin n,p.isData.read m ((2*i.val:ℕ):Word w)=0
  second : ∀ i : Fin n,p.isData.read m ((2*i.val+1:ℕ):Word w)≠0
  firstRow : ∀ i : Fin n,p.occurrence.read m ((2*i.val:ℕ):Word w)=(i.val:Word w)
  secondRow : ∀ i : Fin n,p.occurrence.read m ((2*i.val+1:ℕ):Word w)=(i.val:Word w)

/-- A single frozen ordinal/parity header serves every shorter finite scatter tape. -/
theorem PairDirectory.restrict {p : Columns} {m : Memory w} {size n : ℕ} (h : PairDirectory p m size)
    (small : n≤ size) : PairDirectory p m n :=
  ⟨fun i=>h.first (Fin.castLE small i),fun i=>h.second (Fin.castLE small i),
    fun i=>h.firstRow (Fin.castLE small i),fun i=>h.secondRow (Fin.castLE small i)⟩

/-- Only the quotient and parity of a public source ordinal enter this directory.
The packet, histogram, credits, debits and commodity addresses are all read elsewhere. -/
def pairAdvice (p : Columns) (n : ℕ) (m : Memory w) : Memory w :=
  fillSegment p.isData.base (2*n) (fun a => (((a-p.isData.base)%2:ℕ):Word w))
    (fillSegment p.occurrence.base (2*n) (fun a => (((a-p.occurrence.base)/2:ℕ):Word w)) m)

theorem pairAdvice_correct (p : Columns) (n : ℕ) (m : Memory w) (size : 2*n≤2^w)
    (owner : 2*n≤p.occurrence.size) (tag : 2*n≤p.isData.size) (sep : p.occurrence.base+2*n≤p.isData.base)
    (wide : 0<w) : PairDirectory p (pairAdvice p n m) n := by
  have odd (k : ℕ) (hk : k<2*n) : p.isData.read (pairAdvice p n m) (k:Word w)=((k%2:ℕ):Word w) := by
    simp [Bank.read,Fin.val_cast_of_lt (hk.trans_le size),Nat.mod_eq_of_lt (hk.trans_le tag),pairAdvice,fillSegment,
      show p.isData.base≤p.isData.base+k ∧ p.isData.base+k<p.isData.base+2*n by omega]
  have row (k : ℕ) (hk : k<2*n) : p.occurrence.read (pairAdvice p n m) (k:Word w)=((k/2:ℕ):Word w) := by
    simp [Bank.read,Fin.val_cast_of_lt (hk.trans_le size),Nat.mod_eq_of_lt (hk.trans_le owner),pairAdvice,fillSegment,
      show ¬(p.isData.base≤p.occurrence.base+k ∧ p.occurrence.base+k<p.isData.base+2*n) by omega,
      show p.occurrence.base≤p.occurrence.base+k ∧ p.occurrence.base+k<p.occurrence.base+2*n by omega]
  constructor
  · intro j
    rw [odd _ (by have := j.isLt; omega),show (2*j.val)%2=0 by omega,Nat.cast_zero]
  · intro j
    rw [odd _ (by have := j.isLt; omega),show (2*j.val+1)%2=1 by omega]
    intro zero
    have h := congrArg Fin.val zero
    rw [Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at h
    exact Nat.one_ne_zero h
  · intro j
    rw [row _ (by have := j.isLt; omega),show 2*j.val/2=j.val by omega]
  · intro j
    rw [row _ (by have := j.isLt; omega),show (2*j.val+1)/2=j.val by omega]

end Hierarchy.ProtocolRAM.RepairHistogram

end OAI
