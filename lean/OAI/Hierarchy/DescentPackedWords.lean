import OAI.Hierarchy.DescentRotorPackets
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Encoding real bundles in the occupied digits of the rotor rows -/

namespace Hierarchy.DescentRotor
open scoped BigOperators Classical
noncomputable section
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

def cell (src dst : E → V) (i j : V) := Finset.univ.filter fun e => src e=i ∧ dst e=j

def serial (src dst : E → V) (i j : V) (e : E) :=
  if h : e∈cell src dst i j then ((cell src dst i j).equivFin ⟨e,h⟩).val else 0

omit [Fintype V] in
theorem serial_lt (src dst : E → V) (e : E) :
    serial src dst (src e) (dst e) e < (cell src dst (src e) (dst e)).card := by
  have h : e∈cell src dst (src e) (dst e) := by simp [cell]
  simp only [serial,dite_eq_left h]
  exact Fin.isLt _

theorem packet_fits {w n : ℕ} (hw : 0<w) : n≤groups w n*w := by
  have H := (div_le_iff₀ (by exact_mod_cast hw : (0:ℝ)<w)).mp (Nat.le_ceil ((n:ℝ)/w))
  exact_mod_cast H

/-- A concrete bundle uses its serial number among the bundles with exactly
these two terminals. Its group and digit are quotient and remainder. -/
def packetAddress (src dst : E → V) {w : ℕ} (hw : 0<w) (e : E) :
    Packet w (fun i j => (cell src dst i j).card) × Fin w :=
  let n := serial src dst (src e) (dst e) e
  (⟨src e,dst e,⟨n/w,(Nat.div_lt_iff_lt_mul hw).2 ((serial_lt src dst e).trans_le (packet_fits hw))⟩⟩,
    ⟨n%w,Nat.mod_lt _ hw⟩)

omit [Fintype V] in
theorem packetAddress_injective (src dst : E → V) {w : ℕ} (hw : 0<w) :
    Function.Injective (packetAddress src dst hw) := by
  intro e f eq
  have start := congrArg (fun p => p.1.1) eq
  have stop := congrArg (fun p => p.1.2.1) eq
  have quot := congrArg (fun p => p.1.2.2.val) eq
  have remd := congrArg (fun p => p.2.val) eq
  change src e=src f at start
  change dst e=dst f at stop
  let ne := serial src dst (src e) (dst e) e
  let nf := serial src dst (src f) (dst f) f
  change ne/w=nf/w at quot
  change ne%w=nf%w at remd
  have same : ne=nf := by
    calc ne=ne%w+w*(ne/w) := (Nat.mod_add_div ..).symm
         _=nf := by rw [quot,remd,Nat.mod_add_div]
  change serial src dst (src e) (dst e) e=serial src dst (src f) (dst f) f at same
  rw [start,stop] at same
  have he : e∈cell src dst (src f) (dst f) := by simp [cell,start,stop]
  have hf : f∈cell src dst (src f) (dst f) := by simp [cell]
  simp only [serial,dite_eq_left he,dite_eq_left hf] at same
  exact congrArg Subtype.val ((cell src dst (src f) (dst f)).equivFin.injective (Fin.ext same))

def bitWord (w : ℕ) : (Fin w → Bool) ≃ Fin (2^w) :=
  (Equiv.arrowCongr (Equiv.refl (Fin w)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- An unoccupied group digit is pinned to false on both ends. Every
occupied digit encodes the specified occurrence of the original bundle. -/
def packetWord {P : Type*} {w u : ℕ} (addr : E → P × Fin w) (x : E → Fin u → Bool)
    (p : P) (k : Fin u) : Fin (2^w) :=
  bitWord w (fun i => if h : ∃ e,addr e=(p,i) then x h.choose k else false)

theorem packetWord_eq {P : Type*} {w u : ℕ} (addr : E → P × Fin w)
    (unique : Function.Injective addr) (x y : E → Fin u → Bool) :
    (∀p,packetWord addr x p=packetWord addr y p) ↔ ∀e,x e=y e := by
  constructor
  · intro eq e
    funext k
    have digits := (bitWord w).injective (congrFun (eq (addr e).1) k)
    have found : ∃ f,addr f=((addr e).1,(addr e).2) := ⟨e,rfl⟩
    have exactHit : found.choose=e := unique found.choose_spec
    simpa only [dite_eq_left found,exactHit] using congrFun digits (addr e).2
  · intro h
    rw [funext h]
    exact fun _=>rfl

/-- Counting actual source and target rows of the finite group-packet type. -/
theorem packet_rows (m : V → V → ℕ) (w : ℕ) (i : V) :
    (Finset.univ.filter fun p : Packet w m => p.1=i).card=∑j,groups w (m i j) := by
  rw [Finset.card_filter,Fintype.sum_sigma]
  change (∑ v : V, ∑ _p : Σ j : V, Fin (groups w (m v j)), if v=i then 1 else 0)=_
  simp only [Finset.sum_ite_irrel,Finset.sum_const,Finset.card_univ,nsmul_one,nsmul_zero,
    Fintype.card_sigma,Fintype.card_fin]
  simp

theorem packet_cols (m : V → V → ℕ) (w : ℕ) (j : V) :
    (Finset.univ.filter fun p : Packet w m => p.2.1=j).card=∑i,groups w (m i j) := by
  rw [Finset.card_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_sigma]
  change (∑ t : V, ∑ _ : Fin (groups w (m v t)), if t=j then 1 else 0)=_
  simp only [Finset.sum_ite_irrel,Finset.sum_const,Finset.card_univ,nsmul_one,nsmul_zero,Fintype.card_fin]
  simp

end
end Hierarchy.DescentRotor

end OAI
