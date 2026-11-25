import OAI.Hierarchy.DescentDyadicReductionRead
import OAI.Hierarchy.DescentWalshDyadicSums

namespace OAI
/-! # Contiguous dyadic work pages and the finite common reduction header -/
namespace Hierarchy.DescentPackedWalshReduction
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Plan where
  sites : ℕ
  axis : ℕ
  height : ℕ
  bits : ℕ
  positive : 0<bits

namespace Plan
variable (P : Plan)
def depth := Nat.clog 2 P.sites
def laneBits (t : ℕ) := min P.axis (Nat.log 2 (P.height/(8*(P.bits+t))))
def hosts (t : ℕ) := 2^(P.depth-t)
def chunks (t : ℕ) := 2^(P.axis-P.laneBits t)
def lanes (t : ℕ) := 2^P.laneBits t
def tile (t : ℕ) : Tile :=
  ⟨P.depth-(t+1),P.axis-P.laneBits t,P.laneBits t-P.laneBits (t+1),P.laneBits (t+1),P.bits+t⟩

theorem decreasing (t : ℕ) : P.laneBits (t+1)≤P.laneBits t := by
  apply min_le_min (le_refl _)
  apply Nat.log_mono_right
  apply Nat.div_le_div_left
  · omega
  · have positive := P.positive;omega

theorem old_hosts {t : ℕ} (ht : t<P.depth) : (P.tile t).H*2=P.hosts t := by
  unfold Tile.H tile hosts
  rw [show P.depth-t=(P.depth-(t+1))+1 by omega,pow_succ]
theorem old_lanes (t : ℕ) : (P.tile t).Z*(P.tile t).L=P.lanes t := by
  simp only [tile,Tile.Z,Tile.L,lanes,←pow_add,Nat.sub_add_cancel (P.decreasing t)]
theorem new_chunks (t : ℕ) : (P.tile t).K*(P.tile t).Z=P.chunks (t+1) := by
  have lt:P.laneBits t≤P.axis:=Nat.min_le_left ..
  have next:=P.decreasing t
  simp only [Tile.K,Tile.Z,tile,chunks,←pow_add]
  congr 1
  omega
theorem rows (t : ℕ) : (P.tile t).rows=P.hosts (t+1)*P.chunks (t+1) := by
  rw [←P.new_chunks t]
  simp only [Tile.rows,Nat.mul_assoc]
  rfl
theorem inputRows {t : ℕ} (lt : t<P.depth) : (P.tile t).inputRows=P.hosts t*P.chunks t := by
  unfold Tile.inputRows
  rw [P.old_hosts lt]
  rfl

/-- Small digit tuples use a common short table. Once only one lane fits,
the scalar native adder can continue at full address-word precision. -/
def scalar (t : ℕ) : Prop := P.height<8*(P.bits+t)
instance (t : ℕ) : Decidable (P.scalar t) := inferInstanceAs (Decidable (P.height<8*(P.bits+t)))

theorem scalar_lanes {t : ℕ} (h : P.scalar t) : P.lanes t=1 ∧ P.lanes (t+1)=1 ∧
    P.chunks t=2^P.axis ∧ P.chunks (t+1)=2^P.axis := by
  change P.height<8*(P.bits+t) at h
  have next : P.height<8*(P.bits+(t+1)):=by omega
  simp [lanes,chunks,laneBits,Nat.div_eq_of_lt h,Nat.div_eq_of_lt next]

def headerSize (t : ℕ) := if P.scalar t then 0 else (P.tile t).span
def headerAt (P : Plan) (root : ℕ) : ℕ→ℕ
  | 0=>root
  | t+1=>P.headerAt root t+P.headerSize t
def dataAt (P : Plan) (first : ℕ) : ℕ→ℕ
  | 0=>first
  | t+1=>P.dataAt first t+P.hosts t*P.chunks t

theorem header_mono (root : ℕ) : Monotone (P.headerAt root) :=
  monotone_nat_of_le_succ (fun _=>Nat.le_add_right ..)
theorem data_mono (first : ℕ) : Monotone (P.dataAt first) :=
  monotone_nat_of_le_succ (fun _=>Nat.le_add_right ..)

def mount (P : Plan) {w : ℕ} (root : ℕ) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | t+1=>if P.scalar t then P.mount root m t else
    (P.tile t).mount (P.headerAt root t) (P.mount root m t)

theorem headerRead {w : ℕ} (root : ℕ) (m : Memory w) {n t : ℕ} (lt : t<n)
    (packed : ¬P.scalar t) (j : ℕ) (cell : j<(P.tile t).span) :
    P.mount root m n (P.headerAt root t+j)=(P.tile t).word j := by
  induction n with
  | zero=>omega
  | succ n ih=>
    by_cases now : t=n
    · subst n
      simpa only [mount,ite_eq_right packed] using (P.tile t).mounted_at (P.headerAt root t) (P.mount root m t) j cell
    · have before : t<n:=by omega
      have lower:=P.header_mono root (show t+1≤n from before)
      rw [headerAt,headerSize,ite_eq_right packed] at lower
      rw [mount]
      split
      · exact ih before
      · rw [Tile.before _ _ _ (by omega)]
        exact ih before

theorem mount_high {w : ℕ} (root : ℕ) (m : Memory w) (n : ℕ) (i : ℕ)
    (past : P.headerAt root n ≤ i) : P.mount root m n i=m i := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [mount]
    split
    next extra=>exact ih ((P.header_mono root (Nat.le_succ n)).trans past)
    next extra=>
      rw [headerAt,headerSize,ite_eq_right extra] at past
      exact ((P.tile n).beyond _ _ past).trans (ih (by omega))

def values (x : Fin P.sites→Fin (2^P.axis)→ℕ) (t v d : ℕ) :=
  DescentWalshDyadicSums.value x t v (d : Fin (2^P.axis))
theorem values_step (x : Fin P.sites→Fin (2^P.axis)→ℕ) (t : ℕ) :
    addSites (P.values x t)=P.values x (t+1) := by
  funext v d
  exact (DescentWalshDyadicSums.value_succ x t v _).symm
theorem value_bound (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀v d,x v d<2^P.bits) (t v d : ℕ) :
    P.values x t v d<2^(P.bits+t) := DescentWalshDyadicSums.value_lt x P.bits hx t v _

end Plan
end
end Hierarchy.DescentPackedWalshReduction

end OAI
