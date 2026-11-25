import OAI.ThreeFlat.Diagonal.HistoryOccupiedTrees
import OAI.ThreeFlat.Diagonal.HistoryPortFootprint

namespace OAI
/-! # Accounting for the occupied and active joins of each history site -/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open MotifOrderedCells MotifNativeCompactors HistogramTileNetwork MotifKernel MotifOuterTerms LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} {p h c : ℕ}

/-- Charge all original rows and private bits, all tree nodes, every emitted
pin-map word, and every postorder copy of a row. -/
def siteCost (T : Tree F p) := T.rows+T.bits+T.nodes+T.footprint.pins+T.copiedRows

theorem siteCost_join {arity : Fin c → ℕ} (wire : ∀ i, Fin (arity i) → BitSource h p)
    (child : ∀ i, Tree F (arity i)) :
    (Tree.join h c arity wire child).siteCost =
      h+1+∑ i, ((child i).siteCost+(child i).rows+arity i) := by
  simp only [siteCost,rows,bits,nodes,footprint,copiedRows,Finset.sum_add_distrib]
  omega

/-- Any local upper bound for this scalar charge bounds scheduled record
work and the separately priced generation of every map word. -/
theorem scheduledWork_le_siteCost (T : Tree F p) (level setup mapCost : ℕ) :
    T.scheduledWork level setup + mapCost*T.footprint.pins ≤
      (10000+25+1016*level+setup+mapCost)*T.siteCost := by
  have core : T.nodes+T.rows+T.bits ≤ T.siteCost := by unfold siteCost; omega
  have maps : T.footprint.pins ≤ T.siteCost := by unfold siteCost; omega
  rw [Nat.add_mul,scheduledWork]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ core) (Nat.mul_le_mul_left _ maps)

/-- Coefficient of a party's resident work and one extra copy of each row at its parent. -/
def partyJoinCoefficient (b k s e d : ℕ) :=
  4*partyCoefficient b k s e d+(5+s+e)+partyPinCoefficient b k s e d

section Occupied
variable {J E S H Z F : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] [Fintype Z] [DecidableEq Z] {k d r s p c a : ℕ}
  (D : PortGraph J E) (G : Supply J S) (place : J → Z) (v : Z) (w base : E → ℕ) (sw : H → S → ℕ)
  (code : H ↪ Fin (2^k)) (id : H ≃ Fin s) (z : Histogram H r) (edges : Fin a ≃ Absorbed (ports G) place v)
  (parts : Fin c ≃ {j // place j=v}) {e n : Fin c → ℕ} (supply : ∀ i, Fin (e i) ≃ (ports G).Port (parts i).val)
  (demand : ∀ i, Fin (n i) ≃ D.Port (parts i).val) (fits : ∀ i q u, sw q (supply i u).1.1 ≤ d)
  (M : ∀ z j, D.State (fun e => Fin (2^base e)) j → (ports G).State (fun a => Fin (2^sw z a)) j → F)
  (C : BitNetwork F ((r*d)+(r*d+r*d))) (count : BitNetwork F (r+(r+r)))
  (old : ∀ i, (q : D.Port (parts i).val) → Fin (w q.1.1) → BitSource (order G place v sw z edges (k:=k)).bits p)
  (cross : (x : ExternalAt (ports G) place v) → Fin (histWidth sw z x.val.val+r*k) → Fin p)

local notation "piece" i:arg => party D G (Subtype.val (parts i)) base (hd D base code parts demand i)
  (supply i) sw (fits i) M id z C count
local notation "root" => occupiedTree D G place v w base sw code id z edges parts supply demand fits M C count old cross

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Fintype Z] in
theorem occupiedTree_siteCost :
    (root).siteCost = (order G place v sw z edges (k:=k)).bits+1+
      ∑ i, ((piece i).siteCost+(piece i).rows+
        (r*(e i*k)+(r*(hd D base code parts demand i).arity+e i*(r*d)))) :=
  siteCost_join _ _

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Fintype Z] in
theorem occupiedTree_pinWords :
    (root).footprint.pins = (∑ i, (piece i).footprint.pins)+
      ∑ i, (r*(e i*k)+(r*(hd D base code parts demand i).arity+e i*(r*d))) := rfl

local notation "P" i:arg => party D G (Subtype.val (parts i)) base (hd D base code parts demand i)
  (supply i) sw (fits i) M id z (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d))
local notation "L" => ((r+1)*(siteHeight r d+1)^3)

omit [Fintype Z] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- The extra occupied-node cost is the absorbed private width, one node,
and the actual mixed selector/header/boundary arity of every party. -/
theorem occupiedTree_native_cost :
    (occupiedTree D G place v w base sw code id z edges parts supply demand fits M
      (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d)) old cross).siteCost ≤
      (order G place v sw z edges (k:=k)).bits+1+∑ i,
        (partyJoinCoefficient (hd D base code parts demand i).arity k s (e i) d*L+
        (r*(e i*k)+(r*(hd D base code parts demand i).arity+e i*(r*d)))) := by
  rw [occupiedTree_siteCost]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  apply Nat.add_le_add_right
  let b := (hd D base code parts demand i).arity
  obtain ⟨size,maps,nodes⟩ := party_resources D G (parts i).val base (hd D base code parts demand i)
    (supply i) sw (fits i) M id z
  have copies := rowCopies_le (party_within D G (parts i).val base (hd D base code parts demand i)
    (supply i) sw (fits i) M id z (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d)))
  change (P i).siteCost+(P i).rows ≤ partyJoinCoefficient b k s (e i) d*L
  rw [show partyJoinCoefficient b k s (e i) d*L =
      4*(partyCoefficient b k s (e i) d*L)+(5+s+e i)*L+partyPinCoefficient b k s (e i) d*L by
    unfold partyJoinCoefficient; ring]
  unfold siteCost
  dsimp only [b]
  omega

end Occupied

section Active
variable {M J V F : Type} [Fintype M] [Fintype J] [Fintype V] [DecidableEq V] {s p : ℕ}
  (site : M → J → V) (v : V) (order : Fin s ≃ Active site v) (child : ∀ _m : Active site v, Tree F p)

omit [Fintype M] [Fintype J] [Fintype V] [DecidableEq V] in
/-- The public pin map has one copy of its full `p`-word identity map per occupied child. -/
theorem activeTree_pinWords : (activeTree site v order child).footprint.pins =
    (∑ i : Fin s, (child (order i)).footprint.pins)+s*p := by
  change _ + (∑ _ : Fin s, p) = _
  simp []

omit [Fintype M] [Fintype J] [Fintype V] [DecidableEq V] in
theorem activeTree_siteCost : (activeTree site v order child).siteCost =
    1+s*p+∑ i : Fin s, ((child (order i)).siteCost+(child (order i)).rows) := by
  rw [activeTree,siteCost_join,Finset.sum_add_distrib]
  simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

omit [Fintype V] in
theorem activeTree_cost_le (bound : Active site v → ℕ) (ok : ∀ m, (child m).siteCost ≤ bound m) :
    (activeTree site v order child).siteCost ≤ 1+s*p+2*∑ m, bound m := by
  rw [activeTree_siteCost,←order.sum_comp bound,Finset.mul_sum]
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have h := ok (order i)
  have rows : (child (order i)).rows ≤ (child (order i)).siteCost := by unfold siteCost; omega
  omega

end Active
end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
