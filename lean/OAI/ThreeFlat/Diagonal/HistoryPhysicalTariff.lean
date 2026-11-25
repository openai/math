import OAI.ThreeFlat.Diagonal.HistorySiteFootprint
import OAI.ThreeFlat.Diagonal.HistoryDirectParty
import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.Diagonal.FixedMotifMaxWidth

namespace OAI
/-! # Copy-count costs of a fixed native motif at an occupied history site -/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open MotifOrderedCells MotifNativeCompactors HistogramTileNetwork MotifKernel MotifOuterTerms LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators
noncomputable section

variable {F H J E S : Type} [Field F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [Fintype H] [DecidableEq H] [Nonempty H]
    {r k p e n d s : ℕ} (D : PortGraph J E) (G : Supply J S) (j : J) (w base : E → ℕ)
    (B : Header (D.Port j) H (fun q => base q.1.1) k n) (sa : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ)
    (fits : ∀ z q, sw z (sa q).1.1 ≤ d)
    (M : ∀ z j, D.State (fun e => Fin (2^base e)) j → (ports G).State (fun a => Fin (2^sw z a)) j → F)
    (id : H ≃ Fin s) (z : Histogram H r)
    (old : (a : D.Port j) → Fin (w a.1.1) → Fin p)
    (fresh : (a : (ports G).Port j) → Fin (histWidth sw z a.1.1+r*k) → Fin p)

local notation "L" => ((r+1)*(siteHeight r d+1)^3)
local notation "T" => party D G j base B sa sw fits M id z (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d))

def headerWidth (D : PortGraph J E) (base : E → ℕ) (k : ℕ) (j : J) :=
  k+∑ q : D.Port j, base q.1.1

omit [Fintype J] [Nonempty J] [Fintype H] [DecidableEq H] [Nonempty H] in
theorem headerWidth_eq : B.arity=headerWidth D base k j := by
  unfold Header.arity headerWidth
  rw [B.ports.sum_comp (fun q => base q.1.1)]

/-- All parameters of this tariff are attributes of one fixed tile. -/
def portTariff (D : PortGraph J E) (P : PortGraph J S) (base : E → ℕ) (k s d : ℕ) (j : J) :=
  let b := headerWidth D base k j
  let e := Fintype.card (P.Port j)
  partyJoinCoefficient b k s e d+(e*k+b+e*d)

def tileTariff (D : PortGraph J E) (P : PortGraph J S) (base : E → ℕ) (k s d : ℕ) :=
  1+Fintype.card S*(d+k)+Fintype.card J*(∑ j, portTariff D P base k s d j)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_join_le : (T).siteCost+(T).rows ≤ partyJoinCoefficient B.arity k s e d*L := by
  obtain ⟨size,maps,nodes⟩ := party_resources D G j base B sa sw fits M id z
  have copies := rowCopies_le (party_within D G j base B sa sw fits M id z
    (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d)))
  rw [show partyJoinCoefficient B.arity k s e d*L =
    4*(partyCoefficient B.arity k s e d*L)+(5+s+e)*L+partyPinCoefficient B.arity k s e d*L by unfold partyJoinCoefficient; ring]
  unfold siteCost
  omega

include sa in
omit [Fintype J] [Nonempty J] [Fintype H] [DecidableEq H] [Nonempty H] in
theorem port_charge_le :
    partyJoinCoefficient B.arity k s e d*L+(r*(e*k)+(r*B.arity+e*(r*d))) ≤ portTariff D (ports G) base k s d j*L := by
  have ne : e=Fintype.card ((ports G).Port j) := by simpa using Fintype.card_congr sa
  have lt : r ≤ L := (Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ (by positivity))
  dsimp only [portTariff]
  rw [←headerWidth_eq D j base B, ←ne,
    Nat.add_mul (partyJoinCoefficient B.arity k s e d) (e*k+B.arity+e*d) L]
  apply Nat.add_le_add_left
  calc
    r*(e*k)+(r*B.arity+e*(r*d)) = (e*k+B.arity+e*d)*r := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lt

omit [Fintype J] [Nonempty J] [DecidableEq H] in
theorem directParty_cost :
    (directParty D G j w base B sa sw fits M id z (partialInput F (r*d) (siteHeight r d))
      (partialInput F r (siteHeight r d)) old fresh).siteCost ≤ (1+portTariff D (ports G) base k s d j)*L := by
  rw [directParty,siteCost_join,Fin.sum_univ_one]
  have h := party_join_le D G j base B sa sw fits M id z
  have a := port_charge_le (r:=r) (d:=d) (s:=s) D G j base B sa
  have l : 1 ≤ L := Nat.succ_le_of_lt (by positivity : 0 < L)
  calc
    _ ≤ 1+(partyJoinCoefficient B.arity k s e d*L+(r*(e*k)+(r*B.arity+e*(r*d)))) :=
      Nat.add_le_add_left (Nat.add_le_add_right h _) _
    _ ≤ _ := by
      rw [Nat.add_mul 1 (portTariff D (ports G) base k s d j) L,Nat.one_mul]
      exact Nat.add_le_add l a

variable {Z : Type} [Fintype Z] [DecidableEq Z] {c a : ℕ}
  (place : J → Z) (v : Z) (code : H ↪ Fin (2^k))
  (edges : Fin a ≃ Absorbed (ports G) place v) (parts : Fin c ≃ {j // place j=v})
  {deg nr : Fin c → ℕ} (supply : ∀ i, Fin (deg i) ≃ (ports G).Port (parts i).val)
  (demand : ∀ i, Fin (nr i) ≃ D.Port (parts i).val) (cap : ∀ y f, sw y f ≤ d)
  (oldPins : ∀ i, (q : D.Port (parts i).val) → Fin (w q.1.1) → BitSource (order G place v sw z edges (k:=k)).bits p)
  (crossPins : (x : ExternalAt (ports G) place v) → Fin (histWidth sw z x.val.val+r*k) → Fin p)

omit [Fintype Z] [Nonempty J] [DecidableEq H] in
theorem occupied_cost :
    (occupiedTree D G place v w base sw code id z edges parts supply demand (fun _ y _ => cap y _)
      M (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d)) oldPins crossPins).siteCost ≤
      tileTariff D (ports G) base k s d*L := by
  let nt := ∑ j, portTariff D (ports G) base k s d j
  have ha : a ≤ Fintype.card S := by
    simpa using Fintype.card_le_of_injective (fun i : Fin a => (edges i).val) (Subtype.val_injective.comp edges.injective)
  have hc : c ≤ Fintype.card J := by
    simpa using Fintype.card_le_of_injective (fun i : Fin c => (parts i).val) (Subtype.val_injective.comp parts.injective)
  have lt : r ≤ L := (Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hp : 1 ≤ L := Nat.succ_le_of_lt (by positivity : 0 < L)
  have hidden : (order G place v sw z edges (k:=k)).bits ≤ Fintype.card S*(d+k)*L := by
    change (∑ i : Fin a, (histWidth sw z (edges i).val+r*k)) ≤ _
    calc
      _ ≤ ∑ _ : Fin a, (d+k)*L := by
        apply Finset.sum_le_sum
        intro i _
        have h := FixedMotifMaxWidth.histWidth_le sw z (edges i).val d (fun y => cap y _)
        calc
          _ ≤ r*d+r*k := Nat.add_le_add_right h _
          _ = (d+k)*r := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ lt
      _ = a*((d+k)*L) := by simp []
      _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ ha
  apply (occupiedTree_native_cost D G place v w base sw code id z edges parts supply demand (fun _ y _ => cap y _)
    M oldPins crossPins).trans
  have parties : (∑ i, (partyJoinCoefficient (hd D base code parts demand i).arity k s (deg i) d*L+
        (r*(deg i*k)+(r*(hd D base code parts demand i).arity+deg i*(r*d))))) ≤ Fintype.card J*nt*L := by
    calc
      _ ≤ ∑ _ : Fin c, nt*L := by
        apply Finset.sum_le_sum
        intro i _
        apply (port_charge_le (r:=r) (d:=d) (s:=s) D G (parts i).val base (hd D base code parts demand i) (supply i)).trans
        exact Nat.mul_le_mul_right _ (Finset.single_le_sum (f:=portTariff D (ports G) base k s d)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (parts i).val))
      _ = c*(nt*L) := by simp []
      _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hc
  change _ ≤ (1+Fintype.card S*(d+k)+Fintype.card J*nt)*L
  calc
    _ ≤ Fintype.card S*(d+k)*L + L + Fintype.card J*nt*L :=
      Nat.add_le_add (Nat.add_le_add hidden hp) parties
    _ = _ := by ring

end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
