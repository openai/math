import OAI.ThreeFlat.Diagonal.HistoryPartyTrees
import OAI.ThreeFlat.Diagonal.HistoryPostorder
import OAI.ThreeFlat.Diagonal.HistogramPartyBudget

namespace OAI
/-! # Footprint of the postorder histogram party tree

Both batches write one pin-map word per child input. The root pair writes
another map for every public input of its two child batches.
-/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open MotifOrderedCells MotifOuterTerms MotifNativeCompactors HistogramTileNetwork LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} {a b r d e s p h c : ℕ}

theorem records_eq_nodes (T : Tree F p) : T.footprint.records = T.nodes := by
  induction T with
  | atom => rfl
  | join h c arity wire child ih => simp only [footprint,nodes,ih,Nat.add_comm]

theorem tasks_eq_commands (T : Tree F p) : T.footprint.tasks = T.commands := by
  induction T with
  | atom => rfl
  | join h c arity wire child ih => simp [footprint,commands,ih,Finset.sum_add_distrib]

theorem batch_pins {arity : Fin c → ℕ} (N : ∀ i, BitNetwork F (arity i))
    (wire : ∀ i, Fin (arity i) → BitSource h p) :
    (batch N wire).footprint.pins = ∑ i, arity i := by simp [batch,footprint]

theorem batch_nodes {arity : Fin c → ℕ} (N : ∀ i, BitNetwork F (arity i))
    (wire : ∀ i, Fin (arity i) → BitSource h p) :
    (batch N wire).nodes = 1+c := by simp [batch,nodes]

theorem pair_pins (A : Tree F a) (B : Tree F b) :
    (pair A B).footprint.pins = A.footprint.pins+B.footprint.pins+(a+b) := by
  rw [pair,footprint]
  simp only [Fin.sum_univ_two]; rfl

theorem pair_nodes (A : Tree F a) (B : Tree F b) :
    (pair A B).nodes = 1+(A.nodes+B.nodes) := by
  rw [pair,nodes,Fin.sum_univ_two]; rfl

theorem pair_rows (A : Tree F a) (B : Tree F b) :
    (pair A B).rows = A.rows+B.rows := by
  rw [pair,rows,Fin.sum_univ_two]; rfl

theorem pair_bits (A : Tree F a) (B : Tree F b) :
    (pair A B).bits = A.bits+B.bits := by
  rw [pair,bits,Fin.sum_univ_two,Nat.zero_add]; rfl

theorem pair_within {k : ℕ} {A : Tree F a} {B : Tree F b} (hA : Within k A) (hB : Within k B) :
    Within (k+1) (pair A B) := by
  unfold pair
  apply Within.join
  intro i
  fin_cases i
  · exact hA
  · exact hB

theorem batch_within {arity : Fin c → ℕ} (N : ∀ i, BitNetwork F (arity i))
    (wire : ∀ i, Fin (arity i) → BitSource h p) : Within 1 (batch N wire) :=
  Within.join fun i => Within.atom 0 (N i)

variable [CommRing F]

theorem tiled_pins {H : Type*} (K : Tile F H e d b) (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    (tiled K C).footprint.pins = r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)) := by
  rw [tiled,batch_pins,Fin.sum_univ_add]
  simp [pieces]

theorem admission_pins (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin s)
    (C : BitNetwork F (r+(r+r))) (v : Histogram (Fin s) r) :
    (admission good letter C v).footprint.pins = r*(b+s)+s*(r+(r+r)) := by
  rw [admission,batch_pins,Fin.sum_univ_add]
  simp [MotifSelectorChecks.components]

/-- Per-copy coefficient of all map words from the two levels. -/
def partyPinCoefficient (b k s e d : ℕ) := 2*(e*k)+4*s+2*b+6*(e*d)

variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k n : ℕ}
  (D : PortGraph J E) (G : Supply J S) (j : J) (base : E → ℕ)
  (B : Header (D.Port j) H (fun q => base q.1.1) k n) (sa : Fin e ≃ (ports G).Port j)
  (sw : H → S → ℕ) (fits : ∀ z a, sw z (sa a).1.1 ≤ d)
  (M : ∀ z v, D.State (fun a => Fin (2^base a)) v → (ports G).State (fun a => Fin (2^sw z a)) v → F)
  (id : H ≃ Fin s) (z : Histogram H r)
  (C : BitNetwork F ((r*d)+(r*d+r*d))) (count : BitNetwork F (r+(r+r)))

local notation "T" => party D G j base B sa sw fits M id z C count

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_pinWords : (T).footprint.pins = r*partyPinCoefficient B.arity k s e d := by
  rw [party,pair_pins,admission_pins,tiled_pins,partyPinCoefficient]
  ring

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_nodes : (T).nodes = 3+2*r+s+e := by
  rw [party,pair_nodes,admission,tiled,batch_nodes,batch_nodes]
  omega

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_within : Within 2 T := pair_within (batch_within ..) (batch_within ..)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_rows_bits :
    (T).rows+(T).bits = (partyNetwork D G j base B sa sw fits M id z C count).cells +
      (partyNetwork D G j base B sa sw fits M id z C count).internal := by
  rw [party,pair_rows,pair_bits]
  simp only [←compiled_rows,←compiled_bits,admission_compile,tiled_compile,
    partyNetwork,BitNetwork.Ordered.pair_cells,BitNetwork.Ordered.pair_hidden]; rfl

local notation "P" => party D G j base B sa sw fits M id z
  (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d))
local notation "L" => ((r+1)*(siteHeight r d+1)^3)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_resources :
    (P).rows+(P).bits ≤ partyCoefficient B.arity k s e d*L ∧
    (P).footprint.pins ≤ partyPinCoefficient B.arity k s e d*L ∧
    (P).nodes ≤ (5+s+e)*L := by
  have hr : r ≤ L := (Nat.le_succ r).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hp : 1 ≤ L := Nat.succ_le_of_lt (by positivity : 0 < L)
  refine ⟨?_,?_,?_⟩
  · rw [party_rows_bits]
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
      partyNetwork_size D G j base B sa sw fits M id z
  · rw [party_pinWords,Nat.mul_comm r]
    exact Nat.mul_le_mul_left _ hr
  · rw [party_nodes]
    have small := Nat.mul_le_mul_left 2 hr
    have fixed := Nat.mul_le_mul_left (3+s+e) hp
    calc
      _ ≤ (3+s+e)*L + 2*L := by simp only [Nat.mul_one] at fixed; omega
      _ = _ := by ring

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- All four resident streams are charged, including both five-word task
records and seven-word driver commands. -/
theorem party_footprint :
    (P).footprint.streams + (P).footprint.pins + 4*(P).footprint.records + 12*(P).footprint.tasks ≤
      (12*partyCoefficient B.arity k s e d + partyPinCoefficient B.arity k s e d + 16*(5+s+e))*L := by
  obtain ⟨size,maps,nodes⟩ := party_resources D G j base B sa sw fits M id z
  have copies := rowCopies_le (party_within D G j base B sa sw fits M id z
    (partialInput F (r*d) (siteHeight r d)) (partialInput F r (siteHeight r d)))
  have commands := (P).command_count
  rw [footprint_streams,records_eq_nodes,tasks_eq_commands]
  rw [show (12*partyCoefficient B.arity k s e d + partyPinCoefficient B.arity k s e d + 16*(5+s+e))*L =
      12*(partyCoefficient B.arity k s e d*L)+partyPinCoefficient B.arity k s e d*L+16*((5+s+e)*L) by ring]
  omega

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- Scheduled row work together with a specified cost for generating each pin-map word. -/
theorem party_scheduledWork (setup mapCost : ℕ) :
    (P).scheduledWork 2 setup + mapCost*(P).footprint.pins ≤
      ((10000+25+1016*2+setup)*(partyCoefficient B.arity k s e d+5+s+e) +
        mapCost*partyPinCoefficient B.arity k s e d)*L := by
  obtain ⟨size,maps,nodes⟩ := party_resources D G j base B sa sw fits M id z
  have work : (P).nodes+(P).rows+(P).bits ≤ (partyCoefficient B.arity k s e d+5+s+e)*L := by
    rw [show (partyCoefficient B.arity k s e d+5+s+e)*L =
      partyCoefficient B.arity k s e d*L + (5+s+e)*L by ring]
    omega
  unfold scheduledWork
  calc
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ work) (Nat.mul_le_mul_left _ maps)
    _ = _ := by ring

end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
