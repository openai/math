import OAI.ThreeFlat.Diagonal.CompressorTagScan
import OAI.ThreeFlat.Diagonal.CompressorLaneSplit
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Cost and packing data for the canonical base scans -/

namespace ThreeFlat.Diagonal.CompressorPacking.Ordered
open Computability.VPVNP.Compression

variable {A V Tag : Type*} {d m n : ℕ}

/-- Number of equality tests in a left-to-right membership search. -/
def membershipChecks [DecidableEq A] (a : A) : List A → ℕ
  | [] => 0
  | b::bs => if a = b then 1 else 1 + membershipChecks a bs

theorem membershipChecks_le [DecidableEq A] (a : A) (bs : List A) :
    membershipChecks a bs ≤ bs.length := by
  induction bs with
  | nil => simp [membershipChecks]
  | cons b bs ih => simp only [membershipChecks,List.length_cons]; split <;> omega

/-- Comparison count of `pick` on the same inputs, stopping after its
first successful candidate. -/
def choiceChecks [DecidableEq A] (banned : List A) : List A → ℕ
  | [] => 0
  | a::xs => membershipChecks a banned + (if a ∈ banned then choiceChecks banned xs else 0)

theorem choiceChecks_le [DecidableEq A] (banned xs : List A) :
    choiceChecks banned xs ≤ xs.length*banned.length := by
  induction xs with
  | nil => simp [choiceChecks]
  | cons a xs ih =>
    have h := membershipChecks_le a banned
    simp only [choiceChecks,List.length_cons,Nat.succ_mul]
    split <;> omega

/-- Total comparisons on the successive table states, including vertices
whose chosen value happens to agree with their old value. -/
def scanChecks [DecidableEq V] [DecidableEq A] (choices : List A) (fallback : A)
    (ban : V → (V → A) → List A) : List V → (V → A) → ℕ
  | [],_ => 0
  | x::xs,f => let b := ban x f
    choiceChecks b choices + scanChecks choices fallback ban xs (Function.update f x (pick b fallback choices))

theorem scanChecks_le [DecidableEq V] [DecidableEq A] (choices : List A) (fallback : A)
    (ban : V → (V → A) → List A) (K : ℕ) (small : ∀ x f, (ban x f).length ≤ K)
    (visits : List V) (f : V → A) :
    scanChecks choices fallback ban visits f ≤ visits.length * (choices.length * K) := by
  induction visits generalizing f with
  | nil => simp [scanChecks]
  | cons x xs ih =>
    simp only [scanChecks,List.length_cons,Nat.succ_mul]
    rw [Nat.add_comm (xs.length * _)]
    exact Nat.add_le_add ((choiceChecks_le _ _).trans (Nat.mul_le_mul_left _ (small x f))) (ih _)

variable [DecidableEq V] [AddCommGroup Tag] [DecidableEq Tag]

theorem color_checks (G : SlotGraph V d) (order : Fin m ≃ V) :
    scanChecks (List.ofFn (Equiv.refl (Fin (2*d+1)))) 0 (colorBan G) (List.ofFn order) (fun _ => 0) ≤
      m*((2*d+1)*(2*d)) := by
  simpa only [List.length_ofFn] using scanChecks_le (List.ofFn (Equiv.refl (Fin (2*d+1)))) 0 (colorBan G) (2*d)
    (by intro x f; simp [colorBan]) (List.ofFn order) (fun _ => 0)

theorem tag_checks (G : SlotGraph V d) (shift : V × Fin d → Tag) (order : Fin m ≃ V)
    (rank : Fin n ≃ Tag) :
    scanChecks (List.ofFn rank) 0 (tagBan G shift) (List.ofFn order) (fun _ => 0) ≤
      m*(n*(2*d*((d+1)+(d+1)^2))) := by
  simpa only [List.length_ofFn] using scanChecks_le (List.ofFn rank) 0 (tagBan G shift) _
    (fun x f => (tagBan_length G shift x f).le) (List.ofFn order) (fun _ => 0)

/-- Use the deterministic scans to construct all tag and color fields of
the packing data from an indexed graph and the canonical finite ranks. -/
def binaryPacking {s remain : ℕ} [Fintype V] (order : Fin m ≃ V)
    (G : LiftedSlots V (2^s) (BitWord ((2*(2^s)+1) + (s + (tagBits (2^s) + remain))))) :
    PackingData V (BitWord s) (BitWord (tagBits (2^s))) (BitWord remain) (2^s) (2*(2^s)+1) :=
  let U := changeLanes G (laneSplit _ _ _ _)
  let shifts := fun e => (U.displacement e).2.2.1
  let rank : Fin (2^(tagBits (2^s))) ≃ BitWord (tagBits (2^s)) := finFunctionFinEquiv.symm
  { slots := G.base
    color := colors G.base order
    proper := colors_proper G.base order
    slotLabel := finFunctionFinEquiv
    offset := offsets G.base shifts order rank
    bitShift e := (U.displacement e).1
    slotShift e := (U.displacement e).2.1
    siteShift e := (U.displacement e).2.2 }

theorem binaryPacking_conditions {s remain : ℕ} [Fintype V] (order : Fin m ≃ V)
    (G : LiftedSlots V (2^s) (BitWord ((2*(2^s)+1) + (s + (tagBits (2^s) + remain))))) :
    let P := binaryPacking order G
    TagConditions P.slots (fun e => (P.siteShift e).1) P.offset := by
  apply offsets_valid
  simpa only [BitWord,Fintype.card_fun,Fintype.card_fin,ZMod.card] using tagBits_fit (2^s)

end ThreeFlat.Diagonal.CompressorPacking.Ordered

end OAI
