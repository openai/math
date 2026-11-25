import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI
/-! # Contraction of the two port copies of each surviving stack wire -/

noncomputable section
namespace Hierarchy.ProtocolStackContraction
open scoped Classical BigOperators

variable {G X F : Type*} [Fintype G] [Fintype X] [CommSemiring F] {D : ℕ}
    {size : G → ℕ} (place : ∀ g, Bool → Fin (size g) ↪ Fin D)

abbrev Edge (size : G → ℕ) := (g : G) × Fin (size g)
abbrev Slot (G : Type*) (D : ℕ) := Option G × Bool × Fin D

/-- Both ends of each surviving wire carry its label; padding, including
the unused group, takes the distinguished blank word. -/
def encode (blank : X) (wire : Edge size → X) : Slot G D → X
  | (none,_,_) => blank
  | (some g,b,i) => Function.extend (place g b) (fun j => wire ⟨g,j⟩) (fun _ => blank) i

omit [Fintype G] [Fintype X] in
@[simp] theorem encode_active (blank : X) (wire : Edge size → X)
    (g : G) (b : Bool) (u : Fin (size g)) :
    encode place blank wire (some g,b,place g b u) = wire ⟨g,u⟩ := by
  exact (place g b).injective.extend_apply (fun j => wire ⟨g,j⟩) (fun _ => blank) u

def Padding (blank : X) (slots : Slot G D → X) : Prop :=
  (∀ b i, slots (none,b,i)=blank) ∧
  ∀ g b i, i ∉ Set.range (place g b) → slots (some g,b,i)=blank

def Linked (slots : Slot G D → X) : Prop :=
  ∀ g u, slots (some g,true,place g true u)=slots (some g,false,place g false u)

omit [Fintype G] [Fintype X] in
theorem encoded_valid (blank : X) (wire : Edge size → X) :
    Padding place blank (encode place blank wire) ∧ Linked place (encode place blank wire) := by
  refine ⟨⟨fun _ _ => rfl,?_⟩,fun g u => by simp⟩
  intro g b i h
  exact Function.extend_apply' (fun j => wire ⟨g,j⟩) (fun _ => blank) i h

omit [Fintype G] [Fintype X] in
theorem encode_injective (blank : X) : Function.Injective (encode place blank) := by
  intro a b eqn
  funext x
  rcases x with ⟨g,u⟩
  simpa only [encode_active] using congrFun eqn (some g,false,place g false u)

omit [Fintype G] [Fintype X] in
theorem exists_encode_of_valid (blank : X) (s : Slot G D → X)
    (p : Padding place blank s) (l : Linked place s) :
    ∃ a : Edge size → X, encode place blank a=s := by
  classical
  let a (x : Edge size) := s (some x.1,false,place x.1 false x.2)
  refine ⟨a,?_⟩
  funext x
  rcases x with ⟨_|g,b,i⟩
  · exact (p.1 b i).symm
  · by_cases active : i ∈ Set.range (place g b)
    · obtain ⟨u,rfl⟩ := active
      rw [encode_active]
      cases b with
      | false => rfl
      | true => exact (l g u).symm
    · exact (Function.extend_apply' (fun j => a ⟨g,j⟩) (fun _ => blank) i active).trans (p.2 g b i active).symm

/-- Summing over independent half-edge words and checking the padded slots
recovers exactly one extension of each assignment to active wires. -/
theorem contract (blank : X) (rest : (Slot G D → X) → F) :
    (∑ s, (if Linked place s then (1:F) else 0) *
      (if Padding place blank s then rest s else 0)) =
      ∑ a : Edge size → X, rest (encode place blank a) := by
  classical
  let emb : (Edge size → X) ↪ (Slot G D → X) := ⟨encode place blank,encode_injective place blank⟩
  let value (s : Slot G D → X) := (if Linked place s then (1:F) else 0) *
    (if Padding place blank s then rest s else 0)
  have valid (a : Edge size → X) : value (emb a) = rest (encode place blank a) := by
    obtain ⟨p,l⟩ := encoded_valid place blank a
    simp [value,emb,p,l]
  have covers (s : Slot G D → X) (p : Padding place blank s) (l : Linked place s) :
      s ∈ Finset.univ.map emb := by
    obtain ⟨a,eqn⟩ := exists_encode_of_valid place blank s p l
    exact Finset.mem_map.mpr ⟨a,Finset.mem_univ _,eqn⟩
  change (∑ s, value s)=_
  calc
    _ = ∑ s ∈ Finset.univ.map emb, value s := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro s _ missing
      by_cases p : Padding place blank s
      · have l : ¬Linked place s := fun h => missing (covers s p h)
        simp [value,l]
      · simp [value,p]
    _ = _ := by rw [Finset.sum_map]; exact Finset.sum_congr rfl (fun a _ => valid a)

/-- Reorder the half-edge slots for each local table. A missing slot reads
the blank word; the side bit specifies which copy of a real edge is read. -/
def tableRead {R : Type*} (arity : R → ℕ)
    (ports : ∀ r, Fin (arity r) → Option (Bool × Edge size))
    (blank : X) (s : Slot G D → X) (r : R) (j : Fin (arity r)) : X :=
  match ports r j with
  | none => blank
  | some (b,x) => s (some x.1,b,place x.1 b x.2)

/-- The lookup key at each occurrence is its ordered tuple of wire labels.
Zero-arity occurrences contribute exactly their scalar table entry. -/
theorem table_contraction {R : Type*} [Fintype R] (arity : R → ℕ)
    (ports : ∀ r, Fin (arity r) → Option (Bool × Edge size))
    (blank : X) (table : ∀ r, (Fin (arity r) → X) → F) :
    (∑ s, (if Linked place s then (1:F) else 0) *
      (if Padding place blank s then ∏ r, table r (tableRead place arity ports blank s r) else 0)) =
      ∑ wire : Edge size → X, ∏ r, table r (fun j => (ports r j).elim blank (fun x => wire x.2)) := by
  rw [contract]
  apply Finset.sum_congr rfl
  intro wire _
  apply Finset.prod_congr rfl
  intro r _
  congr 1
  funext j
  unfold tableRead
  cases ports r j with
  | none => rfl
  | some y => rcases y with ⟨b,x⟩; exact encode_active place blank wire x.1 b x.2

/-- The finite table menu may be valued over an arbitrary field.  Only
the bounded multiplicity of each shared entry has to be communicated. -/
theorem table_histogram {R K : Type*} [Fintype R] [Fintype K]
    (key : R → K) (scalar : K → F) :
    (∏ r, scalar (key r)) =
      ∏ k, scalar k ^ (Finset.univ.filter fun r => key r=k).card := by
  classical
  simpa only [Finset.prod_const] using (Finset.prod_fiberwise' Finset.univ key scalar).symm

private theorem lowBits (v n : ℕ) :
    (∑ i : Fin n, (v.testBit i.val).toNat*2^i.val)=v%2^n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih,Nat.toNat_testBit,Nat.mod_pow_succ,Nat.mul_comm (v / 2^n % 2)]

/-- A bit of a class count selects an ordinary scalar power, also for zero
scalar and zero occurrences. -/
theorem power_bits (scalar : F) (v n : ℕ) (fit : v<2^n) :
    scalar^v=∏ j : Fin n, if v.testBit j.val then scalar^(2^j.val) else 1 := by
  calc
    _ = scalar ^ (∑ j : Fin n, (v.testBit j.val).toNat*2^j.val) := by
      rw [lowBits,Nat.mod_eq_of_lt fit]
    _ = _ := by
      rw [←Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      cases v.testBit j.val <;> simp

theorem table_histogram_bits {R K : Type*} [Fintype R] [Fintype K]
    (key : R → K) (scalar : K → F) (n : ℕ) (fit : Fintype.card R<2^n) :
    (∏ r, scalar (key r)) = ∏ k, ∏ j : Fin n,
      if (Finset.univ.filter fun r => key r=k).card.testBit j.val then scalar k^(2^j.val) else 1 := by
  rw [table_histogram key scalar]
  apply Finset.prod_congr rfl
  intro k _
  apply power_bits
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt (by simpa using fit)

end Hierarchy.ProtocolStackContraction

end
end OAI
