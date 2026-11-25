import OAI.Computability.NearSquareRoot.CRTPositionDescriptorEval
import OAI.Computability.NearSquareRoot.CRTPositionLayerTable
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # Preparing the directed XOR reads for all three address chunks

The first tuple contains both read directions for each of the ordered pairs
of chunks (0,1), (0,2), and (1,2). The second contains the borrowing reads
for transpositions within each of the three chunks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionPreparation

set_option synthInstance.maxSize 5000

open IntegerMultiplication.Code
open Reflections

/-- Width of a contiguous equal-sized chunk, taken by P192's unary divider. -/
def third (t : Tally) : Tally := (IntegerMultiplication.Staff.quot (t,tally 3)).1

@[fun_prop] theorem poly_third : Poly third :=
  ((Easy.identity.poly.pair (IntegerMultiplication.Code.Poly.const (tally 3))).compose IntegerMultiplication.Staff.stable_q).fstCompose

theorem third_tally (k : ℕ) : third (tally k) = tally (k/3) :=
  congrArg Prod.fst (IntegerMultiplication.Staff.quot_r k 3)

abbrev ReadTable := List (Option Tally)
abbrev Both := ReadTable × ReadTable
abbrev Borrow := List BorrowPorts
abbrev RoundTables := (Both × Both × Both) × (Borrow × Borrow × Borrow)

def both (q : ChunkQuery) : Both :=
  (crossDescriptor q,crossDescriptor (q.1,q.2.2.1,q.2.1,q.2.2.2))

@[fun_prop] theorem poly_both : Poly both := by unfold both; fun_prop

def twice (m : Tally) : Tally := m ++ m

@[fun_prop] theorem poly_twice : Poly twice := (show Easy twice by unfold twice; fun_prop).poly

def roundTables (z : Tally × Table) : RoundTables :=
  let m := z.1
  let t := z.2
  ((both (m,[],m,t),both (m,[],twice m,t),both (m,m,twice m,t)),
    borrowedDescriptor (m,[],t),borrowedDescriptor (m,m,t),borrowedDescriptor (m,twice m,t))

@[fun_prop] theorem poly_roundTables : Poly roundTables := by unfold roundTables; fun_prop

/-- The first reflection is applied to positions before the second. -/
def bulk (z : Tally × Table) : RoundTables × RoundTables :=
  let tables := prepare z.2
  (roundTables (z.1,tables.1),roundTables (z.1,tables.2))

@[fun_prop] theorem poly_bulk : Poly bulk := by unfold bulk; fun_prop

theorem bulk_correct {k : ℕ} (m : Tally) (p : Equiv.Perm (Fin k)) :
    bulk (m,table p) = (roundTables (m,table (first p)),roundTables (m,table (second p))) := by
  simp only [bulk,prepare_spec]

def portAt {m k : ℕ} (p : Equiv.Perm (Fin k)) (s d : ℕ) (hd : d+m ≤ k) : ReadTable :=
  List.ofFn fun i : Fin m =>
    let y := (p ⟨d+i.val,by omega⟩).val
    if s ≤ y ∧ y < s+m then some (tally (y-s)) else none

def pairAt {m k : ℕ} (p : Equiv.Perm (Fin k)) (s d : ℕ) (hs : s+m ≤ k)
    (hd : d+m ≤ k) : Both := (portAt p s d hd,portAt p d s hs)

def borrowAt {m k : ℕ} (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : ℕ) (hs : s+m ≤ k) : Borrow :=
  let q := withinChunk p hp hs
  List.ofFn fun i : Fin m => (unaryPort (borrowIdRead q i),
    unaryPort (borrowUpRead q i),unaryPort (borrowDownRead q i))

private theorem both_value {k m s d : ℕ} (p : Equiv.Perm (Fin k)) (hs : s+m ≤ k) (hd : d+m ≤ k) :
    both (tally m,tally s,tally d,table p) = pairAt p s d hs hd :=
  Prod.ext (crossDescriptor_value hd p) (crossDescriptor_value hs p)

/-- Specification of every read port in the six chunk matchings for an involution. -/
theorem roundTables_value {k m : ℕ} (hm : 3*m ≤ k) (p : Equiv.Perm (Fin k))
    (hp : Function.Involutive p) :
    roundTables (tally m,table p) =
      ((pairAt (m := m) p 0 m (by omega) (by omega),pairAt (m := m) p 0 (2*m) (by omega) (by omega),
        pairAt (m := m) p m (2*m) (by omega) (by omega)),borrowAt (m := m) p hp 0 (by omega),
        borrowAt (m := m) p hp m (by omega),borrowAt (m := m) p hp (2*m) (by omega)) := by
  have twice_eq : twice (tally m) = tally (2*m) := by
    rw [← recover_tally (twice (tally m))]
    simp [twice,two_mul]
  have h₀ : 0+m ≤ k := by omega
  have h₁ : m+m ≤ k := by omega
  have h₂ : 2*m+m ≤ k := by omega
  change roundTables (tally m,positionImages p) = _
  simp only [roundTables,twice_eq]
  exact Prod.ext
    (Prod.ext (both_value p h₀ h₁) (Prod.ext (both_value p h₀ h₂) (both_value p h₁ h₂)))
    (Prod.ext (borrowedDescriptor_value h₀ p hp)
      (Prod.ext (borrowedDescriptor_value h₁ p hp) (borrowedDescriptor_value h₂ p hp)))

end Controlled.PositionPreparation

end NearSquareRoot
end Computability
end OAI
