import OAI.ThreeFlat.RAM.ChunkRequestExpr
import OAI.ThreeFlat.Diagonal.TickBitRule
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Two fixed request slots per auxiliary bit -/

namespace ThreeFlat.RAM.TickBitRelation

open Computability.VPVNP.BurstRAM ChunkRequests Diagonal.TickAuxiliary
open scoped Fin.NatCast

/-- An occupied request carries its mode and its expected literal, respectively. -/
def request (r : Rule) (which : Fin 2) : Option (ℕ × ℕ) :=
  match r with
  | .any => none
  | .same => if which = 0 then some (2,0) else none
  | .oldZero => if which = 0 then some (0,0) else none
  | .newZero => if which = 0 then some (1,0) else none
  | .bothZero => if which = 0 then some (0,0) else some (1,0)
  | .zeroOne => if which = 0 then some (0,0) else some (1,1)
  | .oneZero => if which = 0 then some (0,1) else some (1,0)
  | .bothOne => if which = 0 then some (0,1) else some (1,1)

def rowCount (r : Rule) : ℕ :=
  ((request r 0).isSome).toNat + ((request r 1).isSome).toNat

theorem rowCount_le (r : Rule) : rowCount r ≤ 2 := by cases r <;> decide

/-- Tag zero is live. Tag one turns the unused second or first slot into a no-op. -/
def paddedRequest {w : ℕ} (r : Rule) (which : Fin 2) (off : Word w) : Request w :=
  match request r which with
  | none => ⟨1,0,off,0⟩
  | some (mode,expected) => ⟨0,Fin.ofNat _ mode,off,Fin.ofNat _ expected⟩

def bitWord (w : ℕ) (b : Bool) : Word w := if b then 1 else 0

theorem paddedRequest_matches {w : ℕ} (width : 2 < 2^w) (r : Rule)
    (m : Memory w) (oldBase newBase off : Word w) (a b : Bool)
    (old_ok : bitAt m oldBase off = bitWord w a)
    (new_ok : bitAt m newBase off = bitWord w b) :
    (∀ which, rowMatches m (paddedRequest r which off) 0 oldBase newBase) ↔ r.holds a b := by
  have z : (0:Word w).val = 0 := rfl
  have o : (1:Word w).val = 1 := Nat.mod_eq_of_lt (show (1 : ℕ) < 2^w by omega)
  have t : (2:Word w).val = 2 := Nat.mod_eq_of_lt width
  have zo : (0:Word w) ≠ 1 := fun e => by have := congrArg Fin.val e; omega
  have zt : (0:Word w) ≠ 2 := fun e => by have := congrArg Fin.val e; omega
  have ot : (1:Word w) ≠ 2 := fun e => by have := congrArg Fin.val e; omega
  have zero : Fin.ofNat (2^w) 0 = (0:Word w) := rfl
  have one : Fin.ofNat (2^w) 1 = (1:Word w) := rfl
  have two : Fin.ofNat (2^w) 2 = (2:Word w) := rfl
  have cast₀ : ((0:ℕ) : Word w) = 0 := rfl
  have cast₁ : ((1:ℕ) : Word w) = 1 := rfl
  have cast₂ : ((2:ℕ) : Word w) = 2 := rfl
  cases r <;> cases a <;> cases b <;>
    simp [-Fin.ofNat_eq_cast,Fin.forall_fin_succ, paddedRequest, request, rowMatches, Rule.holds,
      old_ok,new_ok,bitWord,zero,one,two,zo,zo.symm,zt,ot,ot.symm]

/-- Slot number is twice the local bit index plus the request number. -/
def rangeRequest {w n : ℕ} (rules : Fin n → Rule) (baseOffset : Word w)
    (z : Fin (n*2)) : Request w :=
  let ij := finProdFinEquiv.symm z
  paddedRequest (rules ij.1) ij.2 (baseOffset + Fin.ofNat _ ij.1.val)

def rangeRows {w n : ℕ} (rules : Fin n → Rule) (baseOffset : Word w) : List (Request w) :=
  List.ofFn (rangeRequest rules baseOffset)

@[simp] theorem rangeRows_length {w n : ℕ} (rules : Fin n → Rule) (baseOffset : Word w) :
    (rangeRows rules baseOffset).length = n*2 := List.length_ofFn

theorem rangeRows_matches {w n : ℕ} (width : 2 < 2^w) (rules : Fin n → Rule)
    (m : Memory w) (oldBase newBase baseOffset : Word w) (a b : Fin n → Bool)
    (old_ok : ∀ j : Fin n, bitAt m oldBase (baseOffset+Fin.ofNat _ j.val) = bitWord w (a j))
    (new_ok : ∀ j : Fin n, bitAt m newBase (baseOffset+Fin.ofNat _ j.val) = bitWord w (b j)) :
    (∀ row ∈ rangeRows rules baseOffset, rowMatches m row 0 oldBase newBase) ↔
      ∀ j, (rules j).holds (a j) (b j) := by
  rw [rangeRows, List.forall_mem_ofFn_iff]
  have localCheck (i : Fin n) := paddedRequest_matches width (rules i) m oldBase newBase
    (baseOffset+Fin.ofNat _ i.val) (a i) (b i) (old_ok i) (new_ok i)
  constructor
  · intro h i
    apply (localCheck i).mp
    intro s
    simpa [rangeRequest] using h (finProdFinEquiv (i,s))
  · intro h z
    obtain ⟨⟨i,s⟩,rfl⟩ := finProdFinEquiv.surjective z
    simpa [rangeRequest] using (localCheck i).mpr (h i) s

end ThreeFlat.RAM.TickBitRelation

end OAI
