import OAI.Computability.MultitapeWeakETH.TraceNetwork
import OAI.Computability.MultitapeWeakETH.Deadline
import OAI.Computability.MultitapeWeakETH.Trace

/-! # Tape-block alphabets and the participating blocks of each stage -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open IntegerMultiplication
open scoped Classical
noncomputable section

variable (M : Machine)

local instance : Fintype M.Tapes := @Fintype.ofFinite _ M.tapesFinite
local instance : Fintype M.Alphabet := @Fintype.ofFinite _ M.alphabetFinite
local instance : Fintype M.State := @Fintype.ofFinite _ M.stateFinite

/-- The extra register stores the phase, state and head offsets at a boundary. -/
abbrev Key := Option (M.Tapes × ℤ)

def Value (b : ℕ) : Key M → Type
  | none => Bool × M.State × (M.Tapes → Fin b)
  | some _ => Fin b → M.Alphabet

def widthFactor := 1 + Fintype.card M.State + Fintype.card M.Tapes + Fintype.card M.Alphabet

/-- One factor depending only on the machine suffices for both kinds of wire. -/
def pack {b : ℕ} (hb : 0 < b) (i : Key M) : Value M b i ↪ Word (widthFactor M * b) := by
  cases i with
  | none =>
    change (Bool × M.State × (M.Tapes → Fin b)) ↪ _
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simp only [Word,Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
    let q := Fintype.card M.State
    let h := Fintype.card M.Tapes
    change 2 * (q * b^h) ≤ 2 ^ (widthFactor M * b)
    calc
      _ ≤ 2 * (2^q * (2^b)^h) := by gcongr <;> exact Nat.lt_two_pow_self.le
      _ = 2^(1+q+b*h) := by rw [pow_add,pow_add,pow_one,pow_mul]; ring
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [widthFactor,q,h]
        nlinarith [Nat.mul_le_mul_right (1+Fintype.card M.State) hb]
  | some cell =>
    change (Fin b → M.Alphabet) ↪ _
    apply Classical.choice
    apply Function.Embedding.nonempty_of_card_le
    simp only [Word,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
    calc
      _ ≤ (2 ^ Fintype.card M.Alphabet)^b := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2^(Fintype.card M.Alphabet * b) := (pow_mul ..).symm
      _ ≤ _ := by unfold widthFactor; gcongr; omega

/-- Each head supplies three candidate blocks, plus the one shared controller. -/
def epochKeys (base : M.Tapes → ℤ) : Finset (Key M) :=
  insert none (Finset.univ.biUnion fun i : M.Tapes =>
    {some (i,base i-1),some (i,base i),some (i,base i+1)})

theorem epochKeys_card (base : M.Tapes → ℤ) :
    (epochKeys M base).card ≤ 3 * Fintype.card M.Tapes + 1 := by
  unfold epochKeys
  apply (Finset.card_insert_le ..).trans
  apply Nat.add_le_add_right
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _ : M.Tapes, 3 := Finset.sum_le_sum fun _ _ => by
      exact (Finset.card_insert_le ..).trans
        (Nat.add_le_add_right ((Finset.card_insert_le ..).trans (by simp)) _)
    _ = _ := by simp [Nat.mul_comm]

theorem mem_epochKeys {base : M.Tapes → ℤ} {i : M.Tapes} {j : ℤ} (h : |j-base i| ≤ 1) :
    some (i,j) ∈ epochKeys M base := by
  have h' := abs_le.mp h
  have cases : j = base i-1 ∨ j = base i ∨ j = base i+1 := by omega
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  exact ⟨i,Finset.mem_univ _,by rcases cases with e|e|e <;> simp [e]⟩

/-- The high-address endpoint of a big-endian external block fixes its two
candidate physical blocks even when the output starts at a negative address. -/
def ioKeys (tape : M.Tapes) (start : ℤ) (n b j : ℕ) : Finset (Key M) :=
  let top := (start + n - 1 - (j:ℤ)*b) / (b:ℤ)
  {some (tape,top),some (tape,top-1)}

theorem ioKeys_card (tape : M.Tapes) (start : ℤ) (n b j : ℕ) :
    (ioKeys M tape start n b j).card ≤ 2 :=
  (Finset.card_insert_le ..).trans (by simp)

theorem mem_ioKeys {n b : ℕ} (hb : 0 < b) (i : Fin n) (start : ℤ) (tape : M.Tapes) :
    some (tape,(start + i.val)/(b:ℤ)) ∈ ioKeys M tape start n b (block b i) := by
  let r := (n-1-i.val)%b
  have bound : r < b := Nat.mod_lt _ hb
  have div := Nat.mod_add_div (n-1-i.val) b
  have sub : (n-1-i.val : ℕ) + i.val + 1 = n := by omega
  have body : r + b * block b i + i.val + 1 = n := by
    change (n-1-i.val)%b + b*((n-1-i.val)/b) + i.val + 1 = n
    omega
  have castBody := congrArg (fun a : ℕ => (a:ℤ)) body
  push_cast at castBody
  have eq : start + n - 1 - (block b i:ℤ)*b = start + i.val + r := by linarith [mul_comm (block b i:ℤ) (b:ℤ)]
  have pos : 0 < (b:ℤ) := by exact_mod_cast hb
  have h₁ := Int.ediv_le_ediv pos (show start + i.val ≤ start + i.val + r by omega)
  have h₂ := Int.ediv_le_ediv pos (show start + i.val + r ≤ start + i.val + b by omega)
  rw [Int.add_ediv_of_dvd_right (dvd_refl _),Int.ediv_self pos.ne'] at h₂
  have choices : (start+i.val)/(b:ℤ) = (start+i.val+r)/(b:ℤ) ∨
      (start+i.val)/(b:ℤ) = (start+i.val+r)/(b:ℤ)-1 := by omega
  simpa only [ioKeys,eq,Finset.mem_insert,Finset.mem_singleton,Option.some.injEq,Prod.mk.injEq,
    true_and] using choices

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
