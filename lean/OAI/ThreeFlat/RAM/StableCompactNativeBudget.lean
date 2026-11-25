import OAI.ThreeFlat.Routing.StableCompactNative
import OAI.ThreeFlat.RAM.StableCompactAddress

namespace OAI
/-! # Address capacity and program sizes of the native stable compactor -/

namespace ThreeFlat.RAM.StableCompactNativeBudget
open Computability.VPVNP.BurstRAM BitLayout Routing.StableCompactNative
open scoped Fin.CommRing

/-- A common capacity for all row addresses, register addresses, and library indices. -/
def budget (m : ℕ) : ℕ := 2^m * (400000*(m+1)^3)

/-- One fixed 19-bit prefix and four bits per logarithmic level suffice. -/
theorem budget_lt_word (m : ℕ) : budget m < 2^(19+4*m) := by
  have grow : m+1 ≤ 2^m := m.lt_two_pow_self
  calc
    budget m ≤ 2^m * (400000 * (2^m)^3) := by
      unfold budget
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left grow _))
    _ < 2^m * (2^19 * (2^m)^3) := Nat.mul_lt_mul_of_pos_left
      (Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) (by positivity)
    _ = 2^(19+4*m) := by
      rw [←pow_mul]
      rw [show 19+4*m = m+(19+m*3) by omega,pow_add (2:ℕ) m,pow_add (2:ℕ) 19]

variable {F : Type*} [Zero F] [One F] {m w k : ℕ}

theorem capacities (F : Type*) [Zero F] [One F] (m : ℕ) :
    4 ≤ budget m ∧ 2^m ≤ budget m ∧ 8*(template F m).cells ≤ budget m ∧
    4*(network F m).cells ≤ budget m ∧
    2 + (2^m+(2^m+2^m)) + (network F m).internal ≤ budget m := by
  let scale := 2^m*(m+1)^3
  have sites : 2^m ≤ scale := Nat.le_mul_of_pos_right _ (by positivity)
  have localScale : (m+1)^3 ≤ scale := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos m)
  have low : 0 < 2^m := Nat.two_pow_pos m
  have room : budget m = 400000*scale := by simp only [budget,scale]; ac_rfl
  have localCap := (template_cells F m).trans (Nat.mul_le_mul_left 32000 localScale)
  have cellCap : (network F m).cells ≤ 32000*scale := by
    simpa only [scale,Nat.mul_left_comm] using network_cells F m
  have regCap : (network F m).internal ≤ 32000*scale := by
    simpa only [scale,Nat.mul_left_comm] using network_internal F m
  rw [room]
  omega

/-- Every referenced source is the exact natural address of a word in the allocated range. -/
theorem sourceAddress_lt (room : budget m < 2^w)
    (source : BitSource (network F m).internal (2^m+(2^m+2^m))) :
    sourceAddress source < 2^w := by
  have cap := (capacities F m).2.2.2.2
  cases source with
  | hidden i => have := i.isLt; dsimp [sourceAddress,hiddenBase]; omega
  | pin i => have := i.isLt; dsimp [sourceAddress]; omega
  | constant b =>
    have four : 4 < 2^w := (capacities F m).1.trans_lt room
    have one : b.toNat ≤ 1 := by cases b <;> decide
    exact one.trans_lt (lt_trans (by decide : 1 < 4) four)

/-- The one shared scalar table contains one eight-entry row per local template cell. -/
theorem library_count_le (F : Type*) [Zero F] [One F] (m : ℕ) :
    (StableCompactAddress.library (template F m)).count ≤ 32000*(m+1)^3 :=
  template_cells F m

theorem metadataProgram_binds (F : Type*) [Zero F] [One F] (m w k : ℕ) :
    (StableCompactAddress.metadataProgram (w:=w) (k:=k) (template F m)).binds ≤
      768000*(m+1)^3 + 20 := by
  have bound := StableCompactAddress.metadataProgram_binds (w:=w) (k:=k) (template F m)
  have size := template_cells F m
  omega

theorem scalarProgram_binds (m k : ℕ) (code : FieldCode F w) :
    (StableCompactAddress.scalarProgram (k:=k) (template F m) code).binds ≤
      768000*(m+1)^3 + 1 := by
  rw [StableCompactAddress.scalarProgram_binds]
  have size := template_cells F m
  omega

/-- The complete metadata record address fits before the cast to a RAM word. -/
theorem metadataIndex_lt (room : budget m < 2^w) (i : Fin (network F m).cells) (j : Fin 4) :
    4*i.val+j.val < 2^w := by
  have rows := (capacities F m).2.2.2.1
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The complete scalar library address also fits before the cast. -/
theorem scalarIndex_lt (room : budget m < 2^w)
    (t : Fin (StableCompactAddress.library (template F m)).count) (j : Fin 8) :
    8*t.val+j.val < 2^w := by
  have count := (capacities F m).2.2.1
  have ht : t.val < (template F m).cells := t.isLt
  have hj := j.isLt
  omega

/-- Metadata evaluation only requires the single capacity bound for the whole compactor. -/
theorem metadataProgram_eval (i : Fin (network F m).cells) (j : Fin 4)
    (room : budget m < 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) :
    (StableCompactAddress.metadataProgram (template F m)).eval words mem vs =
      if hj : j.val < 3 then ((sourceAddress ((network F m).source i ⟨j.val,hj⟩) : ℕ) : Word w)
      else (((StableCompactAddress.library (template F m)).id i).val : Word w) := by
  obtain ⟨four,sites,libCells,_,_⟩ := capacities F m
  exact StableCompactAddress.metadataProgram_eval _ i j (four.trans_lt room) (sites.trans_lt room)
    (by omega) (metadataIndex_lt (F:=F) (m:=m) room i j) words mem vs arg

/-- Reading the result as a natural gives the original source address or library tag. -/
theorem metadataProgram_eval_val (i : Fin (network F m).cells) (j : Fin 4)
    (room : budget m < 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) :
    ((StableCompactAddress.metadataProgram (template F m)).eval words mem vs).val =
      if hj : j.val < 3 then sourceAddress ((network F m).source i ⟨j.val,hj⟩)
      else ((StableCompactAddress.library (template F m)).id i).val := by
  rw [metadataProgram_eval i j room words mem vs arg]
  by_cases hj : j.val < 3
  · simp only [dite_eq_left hj]
    exact Fin.val_cast_of_lt (sourceAddress_lt (F:=F) (m:=m) room _)
  · simp only [dite_eq_right hj]
    have hId : ((StableCompactAddress.library (template F m)).id i).val < (template F m).cells :=
      ((StableCompactAddress.library (template F m)).id i).isLt
    have cells := (capacities F m).2.2.1
    exact Fin.val_cast_of_lt (by omega)

/-- Scalar table evaluation uses the same word-width hypothesis as the metadata evaluator. -/
theorem scalarProgram_eval (code : FieldCode F w) (t : Fin (StableCompactAddress.library (template F m)).count)
    (j : Fin 8) (room : budget m < 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = ((8*t.val+j.val : ℕ) : Word w)) :
    (StableCompactAddress.scalarProgram (template F m) code).eval words mem vs =
      code.encode ((StableCompactAddress.library (template F m)).table t (bits j.val)) :=
  StableCompactAddress.scalarProgram_eval _ code t j ((capacities F m).2.2.1.trans room.le)
    words mem vs arg

end ThreeFlat.RAM.StableCompactNativeBudget

end OAI
