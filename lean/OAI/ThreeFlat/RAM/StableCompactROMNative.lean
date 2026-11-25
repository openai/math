import OAI.ThreeFlat.RAM.StableCompactROMAddress
import OAI.ThreeFlat.RAM.StableCompactROMPool
import OAI.ThreeFlat.RAM.StableCompactNativeBudget

namespace OAI
/-! # A simultaneous polynomial ROM of physical stable-compactor templates -/

noncomputable section
namespace ThreeFlat.RAM.StableCompactROMNative

open Computability.VPVNP.BurstRAM BitLayout Routing.StableCompactNative Routing.StableCompaction
open StableCompactROMEntries
open scoped Classical Fin.CommRing

variable {F : Type*} [Zero F] [One F] {w k : ℕ}

abbrev size (B : ℕ) := StableCompactROMPool.size B 12
def pageBase (B base m : ℕ) := base + m*StableCompactROMPool.page B 12

/-- The fixed-size page reserved for each possible dyadic exponent. -/
theorem pageBase_eq (B base m : ℕ) :
    pageBase B base m = base + m*(384000*(B+1)^3) := by
  unfold pageBase StableCompactROMPool.page StableCompactROMPool.rows
  ring

theorem size_eq (B : ℕ) : size B = 384000*(B+1)^4 := by
  rw [size,StableCompactROMPool.size_eq]

/-- Degree-40 advice bound for the exponent cutoff in the diagonal construction. -/
theorem size_le_degree_forty (u : ℕ) :
    size (16*u^10) ≤ 384000*17^4*(u+1)^40 := by
  have mono : u^10 ≤ (u+1)^10 := Nat.pow_le_pow_left (Nat.le_succ _) _
  have pos : 0 < (u+1)^10 := Nat.pow_pos (Nat.zero_lt_succ _)
  exact StableCompactROMPool.size_le_of_degree (K:=17) (C:=12) (w:=u) (by omega)

private def count (F : Type*) [Zero F] [One F] (m : ℕ) := (template F m).cells
private theorem cap (F : Type*) [Zero F] [One F] {B : ℕ} (m : Fin (B+1)) :
    count F m ≤ StableCompactROMPool.rows m := template_cells F m

private def wordField (tag : Table F → ℕ) (m : ℕ) (i : Fin (count F m)) (f : Fin 12) : Word w :=
  (field (template F m) tag i f : Word w)

/-- The public words can be appended to any other advice directory. -/
def data (B : ℕ) (tag : Table F → ℕ) : Fin (size B) → Word w :=
  StableCompactROMPool.data B 12 (count F) (wordField tag)

def install (B base : ℕ) (tag : Table F → ℕ) (old : Memory w) : Memory w :=
  StableCompactROMPool.install base (size B) (data B tag) old

def Stores (B base : ℕ) (tag : Table F → ℕ) (mem : Memory w) : Prop :=
  ∀ m : Fin (B+1), StableCompactROMAddress.Stores (template F m) tag (pageBase B base m) mem

theorem data_at (B : ℕ) (tag : Table F → ℕ) (m : Fin (B+1)) (t : Fin (template F m).cells)
    (j : Fin 4) (l : Fin 3) :
    data B tag (StableCompactROMPool.place (count F) (cap F) ⟨m,t,finProdFinEquiv (j,l)⟩) =
      (((entry (template F m) tag t j).word l : ℕ) : Word w) := by
  let localRow : Fin (count F m):=t
  have read:=StableCompactROMPool.data_place (count F) (cap F) (wordField (w:=w) tag) m localRow
    (finProdFinEquiv (m:=4) (n:=3) (j,l))
  exact read.trans (congrArg (fun n : ℕ=>(n:Word w)) (field_at (template F m) tag t j l))

theorem stores_of_read (B base : ℕ) (tag : Table F → ℕ) (mem : Memory w)
    (read : ∀ z : Fin (size B), mem (base+z.val) = data B tag z) :
    Stores B base tag mem := by
  intro m t j l
  let pos : Fin (size B) := StableCompactROMPool.place (count F) (cap F) ⟨m,t,finProdFinEquiv (j,l)⟩
  have flat : (finProdFinEquiv (m:=4) (n:=3) (j,l)).val = 3*j.val+l.val := by
    change l.val+3*j.val = _
    omega
  have addr : base+pos.val = pageBase B base m + 3*(4*t.val+j.val)+l.val := by
    rw [show pos.val = _ from StableCompactROMPool.place_val (count F) (cap F) m t (finProdFinEquiv (j,l))]
    unfold StableCompactROMPool.address pageBase
    rw [flat]
    ring
  rw [←addr,read]
  exact data_at B tag m t j l

theorem install_stores (B base : ℕ) (tag : Table F → ℕ) (old : Memory w) :
    Stores B base tag (install B base tag old) :=
  stores_of_read B base tag _ (StableCompactROMPool.install_at base (data B tag) old)

private theorem page_end (B base : ℕ) (m : Fin (B+1)) :
    pageBase B base m.val + 12*(template F m).cells ≤ base+size B := by
  have rows : (template F m).cells ≤ StableCompactROMPool.rows B := (template_cells F m).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.le_of_lt_succ m.isLt)) 3))
  have bound : 12*(template F m).cells ≤ StableCompactROMPool.page B 12 := by
    simpa only [StableCompactROMPool.page,Nat.mul_comm 12] using Nat.mul_le_mul_left 12 rows
  have pages := Nat.mul_le_mul_right (StableCompactROMPool.page B 12) (Nat.succ_le_of_lt m.isLt)
  rw [Nat.succ_mul] at pages
  unfold pageBase size StableCompactROMPool.size
  omega

/-- The same fixed instructions produce every word for every supported exponent,
logical prefix length, and shared coefficient-table numbering. -/
theorem program_eval (B base : ℕ) (m : Fin (B+1)) (n : ℕ) (hn : n ≤ 2^m.val)
    (tag : Table F → ℕ) (i : Fin (network F m).cells) (j : Fin 4)
    (room : StableCompactNativeBudget.budget m < 2^w) (romroom : base+size B ≤ 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 4 → Word w)
    (key : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) (sites : vs 1 = ((2^m.val : ℕ) : Word w))
    (short : vs 2 = (n : Word w)) (ptr : vs 3 = (pageBase B base m : Word w))
    (stored : Stores B base tag mem) :
    StableCompactROMProgram.program.eval words mem vs =
      if hj : j.val<3 then ((sourceAddress ((restrictRows (network F m) n).source i ⟨j.val,hj⟩) : ℕ) : Word w)
      else (tag ((network F m).table i) : Word w) := by
  have capM := StableCompactNativeBudget.capacities F m
  exact StableCompactROMAddress.program_eval (template F m) tag n _ hn i j (capM.1.trans_lt room)
    (capM.2.1.trans_lt room) (StableCompactNativeBudget.metadataIndex_lt (F:=F) room i j)
    ((page_end (F:=F) B base m).trans romroom) words mem vs key sites short ptr (stored m)

private theorem source_lt {m n : ℕ} (hn : n ≤ 2^m) (room : StableCompactNativeBudget.budget m < 2^w)
    (s : BitSource (network F m).internal (n+(n+n))) : sourceAddress s < 2^w := by
  have capM := (StableCompactNativeBudget.capacities F m).2.2.2.2
  cases s with
  | constant b =>
    have tag : 4<2^w := (StableCompactNativeBudget.capacities F m).1.trans_lt room
    cases b
    · exact (show 0<2^w by omega)
    · exact (show 1<2^w by omega)
  | pin i => have bound := i.isLt; dsimp [sourceAddress]; omega
  | hidden i => have bound := i.isLt; dsimp [sourceAddress,hiddenBase]; omega

/-- With a word-sized field-wide LUT index the decoder returns exact natural addresses. -/
theorem program_eval_val (B base : ℕ) (m : Fin (B+1)) (n : ℕ) (hn : n ≤ 2^m.val)
    (tag : Table F → ℕ) (i : Fin (network F m).cells) (j : Fin 4)
    (room : StableCompactNativeBudget.budget m < 2^w) (romroom : base+size B ≤ 2^w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 4 → Word w)
    (key : vs 0 = ((4*i.val+j.val : ℕ) : Word w)) (sites : vs 1 = ((2^m.val : ℕ) : Word w))
    (short : vs 2 = (n : Word w)) (ptr : vs 3 = (pageBase B base m : Word w))
    (stored : Stores B base tag mem) (tagFits : ∀ tbl, tag tbl < 2^w) :
    (StableCompactROMProgram.program.eval words mem vs).val =
      if hj : j.val<3 then sourceAddress ((restrictRows (network F m) n).source i ⟨j.val,hj⟩)
      else tag ((network F m).table i) := by
  rw [program_eval B base m n hn tag i j room romroom words mem vs key sites short ptr stored]
  by_cases hj : j.val < 3
  · simp only [dite_eq_left hj]
    exact Fin.val_cast_of_lt (source_lt (F:=F) hn room _)
  · simp only [dite_eq_right hj]
    exact Fin.val_cast_of_lt (tagFits _)

end ThreeFlat.RAM.StableCompactROMNative

end
end OAI
