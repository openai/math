import OAI.Computability.VPVNP.CompressorShrinkABSliceTable
import OAI.Computability.VPVNP.PairNodeArguments

/-!
# AB demand buffers of a resident shrinking map

The packed descriptor stores a three-word interval for each pair consisting
of a thick old arc and an assigned motif. Its source and target offsets are
relative to the old half-word and the selected AB operand. Each frame copies
a slice from one old half. Taken in old-field order these writes reconstruct
the precise row argument of the matrix at either A or B, even when the two
old halves were guessed independently.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkAB

open BurstRAM Compression Compression.PackingData CompressorRecords
open ShrinkSliceArrays SliceSchedule
open scoped Fin.CommRing

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (width : Arc V H Tag L d c → ℕ) {b : Site V Tag L × Fin d} (m : P.MotifFiber b)

/-- Physical start of the three words in the completed indexed-starts bank. -/
def frame {w : ℕ} (B : Word w) (a : P.ThickFiber b) : ℕ :=
  B.val + (2 ^ c * d / 4) + pieceCount d c +
    3 * ((order b a).val * pieceCount d c + (number b m).val)

/-- The physical word loads from the final AB bank yield the exact typed slice. -/
theorem frame_words {w : ℕ} {B : Word w} {mem : Memory w}
    (stored : IndexedStarts.Stored B (thickWidths P order width b) (abWidths P number width b) mem)
    (a : P.ThickFiber b) :
    let f := frame P number order m B a
    let s := P.demandSlice number order width b a m
    (mem (f+2)).val = s.length ∧
      (0 < s.length → (mem f).val = s.sourceOffset ∧ (mem (f+1)).val = s.targetOffset) := by
  intro f s
  let i := (order b a).val * pieceCount d c + (number b m).val
  have ho : (thickWidths P order width b).length = 2 ^ c * d / 4 := List.length_ofFn
  have hn : (abWidths P number width b).length = pieceCount d c := List.length_ofFn
  have hi : i < (thickWidths P order width b).length * (abWidths P number width b).length := by
    rw [ho,hn]
    calc
      _ < (order b a).val * pieceCount d c + pieceCount d c :=
        Nat.add_lt_add_left (number b m).isLt _
      _ = ((order b a).val + 1) * pieceCount d c := (Nat.succ_mul _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (order b a).isLt
  have hs := ab_sliceAt P number order width b a m
  have len := stored.lengths i hi
  rw [ho,hn,hs] at len
  refine ⟨len, fun hp ↦ ?_⟩
  have off := stored.offsets i hi (hs ▸ hp)
  rw [ho, hn, hs] at off
  exact off

theorem source_bound (a : P.ThickFiber b) :
    let s := P.demandSlice number order width b a m
    ∀ k : Fin s.length, s.sourceOffset + k.val < width a.1.1 := by
  intro s k
  have hk := k.isLt
  dsimp [s,demandSlice,copySlice] at hk ⊢
  omega

theorem target_bound (a : P.ThickFiber b) :
    let s := P.demandSlice number order width b a m
    0 < s.length → s.targetOffset + s.length ≤ P.abWidth number width m.val := by
  intro s h
  dsimp [s,demandSlice,copySlice] at h ⊢
  omega

/-- Bits copied by a single actual AB frame at either packed endpoint. -/
def copyBits (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool) (a : P.ThickFiber b) :
    List Bool :=
  let s := P.demandSlice number order width b a m
  List.ofFn fun k : Fin s.length ↦
    data a ⟨s.sourceOffset+k.val, source_bound P number order width m a k⟩

/-- Read the AB operand of the typed demand-bit bijection from a collection of
old half-wires. The field data can be different at the two packed endpoints. -/
def operand (hc : 2 ≤ c) (hd : 0 < d) (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool)
    (j : Fin (P.abWidth number width m.val)) : Bool :=
  let a := P.demandBitEquiv hc hd number order width b ⟨m, j⟩
  data a.1 a.2

/-- Each copied bit already has its eventual value in the assembled AB word. -/
theorem copyBits_operand (hc : 2 ≤ c) (hd : 0 < d)
    (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool) (a : P.ThickFiber b) :
    let s := P.demandSlice number order width b a m
    ∀ k : Fin s.length, (copyBits P number order width m data a)[k.val]? =
      some (operand P number order width m hc hd data
        ⟨s.targetOffset+k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt _)
          (target_bound P number order width m a (Nat.zero_lt_of_lt k.isLt))⟩) := by
  intro s k
  let src : Fin (width a.1.1) := ⟨s.sourceOffset+k.val, source_bound P number order width m a k⟩
  let dst : Fin (P.abWidth number width m.val) := ⟨s.targetOffset+k.val,
    lt_of_lt_of_le (Nat.add_lt_add_left k.isLt _) (target_bound P number order width m a
      (Nat.zero_lt_of_lt k.isLt))⟩
  have he := (P.demandBitEquiv_eq_iff_slice number order width b hc hd a m src dst).2
    ⟨k.val,k.isLt,rfl,rfl⟩
  change _ = some (let z := P.demandBitEquiv hc hd number order width b ⟨m,dst⟩; data z.1 z.2)
  rw [he]
  simp only [copyBits, List.getElem?_ofFn, src]
  split <;> simp_all [s]

/-- Private-memory effect of the source-major copies into one AB destination. -/
def fill {w : ℕ} (base : ℕ) (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool)
    (as : List (P.ThickFiber b)) (mem : Word w → Word w) : Word w → Word w :=
  as.foldl (fun old a ↦ PrivateFields.storeBits
    (base + (P.demandSlice number order width b a m).targetOffset)
    (copyBits P number order width m data a) old) mem

private theorem store_bit {w : ℕ} (dst : ℕ) (bits : List Bool) (mem : Word w → Word w)
    (k : ℕ) (bit : Bool) (get : bits[k]? = some bit) (fit : dst + bits.length ≤ 2 ^ w) :
    PrivateFields.storeBits dst bits mem ((dst+k : ℕ) : Word w) = PrivateFields.bitValue w bit := by
  have hk : k < bits.length := by
    by_contra! h
    rw [List.getElem?_eq_none h] at get
    contradiction
  rw [List.getElem?_eq_getElem hk, Option.some.injEq] at get
  exact (PrivateFields.storeBits_read dst bits mem fit ⟨k,hk⟩).trans (congrArg _ get)

/-- A positive slice writes its own target coordinates and leaves every other
coordinate of the AB word unchanged. Zero-length frames have no memory effect. -/
private theorem store_at_target {w : ℕ} (hc : 2 ≤ c) (hd : 0 < d) (base : ℕ)
    (fit : base + P.abWidth number width m.val ≤ 2 ^ w)
    (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool) (a : P.ThickFiber b)
    (j : Fin (P.abWidth number width m.val)) (mem : Word w → Word w) :
    let s := P.demandSlice number order width b a m
    let f := (base+j.val : ℕ)
    PrivateFields.storeBits (base+s.targetOffset) (copyBits P number order width m data a) mem
      (f : Word w) = if s.targetOffset ≤ j.val ∧ j.val < s.targetOffset+s.length then
        PrivateFields.bitValue w (operand P number order width m hc hd data j) else mem f := by
  intro s f
  let bs := copyBits P number order width m data a
  have len : bs.length = s.length := List.length_ofFn
  by_cases hz : s.length = 0
  · have nil : bs = [] := List.length_eq_zero_iff.mp (len.trans hz)
    change PrivateFields.storeBits _ bs _ _ = _
    simp [nil, hz, PrivateFields.storeBits]
  have range := target_bound P number order width m a (Nat.pos_of_ne_zero hz)
  change s.targetOffset + s.length ≤ _ at range
  have cap : base+s.targetOffset+bs.length ≤ 2 ^ w := by omega
  by_cases h : s.targetOffset ≤ j.val ∧ j.val < s.targetOffset+s.length
  · rw [ite_eq_left h]
    let k : Fin s.length := ⟨j.val-s.targetOffset, by omega⟩
    have hval : s.targetOffset+k.val = j.val := Nat.add_sub_of_le h.1
    have he := copyBits_operand P number order width m hc hd data a k
    have hdj : (⟨s.targetOffset+k.val, by omega⟩ : Fin (P.abWidth number width m.val)) = j :=
      Fin.ext hval
    rw [hdj] at he
    change PrivateFields.storeBits _ bs _ _ = _
    rw [show f = (base+s.targetOffset)+k.val by dsimp [f]; omega]
    exact store_bit _ _ _ _ _ he cap
  · rw [ite_eq_right h]
    apply PrivateFields.storeBits_outside _ _ _ _ cap
    have hf : (f : Word w).val = f := Nat.mod_eq_of_lt (by dsimp [f]; omega)
    rw [hf]
    dsimp only [f]
    omega

/-- Visiting every thick arc in the bundle reconstructs the exact AB buffer.
The physical readout works for arbitrary prior destination memory. -/
theorem fill_operand {w : ℕ} (hc : 2 ≤ c) (hd : 0 < d) (base : ℕ)
    (fit : base + P.abWidth number width m.val ≤ 2 ^ w)
    (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool)
    (as : List (P.ThickFiber b)) (mem : Word w → Word w) (j : Fin (P.abWidth number width m.val))
    (covered : (P.demandBitEquiv hc hd number order width b ⟨m, j⟩).1 ∈ as ∨
      mem ((base + j.val : ℕ) : Word w) =
        PrivateFields.bitValue w (operand P number order width m hc hd data j)) :
    fill P number order width m base data as mem ((base + j.val : ℕ) : Word w) =
      PrivateFields.bitValue w (operand P number order width m hc hd data j) := by
  induction as generalizing mem with
  | nil => exact covered.resolve_left (by simp)
  | cons a as ih =>
    apply ih
    have hs := store_at_target P number order width m hc hd base fit data a j mem
    dsimp only at hs
    by_cases inside : (P.demandSlice number order width b a m).targetOffset ≤ j.val ∧
        j.val < (P.demandSlice number order width b a m).targetOffset +
          (P.demandSlice number order width b a m).length
    · exact Or.inr (hs.trans (ite_eq_left inside))
    · rw [ite_eq_right inside] at hs
      refine covered.elim (fun ha ↦ Or.inl ?_) (fun val ↦ Or.inr (hs.trans val))
      rw [List.mem_cons] at ha
      apply ha.resolve_left
      intro he
      cases hraw : P.demandBitEquiv hc hd number order width b ⟨m, j⟩ with
      | mk src idx =>
        rw [hraw] at he
        change src = a at he
        subst a
        obtain ⟨k,hk,_,hj⟩ :=
          (P.demandBitEquiv_eq_iff_slice number order width b hc hd src m idx j).mp hraw
        exact inside ⟨by omega, by omega⟩

end PairSimulation.ShrinkAB

end VPVNP
end Computability
end OAI
