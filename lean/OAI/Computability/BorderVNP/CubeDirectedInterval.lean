import OAI.Computability.BorderVNP.RoutingISATableIntervalPass
import OAI.Computability.BorderVNP.CubePhysicalPaddingRank

/-! # Directed label-pair intervals in the physical cable directory

The three words in each processed cable row are its source cell, destination
cell and width. A live row adds its width to the directed pair of its cell
labels, even when the two labels coincide. A cable internal to one cell has
already been absorbed, and receives a dummy ordinal of zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Addresses of the processed geometry, chosen cell labels and the two public output arrays. -/
structure Layout where
  /-- The address of the shared frame. -/
  frame : ℕ
  /-- Base of the three-word processed cable rows. -/
  cables : ℕ
  /-- Number of processed cable rows. -/
  count : ℕ
  /-- Base of the per-cell label array. -/
  labels : ℕ
  /-- Number of product-alphabet labels. -/
  alphabet : ℕ
  /-- Base of the directed square width table. -/
  widths : ℕ
  /-- Base of the cable-order interval start table. -/
  ordinals : ℕ

/-- The three processed columns and their label codes are read directly from the caller's RAM. -/
def Layout.src (l : Layout) (m : ℕ → ℕ) (i : ℕ) := m (l.cables+3*i)

/-- Destination cell number in the processed cable row. -/
def Layout.dst (l : Layout) (m : ℕ → ℕ) (i : ℕ) := m (l.cables+3*i+1)

/-- Public width of the processed cable. -/
def Layout.width (l : Layout) (m : ℕ → ℕ) (i : ℕ) := m (l.cables+3*i+2)

/-- Row-major directed pair address; the orientation is the cable's public source order. -/
def Layout.key (l : Layout) (m : ℕ → ℕ) (i : ℕ) :=
  m (l.labels+l.src m i)*l.alphabet + m (l.labels+l.dst m i)

/-- Total width of the live cables in one directed bin up to a given row. -/
def Layout.prefix (l : Layout) (m : ℕ → ℕ) (j k : ℕ) :=
  ∑ i ∈ Finset.range j, if l.src m i ≠ l.dst m i ∧ l.key m i = k then l.width m i else 0

/-- The stored ordinal is the prefix width of the cable's ordered pair, for a live cable. -/
def Layout.ordinal (l : Layout) (m : ℕ → ℕ) (i : ℕ) :=
  if l.src m i = l.dst m i then 0 else l.prefix m i (l.key m i)

/-- Configuration words read by the native setup. -/
def Layout.Fields (l : Layout) (m : ℕ → ℕ) : Prop :=
  m (l.frame+6) = l.cables ∧ m (l.frame+7) = l.count ∧ m (l.frame+48) = l.labels ∧
    m (l.frame+56) = l.alphabet ∧ m (l.frame+57) = l.widths ∧ m (l.frame+58) = l.ordinals

/-- Register values reserved throughout the native scan. -/
def Layout.regValue (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => l.cables | 4 => l.count
  | 5 => l.labels | 6 => l.alphabet | 7 => l.widths | 8 => l.ordinals | 9 => l.alphabet^2 | _ => 0

/-- Ready configuration with all cable and scratch pointers loaded. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop := ∀ j : Reg, j.val ≤ 9 → z.reg j = l.regValue j.val

/-- A scratch-only instruction block retains the persistent setup registers. -/
theorem Layout.Ready.fixed {l : Layout} {z : NatState} (h : l.Ready z)
    {c : Code} (hc : c.protects 10 = true) (pub : Arg → ℕ) : l.Ready (c.fixedEval pub z) :=
  fun j hj => (c.fixedEval_protected pub z hc j (by omega)).trans (h j hj)

/-- Input addresses, scratch allocations, and total directed widths fit the native word. -/
structure Layout.Fits (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Frame pointer addition and its largest field offset fit. -/
  frameFit : l.frame+58 < 2^w
  /-- Cable scanning counter fits. -/
  countFit : l.count < 2^w
  /-- Clearing the square table uses a word-sized limit. -/
  squareFit : l.alphabet^2 < 2^w
  /-- Each three-word cable interval is addressable. -/
  cableFit : l.cables + 3*l.count ≤ 2^w
  /-- Every label read is addressable and contains an in-range product-alphabet code. -/
  labelsFit : ∀ i < l.count, ∀ c ∈ [l.src m i, l.dst m i], l.labels+c < 2^w ∧ m (l.labels+c) < l.alphabet
  /-- Width output interval fits. -/
  widthsFit : l.widths + l.alphabet^2 ≤ 2^w
  /-- Ordinal output interval fits. -/
  ordinalsFit : l.ordinals+l.count ≤ 2^w
  /-- The two output intervals are disjoint. -/
  disjoint : ∀ k < l.alphabet^2, ∀ i < l.count, l.widths+k ≠ l.ordinals+i
  /-- Every processed row and label lookup avoids both output intervals. -/
  input : ∀ i < l.count, ∀ a ∈ [l.cables+3*i,l.cables+3*i+1,l.cables+3*i+2,
    l.labels+l.src m i,l.labels+l.dst m i],
    (¬(l.widths ≤ a ∧ a < l.widths+l.alphabet^2)) ∧ (¬(l.ordinals ≤ a ∧ a < l.ordinals+l.count))
  /-- Cumulative bin widths do not overflow in the selected word size. -/
  volume : ∀ i ≤ l.count, ∀ k, l.prefix m i k < 2^w

/-- An exact prefix image of both output arrays, retaining all other memory. -/
structure Layout.Image (l : Layout) (before : ℕ → ℕ) (j : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Width after the first `j` descriptors. -/
  widths : ∀ k < l.alphabet^2, mem (l.widths+k) = l.prefix before j k
  /-- Ordinal of each completed descriptor. -/
  ordinals : ∀ i < j, mem (l.ordinals+i) = l.ordinal before i
  /-- Contents away from both output arrays. -/
  outside : ∀ x, ¬(l.widths ≤ x ∧ x < l.widths+l.alphabet^2) →
    ¬(l.ordinals ≤ x ∧ x < l.ordinals+l.count) → mem x = before x

/-- The directed ordered-pair index lies inside its square, even for matching labels. -/
theorem Layout.key_lt {l : Layout} {w : ℕ} {m : ℕ → ℕ} (h : l.Fits w m) {i : ℕ} (hi : i < l.count) :
    l.key m i < l.alphabet^2 := by
  have hs := (h.labelsFit i hi (l.src m i) (by simp)).2
  have hd := (h.labelsFit i hi (l.dst m i) (by simp)).2
  calc
    _ < (m (l.labels+l.src m i)+1)*l.alphabet := by dsimp [Layout.key]; rw [Nat.add_mul,one_mul]; omega
    _ ≤ _ := (Nat.mul_le_mul_right _ hs).trans_eq (pow_two l.alphabet).symm

/-- Saving the start and advancing a bin count only for a live crossing. -/
def Layout.store (l : Layout) (before mem : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  if l.src before i = l.dst before i then Function.update mem (l.ordinals+i) 0 else
    let a := l.widths+l.key before i
    Function.update (Function.update mem (l.ordinals+i) (mem a)) a (mem a+l.width before i)

/-- Prefix and ordinal identities are preserved by both genuine native stores. -/
theorem Layout.Image.store {l : Layout} {w j : ℕ} {before mem : ℕ → ℕ} (h : l.Image before j mem)
    (fit : l.Fits w before) (hj : j < l.count) : l.Image before (j+1) (l.store before mem j) := by
  have hkey := l.key_lt fit hj
  constructor
  · intro k hk
    have sep := fit.disjoint k hk j hj
    by_cases hc : l.src before j = l.dst before j
    · simp [Layout.store,hc, Function.update_of_ne sep, h.widths k hk, Layout.prefix, Finset.sum_range_succ]
    · by_cases he : k = l.key before j
      · subst k
        simp [Layout.store,hc,h.widths _ hkey,Layout.prefix,Finset.sum_range_succ]
      · have ha : l.widths+k ≠ l.widths+l.key before j := by omega
        simp [Layout.store,hc,Function.update_of_ne ha,Function.update_of_ne sep,
          h.widths k hk,Layout.prefix,Finset.sum_range_succ,Ne.symm he]
  · intro i hi
    have sep := (fit.disjoint _ hkey i (by omega)).symm
    by_cases eq : i = j
    · subst i
      by_cases hc : l.src before j = l.dst before j <;> simp [Layout.store,Layout.ordinal,hc,Function.update_of_ne sep,h.widths _ hkey]
    · have ha : l.ordinals+i ≠ l.ordinals+j := by omega
      have hv := h.ordinals i (by omega)
      by_cases hc : l.src before j = l.dst before j <;> simp [Layout.store,hc,Function.update_of_ne sep,Function.update_of_ne ha,hv]
  · intro x hx hy
    have hxo : x ≠ l.ordinals+j := by intro he; apply hy; omega
    have hxw : x ≠ l.widths+l.key before j := by intro he; apply hx; omega
    by_cases hc : l.src before j = l.dst before j <;> simp [Layout.store,hc,Function.update_of_ne hxo,
      Function.update_of_ne hxw,h.outside x hx hy]

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
