import OAI.Computability.BorderVNP.CubeHostScatterLayout
import OAI.Computability.BorderVNP.TransmissionDataSlabs
import OAI.Computability.BorderVNP.RoutingISACompactWriteLoop

/-! # Reading back the bits scattered into each owned cell's exterior bank

The physical sparse order may interleave both ends of a cable with arbitrary unowned
or absorbed cables. Disjoint destination intervals ensure that each copied bit survives
all subsequent endpoints. All addresses outside the visited intervals retain their inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA.CompactWrite

/-- Distinct owned endpoints in the directory occupy disjoint half-open intervals. -/
def Layout.SeparateDestinations (l : Layout) (m : ℕ → ℕ) : Prop :=
  ∀ i < l.count, ∀ s, l.Owned m i s → ∀ k < l.count, ∀ t, l.Owned m k t →
    (i,s) ≠ (k,t) → Disjoint (l.dest m i s) (l.width m i) (l.dest m k t) (l.width m k)

/-- The actual owned endpoints to be placed among the cell bank's supplied words. -/
abbrev Layout.OwnedEnd (l : Layout) (m : ℕ → ℕ) :=
  {p : Fin l.count × Bool // l.Owned m p.1 p.2}

/-- The compact cell-bank layout gives disjoint destinations. Other supplied words may
share the same cell and occupy slots between the embedded crossing ends. -/
theorem Layout.separateDestinations_of_slabs {l : Layout} {m : ℕ → ℕ} {A : Type*}
    [Fintype A] {cells : ℕ} (cell : A → Fin cells) (row : A ↪ ℕ) (width : A → ℕ)
    (origin stride : ℕ) (room : ∀ c, Packing.Directory.DataSlabs.size cell width c ≤ stride)
    (ends : l.OwnedEnd m ↪ A)
    (widths : ∀ p, width (ends p) = l.width m p.val.1)
    (placed : ∀ p, l.dest m p.val.1 p.val.2 = origin + (cell (ends p)).val*stride +
      Packing.Directory.DataSlabs.base cell row width (ends p)) :
    l.SeparateDestinations m := by
  intro i hi s hs k hk t ht ne
  let p : l.OwnedEnd m := ⟨(⟨i,hi⟩,s),hs⟩
  let q : l.OwnedEnd m := ⟨(⟨k,hk⟩,t),ht⟩
  by_contra h
  change ¬(_ ≤ _ ∨ _ ≤ _) at h
  let a := max (l.dest m i s) (l.dest m k t)
  have pos := hs.1
  have pos' := ht.1
  have wp : a-l.dest m i s < width (ends p) := by
    rw [widths]; change a-l.dest m i s < l.width m i; dsimp [a]; omega
  have wq : a-l.dest m k t < width (ends q) := by
    rw [widths]; change a-l.dest m k t < l.width m k; dsimp [a]; omega
  let x : (v : A) × Fin (width v) := ⟨ends p,⟨a-l.dest m i s,wp⟩⟩
  let y : (v : A) × Fin (width v) := ⟨ends q,⟨a-l.dest m k t,wq⟩⟩
  have addr : Packing.Directory.DataSlabs.address cell row width origin stride x =
      Packing.Directory.DataSlabs.address cell row width origin stride y := by
    dsimp only [Packing.Directory.DataSlabs.address,x,y]
    rw [← placed p,← placed q]
    change l.dest m i s+(a-l.dest m i s) = l.dest m k t+(a-l.dest m k t)
    dsimp [a]; omega
  have equal := Packing.Directory.DataSlabs.address_injective cell row width origin stride room addr
  exact ne (congrArg (fun v : l.OwnedEnd m => (v.val.1.val,v.val.2))
    (ends.injective (congrArg Sigma.fst equal)))

variable {l : Layout} {before mem : ℕ → ℕ}

private theorem copyEnd_off {i a : ℕ} {side : Bool}
    (away : l.Owned before i side → a < l.dest before i side ∨ l.dest before i side+l.width before i ≤ a) :
    l.copyEnd before mem i side a = mem a := by
  apply ite_eq_right
  rintro ⟨owned,low,high⟩
  rcases away owned with h | h <;> omega

/-- Addresses outside all owned intervals of the first rows keep their input value.
This also covers the empty scan and a directory containing only absorbed cables. -/
theorem Layout.prefix_outside (l : Layout) (before : ℕ → ℕ) (n a : ℕ)
    (away : ∀ i < n, ∀ s, l.Owned before i s →
      a < l.dest before i s ∨ l.dest before i s + l.width before i ≤ a) :
    l.prefix before n a = before a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Layout.prefix,copyEnd_off (away n (Nat.lt_succ_self _) true),
      copyEnd_off (away n (Nat.lt_succ_self _) false)]
    exact ih fun i hi => away i (Nat.lt_succ_of_lt hi)

private theorem copyEnd_bit {i j : ℕ} {side : Bool} (owned : l.Owned before i side)
    (hj : j < l.width before i) :
    l.copyEnd before mem i side (l.dest before i side+j) = before (l.source before i side j) := by
  simp only [Layout.copyEnd,owned,Nat.le_add_right,Nat.add_lt_add_iff_left,hj,
    and_self,ite_true,Nat.add_sub_cancel_left]

private theorem copyEnd_other (apart : l.SeparateDestinations before) {i k j : ℕ} {s t : Bool}
    (hi : i < l.count) (hk : k < l.count) (owned : l.Owned before i s)
    (hj : j < l.width before i) (different : (i,s) ≠ (k,t)) :
    l.copyEnd before mem k t (l.dest before i s+j) = mem (l.dest before i s+j) := by
  apply copyEnd_off
  intro other
  rcases apart i hi s owned k hk t other different with h | h <;> omega

/-- After any prefix containing its row, each owned endpoint bit reads back exactly
the original singleton or antipodal packet bit chosen by its physical source address. -/
theorem Layout.prefix_owned_bit {l : Layout} {before : ℕ → ℕ}
    (apart : l.SeparateDestinations before) {i n : ℕ} (hin : i < n) (hn : n ≤ l.count)
    {s : Bool} (owned : l.Owned before i s) {j : ℕ} (hj : j < l.width before i) :
    l.prefix before n (l.dest before i s+j) = before (l.source before i s j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hi : i < l.count := hin.trans_le hn
    have hk : n < l.count := by omega
    rw [Layout.prefix]
    by_cases same : i = n
    · subst i
      cases s with
      | false =>
        rw [copyEnd_other apart hk hk owned hj (by simp : (n,false) ≠ (n,true))]
        exact copyEnd_bit owned hj
      | true => exact copyEnd_bit owned hj
    · rw [copyEnd_other apart hi hk owned hj (by simp [same] : (i,s) ≠ (n,true)),
        copyEnd_other apart hi hk owned hj (by simp [same] : (i,s) ≠ (n,false))]
      exact ih (by omega) (by omega)

/-- At the end of the directory, all owned source bits have arrived and every other
address retains the original word. -/
theorem Layout.prefix_readback (l : Layout) (before : ℕ → ℕ) (apart : l.SeparateDestinations before) :
    (∀ i < l.count, ∀ s, l.Owned before i s → ∀ j < l.width before i,
      l.prefix before l.count (l.dest before i s+j) = before (l.source before i s j)) ∧
    ∀ a, (∀ i < l.count, ∀ s, l.Owned before i s →
      a < l.dest before i s ∨ l.dest before i s+l.width before i ≤ a) →
      l.prefix before l.count a = before a :=
  ⟨fun _ hi _ owned _ hj => prefix_owned_bit apart hi le_rfl owned hj, prefix_outside l before l.count⟩

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
