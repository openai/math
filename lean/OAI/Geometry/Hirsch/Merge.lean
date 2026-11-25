import OAI.Geometry.Hirsch.Cluster

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

def piece (width j : ℕ) : Set ℕ := {x | x/width = j}

def pieces (width j a : ℕ) : Set ℕ := {x | j ≤ x/width ∧ x/width < j+a}

theorem pieces_succ (width j a : ℕ) :
    pieces width j (a+1) = pieces width j a ∪ piece width (j+a) := by
  ext x; simp only [pieces,piece,Set.mem_ofPred_eq,Set.mem_union]; omega

theorem pieces_eq (width j a : ℕ) (ha : 0 < a) :
    pieces width (j*a) a = piece (width*a) j := by
  ext x
  simp only [pieces,piece,Set.mem_ofPred_eq,← Nat.div_div_eq_div_mul]
  rw [show j*a+a = (j+1)*a by ring,← Nat.le_div_iff_mul_le ha,← Nat.div_lt_iff_lt_mul ha]
  omega

variable {I Bit : Type} {n : ℕ} (w : Board I n) (keys : Bit → Finset I)

def home (width : ℕ) (i : I) := piece width (w.place i / width)

theorem home_eq {width j : ℕ} {i : I} (h : w.place i ∈ piece width j) : w.home width i = piece width j :=
  congrArg (piece width) h

theorem home_sub (width a : ℕ) (i : I) : w.home width i ⊆ w.home (width*a) i := by
  intro x hx
  change x/width = w.place i/width at hx
  change x/(width*a) = w.place i/(width*a)
  simp only [← Nat.div_div_eq_div_mul,hx]

def zone (area : Set ℕ) : Set Bit :=
  {b | (keys b).Nonempty ∧ ∀ g ∈ keys b, w.place g ∈ area}

theorem zone_mono {area region : Set ℕ} (h : area ⊆ region) : w.zone keys area ⊆ w.zone keys region :=
  fun _ hb => ⟨hb.1,fun _ hg => h (hb.2 _ hg)⟩

theorem zone_disjoint {A B : Set ℕ} (hd : Disjoint A B) : Disjoint (w.zone keys A) (w.zone keys B) := by
  apply Set.disjoint_left.mpr
  rintro b ⟨⟨g,hg⟩,hA⟩ ⟨_,hB⟩
  exact Set.disjoint_left.mp hd (hA _ hg) (hB _ hg)

namespace Round

variable {w keys} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {r : w.Round} {d : Bool} {R : ℕ} {select : Table Bit → Finset I} {U : ℝ}

def Caps (coin : Coins Bit) (keys : Bit → Finset I) (r : w.Round) (d : Bool) (R : ℕ)
    (select : Table Bit → Finset I) (width : ℕ) (U : ℝ) :=
  ∀ j, Cap coin r d R select (piece width j) (w.zone keys (piece width j)) U

theorem Caps.merge {width a : ℕ} (h : Caps coin keys r d R select width U) (ha : 0 < a) :
    Caps coin keys r d R select (width*a) (a*U) := by
  have aux : ∀ j k, Cap coin r d R select (pieces width j k) (w.zone keys (pieces width j k)) ((k : ℝ)*U) := by
    intro j k
    induction k with
    | zero =>
      have he : pieces width j 0 = ∅ := by ext; simp [pieces]
      rw [he,Nat.cast_zero,zero_mul]; exact ⟨le_rfl,by simp,by simp⟩
    | succ k ih =>
      rw [pieces_succ,Nat.cast_succ,add_mul,one_mul]
      let A := pieces width j k
      let B := piece width (j+k)
      have ord : Precedes true A B := by
        intro x hx y hy
        have lt : x/width < y/width := hx.2.trans_eq hy.symm
        exact lt_of_not_ge fun hh => lt.not_ge (Nat.div_le_div_right hh)
      have dis := w.zone_disjoint keys ord.disjoint
      have hh : Cap coin r d R select (A ∪ B) (w.zone keys A ∪ w.zone keys B) (k*U+U) := by
        cases d
        · rw [Set.union_comm A,Set.union_comm (w.zone keys A),add_comm]
          exact (h _).join ih (fun x hx y hy => ord y hy x hx) dis.symm
        · exact ih.join (h _) ord dis
      exact ⟨hh.nonneg,fun i hi => (hh.reads i hi).mono (Set.union_subset
        (w.zone_mono keys Set.subset_union_left) (w.zone_mono keys Set.subset_union_right)),hh.bound⟩
  intro j; rw [← pieces_eq width j a ha]; exact aux _ _

end Round
end OAI.Geometry.Hirsch.Layer.Board
