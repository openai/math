import OAI.Geometry.Hirsch.LocalBits

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Board (I : Type) (n : ℕ) := World I (n*3)

namespace Board

variable {I : Type} {n : ℕ} (w : Board I n)

def place (i : I) := w.layer i / 3
def Middle (i : I) := w.layer i % 3 = 1
def Shore (d : Bool) (i : I) := w.layer i % 3 = if d then 2 else 0

def loc (d : Bool) (i : I) := if d then w.layer i else n*3-1-w.layer i

def num (d : Bool) (i : I) := w.loc d i / 3

theorem num_lt (d : Bool) (i : I) : w.num d i < n := by
  have := w.bound i
  unfold num loc
  split <;> omega

theorem same (d : Bool) (i j : I) : w.num d i = w.num d j ↔ w.place i = w.place j := by
  have := w.bound i
  have := w.bound j
  cases d <;> simp [num,loc,place]; omega

theorem reverse (d : Bool) (i : I) : w.num (!d) i + w.num d i + 1 = n := by
  have := w.bound i
  cases d <;> simp [num,loc] <;> omega

theorem loc_step (d : Bool) {i : I} (hi : w.live i) : w.loc d (w.step i d) = w.loc d i + 1 := by
  have := w.bound i
  have := w.east i hi
  have := w.west i hi
  cases d <;> simp [loc] <;> omega

theorem shore_loc (d : Bool) (i : I) : w.Shore d i ↔ w.loc d i % 3 = 2 := by
  have := w.bound i
  cases d <;> simp [Shore,loc]; omega

theorem middle_loc (d : Bool) (i : I) : w.Middle i ↔ w.loc d i % 3 = 1 := by
  have := w.bound i
  cases d <;> simp [Middle,loc]; omega

theorem middle_step {i : I} (hm : w.Middle i) (hl : w.live i) (d : Bool) :
    w.Shore d (w.step i d) ∧ w.place (w.step i d) = w.place i := by
  have := w.loc_step d hl
  have := (w.middle_loc d i).mp hm
  rw [w.shore_loc,← w.same d]
  unfold num
  omega

structure Round where
  mark : I → Bool → Prop
  middle : ∀ i d, mark i d → w.Middle i ∧ w.live i
  jump : I → Bool → I → Prop
  localJump : ∀ i d j, jump i d j → w.live i ∧ w.layer j = w.layer i ∧ w.rank j < w.rank i

abbrev Budget := ℕ → ℕ

def flat (d : ℕ) : Budget := fun _ => d

def atLayer (j : ℕ) : Budget := fun k => if k = j then 1 else 0

def ahead (d : Bool) (i : I) : Budget :=
  fun j => if (if d then w.layer i ≤ j else j ≤ w.layer i) then 1 else 0

theorem ahead_one (d : Bool) (i : I) : w.ahead d i ≤ flat 1 := by intro j; simp only [ahead,flat]; split_ifs <;> omega

theorem ahead_step (d : Bool) {i : I} (hi : w.live i) :
    atLayer (w.layer i) + w.ahead d (w.step i d) = w.ahead d i := by
  have := w.east i hi
  have := w.west i hi
  ext j
  cases d <;> simp only [atLayer,ahead,Pi.add_apply,Bool.false_eq_true,↓reduceIte] <;> split_ifs <;> omega

namespace Round

variable {w} (r : w.Round)

def charge (i : I) (d : Bool) : List I := if r.mark i d then [w.step i d] else []

theorem charge_mem {i j : I} {d : Bool} : j ∈ r.charge i d ↔ r.mark i d ∧ j = w.step i d := by
  by_cases h : r.mark i d <;> simp [charge,h]

def Move (i : I) (d : Bool) (j : I) := w.live i ∧ (j = w.step i d ∨ r.jump i d j)

theorem basic {i : I} (hi : w.live i) (d : Bool) : r.Move i d (w.step i d) := ⟨hi,.inl rfl⟩

theorem falls {i j : I} {d : Bool} (hm : r.Move i d j) : w.rank j < w.rank i := by
  rcases hm with ⟨hl,rfl | hh⟩
  · exact w.decrease _ hl _
  · exact (r.localJump _ _ _ hh).2.2

inductive Trip (area : Set ℕ) : I → I → Budget → List I → Prop
  | nil {i b} : Trip area i i b []
  | go {i j k d b a path} (inside : w.place i ∈ area) (move : r.Move i d j)
      (allow : atLayer (w.layer i) + a ≤ b) (tail : Trip area j k a path) :
      Trip area i k b (r.charge i d ++ path)

def Ends (w : Board I n) (area : Set ℕ) (d : Bool) (i : I) :=
  (w.place i ∈ area ∧ ¬w.live i) ∨ (w.place i ∉ area ∧ w.Shore (!d) i)

def test (area : Set ℕ) (d : Bool) (b : Budget) (i : I) : Trial I :=
  {path | ∃ j, Ends w area d j ∧ r.Trip area i j b path}

def paths (area : Set ℕ) (b : Budget) (i : I) : Trial I :=
  {path | ∃ j, r.Trip area i j b path}

variable {r} {area : Set ℕ} {i j k : I} {a b c : Budget} {path path' : List I}

theorem Trip.more (h : r.Trip area i j a path) (hb : a ≤ b) : r.Trip area i j b path := by
  cases h with
  | nil => exact .nil
  | go hi hm ha ht => exact .go hi hm (ha.trans hb) ht

theorem Trip.append (h : r.Trip area i j a path) (h' : r.Trip area j k b path') :
    r.Trip area i k (a+b) (path ++ path') := by
  induction h with
  | nil => exact h'.more (fun _ => Nat.le_add_left ..)
  | go hi hm ha ht ih =>
    rw [List.append_assoc]
    exact .go hi hm (by rw [← add_assoc]; exact add_le_add_left ha _) (ih h')

theorem Trip.widen (h : r.Trip area i j a path) {s : Set ℕ} (hs : area ⊆ s) : r.Trip s i j a path := by
  induction h with
  | nil => exact .nil
  | go hi hm ha ht ih => exact .go (hs hi) hm ha ih

theorem Trip.rank (h : r.Trip area i j a path) : w.rank j ≤ w.rank i := by
  induction h with
  | nil => rfl
  | go hi hm ha ht ih => exact ih.trans (r.falls hm).le

theorem Trip.member (h : r.Trip area i j a path) {g : I} (hg : g ∈ path) :
    w.place g ∈ area ∧ w.rank g < w.rank i := by
  induction h with
  | nil => simp at hg
  | go hi hm ha ht ih =>
    rcases List.mem_append.mp hg with hh | hh
    · obtain ⟨hc,rfl⟩ := r.charge_mem.mp hh
      exact ⟨(w.middle_step (r.middle _ _ hc).1 hm.1 _).2.symm ▸ hi,w.decrease _ hm.1 _⟩
    · exact ⟨(ih hh).1,(ih hh).2.trans (r.falls hm)⟩

theorem test_mono (r : w.Round) (area : Set ℕ) (d : Bool) (i : I) (h : a ≤ b) :
    (r.test area d a i).Refines (r.test area d b i) := by
  rintro s hs path ⟨j,hj,hp⟩
  exact hs path ⟨j,hj,hp.more h⟩

end Round
end Board
end OAI.Geometry.Hirsch.Layer
