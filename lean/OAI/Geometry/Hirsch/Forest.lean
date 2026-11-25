import OAI.Geometry.Hirsch.Samples

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

structure Forest (Coord Choice : Type) (height : ℕ) where
  path : Coord → List (Coord × Choice)
  proper : ∀ idx parent opt tail, path idx = (parent, opt) :: tail → path parent = tail
  bounded : ∀ idx, (path idx).length ≤ height

namespace Forest

variable {Coord Choice : Type} {height : ℕ} (tree : Forest Coord Choice height)

def Live (usable : Set Coord) (pick : Coord → Choice) (path : List (Coord × Choice)) : Prop :=
  ∀ entry ∈ path, entry.1 ∉ usable ∧ pick entry.1 = entry.2

@[simp] theorem live_nil (usable : Set Coord) (pick : Coord → Choice) : Live usable pick [] := by
  simp [Live]

@[simp] theorem live_cons (usable : Set Coord) (pick : Coord → Choice) (idx opt tail) :
    Live usable pick ((idx, opt) :: tail) ↔ idx ∉ usable ∧ pick idx = opt ∧ Live usable pick tail := by
  simp [Live, and_assoc]

def Wins (usable : Set Coord) (pick : Coord → Choice) : Prop :=
  ∀ idx, Live usable pick (tree.path idx) → (tree.path idx).length = height → idx ∈ usable

def Viable (usable : Set Coord) : Prop := ∃ pick, tree.Wins usable pick

theorem viable_mono : Monotone tree.Viable := by
  rintro small large hsub ⟨pick, hp⟩
  refine ⟨pick, fun idx hh hl => hsub (hp idx ?_ hl)⟩
  intro entry he
  exact ⟨fun hi => (hh entry he).1 (hsub hi), (hh entry he).2⟩

def past (path : List (Coord × Choice)) : Set Coord := {idx | ∃ opt, (idx, opt) ∈ path}

@[simp] theorem past_nil : past ([] : List (Coord × Choice)) = ∅ := by ext; simp [past]

@[simp] theorem past_cons (idx : Coord) (opt : Choice) (tail) :
    past ((idx, opt) :: tail) = insert idx (past tail) := by
  ext
  simp [past, exists_or]

theorem past_bound (path : List (Coord × Choice)) : (past path).ncard ≤ path.length := by
  induction path with
  | nil => simp
  | cons entry tail ih =>
    obtain ⟨idx, opt⟩ := entry
    rw [past_cons, List.length_cons]
    exact (ncard_insert_le ..).trans (Nat.add_le_add_right ih 1)

def ancestors (idx : Coord) : Set Coord := insert idx (past (tree.path idx))

theorem ancestors_bound (idx : Coord) : (tree.ancestors idx).ncard ≤ height + 1 :=
  (ncard_insert_le ..).trans (Nat.add_le_add_right ((past_bound _).trans (tree.bounded idx)) 1)

abbrev program [Fintype Coord] [Nonempty Choice] : Program where
  Coord := Coord
  viable := tree.Viable
  allViable := ⟨fun _ => Classical.arbitrary _, fun _ _ _ => mem_univ _⟩
  ancestors := tree.ancestors
  self_mem idx := mem_insert idx _

def Presents {prog : Program} (tree : Forest prog.Coord Choice height) : Prop :=
  prog.viable = tree.Viable ∧ prog.ancestors = tree.ancestors

variable {Index : Type} {coords : Index → Type} (seq : ∀ idx, Forest (coords idx) Choice height)

def tag (idx : Index) (entry : coords idx × Choice) : Sigma coords × Choice :=
  (⟨idx, entry.1⟩, entry.2)

def join : Forest (Sigma coords) Choice height where
  path idx := ((seq idx.1).path idx.2).map (tag idx.1)
  proper := by
    rintro ⟨idx, coord⟩ parent opt tail he
    cases hh : (seq idx).path coord with
    | nil => simp [hh] at he
    | cons entry rest =>
      obtain ⟨src, label⟩ := entry
      simp only [hh, List.map_cons, List.cons.injEq, tag, Prod.mk.injEq] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      exact congrArg (List.map (tag idx)) ((seq idx).proper _ _ _ _ hh)
  bounded idx := by simpa using (seq idx.1).bounded idx.2

theorem join_live (usable : Set (Sigma coords)) (pick : Sigma coords → Choice) (idx : Index) (coord) :
    Live usable pick ((join seq).path ⟨idx, coord⟩) ↔
      Live (Sigma.mk idx ⁻¹' usable) (pick ∘ Sigma.mk idx) ((seq idx).path coord) := by
  constructor
  · exact fun hh entry he => hh _ (List.mem_map.mpr ⟨entry, he, rfl⟩)
  · intro hh entry he
    obtain ⟨src, hs, rfl⟩ := List.mem_map.mp he
    exact hh src hs

theorem join_viable (usable : Set (Sigma coords)) :
    (join seq).Viable usable ↔ ∀ idx, (seq idx).Viable (Sigma.mk idx ⁻¹' usable) := by
  constructor
  · rintro ⟨pick, hp⟩ idx
    exact ⟨pick ∘ Sigma.mk idx, fun coord hh hl =>
      hp ⟨idx, coord⟩ ((join_live ..).mpr hh) (by simpa [join] using hl)⟩
  · intro hh
    choose pick hp using hh
    refine ⟨fun idx => pick idx.1 idx.2, ?_⟩
    rintro ⟨idx, coord⟩ hl he
    exact hp idx coord ((join_live ..).mp hl) (by simpa [join] using he)

theorem join_ancestors (idx : Index) (coord : coords idx) :
    (join seq).ancestors ⟨idx, coord⟩ = Sigma.mk idx '' (seq idx).ancestors coord := by
  rw [ancestors, ancestors, image_insert_eq]
  congr 1
  ext other
  simp only [past, mem_ofPred_eq, join, List.mem_map, mem_image]
  constructor
  · rintro ⟨opt, ⟨src, label⟩, hm, he⟩
    exact ⟨src, ⟨label, hm⟩, (Prod.mk.inj he).1⟩
  · rintro ⟨src, ⟨label, hm⟩, rfl⟩
    exact ⟨label, (src, label), hm, rfl⟩

def bank (Choice : Type) (height : ℕ) : Bank where
  accepts prog := ∃ tree : Forest prog.Coord Choice height, tree.Presents
  join := by
    intro Index inst seq hh
    choose tree ht using hh
    refine ⟨join tree, ?_, ?_⟩
    · funext usable
      apply propext
      rw [join_viable]
      exact forall_congr' fun idx => congrFun (ht idx).1 _ |>.to_iff
    · funext coord
      obtain ⟨idx, coord⟩ := coord
      rw [join_ancestors, ← (ht idx).2]

theorem accepts [Fintype Coord] [Nonempty Choice] :
    (bank Choice height).accepts tree.program := ⟨tree, rfl, rfl⟩

end Forest
end OAI.Geometry.Hirsch
