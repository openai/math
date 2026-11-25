import OAI.Geometry.Hirsch.CutOrder

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Pins

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)
  {A B C D : Finset (Finset I)}

abbrev Relation (I : Type) := Finset I → Finset I → Prop

def pairMass (A B : Finset (Finset I)) (P : Relation I) :=
  ∑ s ∈ A, pins.weight s * pins.mass (B.filter (P s))

theorem pair_nonneg (P : Relation I) : 0 ≤ pins.pairMass A B P :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pins.positive _).le (pins.mass_nonneg _)

theorem pair_mono {P Q : Relation I} (ha : A ⊆ C) (hb : B ⊆ D) (hp : ∀ s ∈ A, ∀ t ∈ B, P s t → Q s t) :
    pins.pairMass A B P ≤ pins.pairMass C D Q := by
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg ha (f := fun s =>
    pins.weight s * pins.mass (D.filter (Q s))) (fun _ _ _ => mul_nonneg (pins.positive _).le (pins.mass_nonneg _)))
  apply Finset.sum_le_sum
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (pins.positive s).le
  apply pins.mass_mono
  intro t ht
  obtain ⟨ht',h⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hb ht',hp _ hs _ ht' h⟩

theorem pair_flip (A B : Finset (Finset I)) (P : Relation I) :
    pins.pairMass A B (fun s t => P t s) = pins.pairMass B A P := by
  simp only [pairMass,mass,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pair_or (A B : Finset (Finset I)) (P Q : Relation I) :
    pins.pairMass A B (fun s t => P s t ∨ Q s t) ≤ pins.pairMass A B P + pins.pairMass A B Q := by
  unfold pairMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (pins.positive s).le
  exact (pins.mass_mono (by intro t ht; simpa [and_or_left] using ht)).trans (pins.mass_union ..)

theorem pair_full (A B : Finset (Finset I)) :
    pins.pairMass A B (fun _ _ => True) = pins.mass A * pins.mass B := by
  simp [pairMass,mass,Finset.sum_mul]

theorem pair_bound {P : Relation I} {M : ℝ} (hh : ∀ s ∈ A, pins.mass (B.filter (P s)) ≤ M) :
    pins.pairMass A B P ≤ pins.mass A * M := by
  rw [mass,Finset.sum_mul]
  exact Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hh s hs) (pins.positive _).le

theorem pair_exists {P : Relation I} {M : ℝ} (hh : pins.mass A * M < pins.pairMass A B P) :
    ∃ s ∈ A, M < pins.mass (B.filter (P s)) := by
  by_contra! hn
  exact hh.not_ge (pins.pair_bound hn)

theorem pair_exception {P : Relation I} (A B : Finset (Finset I)) :
    pins.mass (A.filter fun s => ∀ t ∈ B, P s t) * pins.mass B ≤ pins.pairMass A B P := by
  rw [← pair_full]
  exact pins.pair_mono (Finset.filter_subset ..) Finset.Subset.rfl
    (fun _ hs t ht _ => (Finset.mem_filter.mp hs).2 t ht)

end OAI.Geometry.Hirsch.Layer.Pins

namespace OAI.Geometry.Hirsch.Layer.Trial.Core

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)
  {rank : I → ℕ} (core : Core rank) (list : Finset (Finset I))

def Fails (s t : Finset I) := ∃ g ∈ s, g ∈ t ∨ ¬(core.near g).Minimal t

theorem bad_pairs {K : ℕ} {loss key : ℝ} (hk : 0 ≤ key) (hl : 0 ≤ loss)
    (hsize : ∀ s ∈ list, s.card ≤ K)
    (hkey : ∀ g, pins.mass (list.filter (g ∈ ·)) ≤ key)
    (hloss : ∀ g, (∃ s ∈ list, g ∈ s) → pins.mass (list.filter fun t => ¬(core.near g).Minimal t) ≤ loss) :
    pins.pairMass list list (fun s t => ¬core.Good s t) ≤ 2*pins.mass list * (K*(key+loss)) := by
  have one : pins.pairMass list list core.Fails ≤ pins.mass list * (K*(key+loss)) := by
    apply pins.pair_bound
    intro s hs
    let f := fun g => list.filter (g ∈ ·) ∪ list.filter (fun t => ¬(core.near g).Minimal t)
    calc
      _ ≤ ∑ g ∈ s, pins.mass (f g) := by
        apply pins.mass_cover
        intro t ht
        obtain ⟨ht,g,hg,hh⟩ := Finset.mem_filter.mp ht
        exact ⟨g,hg,by simpa [f,ht] using hh⟩
      _ ≤ ∑ _ ∈ s, (key+loss) := Finset.sum_le_sum fun g hg =>
        (pins.mass_union ..).trans (add_le_add (hkey g) (hloss g ⟨s,hs,hg⟩))
      _ ≤ _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hsize s hs)) (add_nonneg hk hl)
  have cover : ∀ s ∈ list, ∀ t ∈ list, ¬core.Good s t → core.Fails s t ∨ core.Fails t s := by
    intro s _ t _ hn
    by_contra! hh
    apply hn
    exact ⟨Finset.disjoint_left.mpr (fun g hg ht => hh.1 ⟨g,hg,.inl ht⟩),
      fun g hg => by_contra (fun ht => hh.1 ⟨g,hg,.inr ht⟩),
      fun g hg => by_contra (fun ht => hh.2 ⟨g,hg,.inr ht⟩)⟩
  have both := (pins.pair_mono Finset.Subset.rfl Finset.Subset.rfl cover).trans
    (pins.pair_or list list core.Fails (fun s t => core.Fails t s))
  rw [pins.pair_flip list list core.Fails] at both
  linarith

theorem heavy {beta : ℝ} (hc : ∀ s ∈ list, core.Cut s)
    (hb : pins.pairMass list list (fun s t => ¬core.Good s t) ≤ beta)
    (hh : 3*beta < (pins.mass list)^2) :
    (∃ s ∈ list, pins.mass list / 3 < pins.mass (list.filter (core.Newer s))) ∧
    (∃ t ∈ list, pins.mass list / 3 < pins.mass (list.filter (fun s => core.Newer s t))) := by
  let old := fun s t => core.Newer t s
  let bad := fun s t => ¬core.Good s t
  let good := fun s t => core.Newer s t ∨ old s t
  have sub : ∀ s ∈ list, ∀ t ∈ list, True → bad s t ∨ good s t := by
    intro s hs t ht _
    by_cases hg : core.Good s t
    · exact .inr (hg.order (hc _ hs) (hc _ ht))
    · exact .inl hg
  have bound := (pins.pair_mono Finset.Subset.rfl Finset.Subset.rfl sub).trans
    ((pins.pair_or list list bad good).trans (add_le_add hb (pins.pair_or list list core.Newer old)))
  rw [pins.pair_full] at bound
  have he : pins.pairMass list list old = pins.pairMass list list core.Newer :=
    pins.pair_flip list list core.Newer
  have low : pins.mass list * (pins.mass list / 3) < pins.pairMass list list core.Newer := by linarith
  exact ⟨pins.pair_exists low,pins.pair_exists (P := old) (low.trans_eq he.symm)⟩

end OAI.Geometry.Hirsch.Layer.Trial.Core
