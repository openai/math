import OAI.Geometry.Hirsch.CutSearch

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I Z : Type} [Fintype Ω] {p : Law Ω}

namespace Law

theorem union_finset (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) :
    p.prob (fun x => ∃ i ∈ s, e i x) ≤ ∑ i ∈ s, p.prob (e i) := by
  have hh := p.union (fun i : ↥s => e i.val)
  rw [Finset.sum_coe_sort s (fun i => p.prob (e i))] at hh
  simpa only [Subtype.exists,exists_prop] using hh

theorem count (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) :
    ∑ i ∈ s, p.prob (e i) = p.mean (fun x => ((s.filter (fun i => e i x)).card : ℝ)) := by
  simp_rw [← mean_ind]
  rw [← mean_sum]
  apply p.mean_congr
  intro x
  simp [ind]

theorem multiplicity (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) (event : Ω → Prop) {M : ℕ}
    (hb : ∀ x, (s.filter (fun i => e i x)).card ≤ M)
    (he : ∀ i ∈ s, ∀ x, e i x → event x) :
    ∑ i ∈ s, p.prob (e i) ≤ M * p.prob event := by
  rw [count,← mean_ind,← mean_scale]
  apply p.mean_mono
  intro x
  by_cases hx : event x
  · simpa [ind,hx] using hb x
  · have hzero : s.filter (fun i => e i x) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i hi hh => hx (he i hi x hh))
    simp [ind,hx,hzero]

end Law

namespace Pins

variable (pins : Pins p I)

def mass (family : Finset (Finset I)) := ∑ s ∈ family, pins.weight s

theorem mass_nonneg (family : Finset (Finset I)) : 0 ≤ pins.mass family :=
  Finset.sum_nonneg fun _ _ => (pins.positive _).le

theorem mass_mono {a b : Finset (Finset I)} (h : a ⊆ b) : pins.mass a ≤ pins.mass b :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => (pins.positive _).le

theorem mass_split (s : Finset (Finset I)) (P : Finset I → Prop) [DecidablePred P] :
    pins.mass (s.filter P) + pins.mass (s.filter fun t => ¬P t) = pins.mass s :=
  Finset.sum_filter_add_sum_filter_not ..

theorem extra (s a : Finset I) (hn : ∀ i ∈ a, i ∉ s) :
    p.prob (fun x => s ⊆ pins.success x ∧ ∃ i ∈ a, i ∈ pins.success x) ≤
      a.card * pins.rate * pins.weight s := by
  calc
    _ ≤ p.prob (fun x => ∃ i ∈ a, insert i s ⊆ pins.success x) :=
      p.mono (fun _ ⟨hs,i,hi,hm⟩ => ⟨i,hi,Finset.insert_subset hm hs⟩)
    _ ≤ ∑ i ∈ a, p.prob (fun x => insert i s ⊆ pins.success x) := p.union_finset ..
    _ = ∑ _ ∈ a, pins.rate * pins.weight s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pins.prob,Finset.card_insert_of_notMem (hn i hi),pow_succ']
      rfl
    _ = _ := by simp [mul_assoc]

end Pins

namespace Trial

variable {place : I → Z} {K e d : ℕ} {tests : Tests place e d}

structure Gates (pins : Pins p I) (place : I → Z) (K : ℕ) (gamma alpha : ℝ) where
  pass : Ω → Finset I
  pinned : ∀ x, pass x ⊆ pins.success x
  bad : I → Ω → Prop
  screen : ∀ x g, g ∈ pass x → ¬bad g x
  possible : ∀ s : Finset I, s.card ≤ K → (∃ x, s ⊆ pass x) →
    gamma * pins.weight s ≤ p.prob (fun x => s ⊆ pass x)
  compatible : ∀ x g, g ∈ pass x → ∀ s ⊆ pass x, s.card ≤ K → pins.given (bad g) s ≤ alpha

namespace Gates

variable {pins : Pins p I} {gamma alpha : ℝ} (gate : Gates pins place K gamma alpha)

def Serves (tests : Tests place e d) :=
  ∀ x g, ¬gate.bad g x → ∃ path ∈ tests.next g, ∀ j ∈ path, j ∈ gate.pass x → place j = place g

theorem Serves.available {gate : Gates pins place K gamma alpha} (hs : gate.Serves tests) (x : Ω) :
    tests.Available (gate.pass x) := fun g hg => hs x g (gate.screen _ _ hg)

def ListAt (tests : Tests place e d) (family : Finset (Finset I)) :=
  ∀ s ∈ family, tests.Listed K s ∧ ∃ x, s ⊆ gate.pass x

variable {gate} {family : Finset (Finset I)}

theorem ListAt.sub {sub : Finset (Finset I)} (hl : gate.ListAt tests family) (hs : sub ⊆ family) :
    gate.ListAt tests sub := fun s hh => hl s (hs hh)

theorem ListAt.estimate {Γ : Type} [Fintype Γ] (hl : gate.ListAt tests family) (hs : gate.Serves tests)
    (q : Law Γ) (original : Γ → Ω) (hit : Finset I → Γ → Prop) (event : Γ → Prop)
    (lower : ∀ s ∈ family, gamma * pins.weight s ≤ q.prob (hit s))
    (pass : ∀ s ∈ family, ∀ x, hit s x → s ⊆ gate.pass (original x))
    (implies : ∀ s ∈ family, ∀ x, hit s x → event x) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * q.prob event := by
  rw [Pins.mass,Finset.mul_sum]
  apply (Finset.sum_le_sum lower).trans
  apply q.multiplicity _ _ _ _ implies
  intro x
  apply (hs.available (original x)).multiplicity
  intro s hh
  obtain ⟨hf,hx⟩ := Finset.mem_filter.mp hh
  exact ⟨(hl _ hf).1,pass s hf x hx⟩

theorem ListAt.bound (hl : gate.ListAt tests family) (hs : gate.Serves tests) (event : Ω → Prop)
    (implies : ∀ s ∈ family, ∀ x, s ⊆ gate.pass x → event x) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * p.prob event :=
  hl.estimate hs p id (fun s x => s ⊆ gate.pass x) event
    (fun s hf => gate.possible _ (hl s hf).1.1 (hl s hf).2) (fun _ _ _ h => h) implies

end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
