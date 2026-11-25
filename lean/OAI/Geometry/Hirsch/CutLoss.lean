import OAI.Geometry.Hirsch.CutLinks

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I J : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)

namespace Pins

theorem mass_cover (src : Finset (Finset I)) (indices : Finset J) (sets : J → Finset (Finset I))
    (covered : ∀ s ∈ src, ∃ j ∈ indices, s ∈ sets j) :
    pins.mass src ≤ ∑ j ∈ indices, pins.mass (sets j) := by
  calc
    _ ≤ ∑ s ∈ src, ∑ j ∈ indices, if s ∈ sets j then pins.weight s else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨j,hj,hm⟩ := covered s hs
      let f := fun i => if s ∈ sets i then pins.weight s else 0
      have hn : ∀ i ∈ indices, 0 ≤ f i := fun _ _ => by unfold f; split <;> simp [(pins.positive s).le]
      simpa [f,hm] using Finset.single_le_sum hn hj
    _ ≤ _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_filter]
      exact pins.mass_mono (fun _ h => (Finset.mem_filter.mp h).2)

theorem mass_union (a b : Finset (Finset I)) : pins.mass (a ∪ b) ≤ pins.mass a + pins.mass b := by
  have he := Finset.sum_union_inter (s₁ := a) (s₂ := b) (f := pins.weight)
  exact (le_add_of_nonneg_right (pins.mass_nonneg (a ∩ b))).trans_eq he

end Pins

namespace Trial

theorem plateau (paths : ℕ → Trial I) {s : Finset I} {k : ℕ} (hk : s.card ≤ k)
    (hc : (paths (k+1)).Covers s) :
    ∃ j ≤ k, ∃ t ⊆ s, (paths (j+1)).Covers t ∧ (paths j).Minimal t := by
  induction k generalizing s with
  | zero =>
    refine ⟨0,le_rfl,s,Finset.Subset.rfl,hc,fun u hu => ?_⟩
    have := Finset.card_lt_card hu
    omega
  | succ k ih =>
    by_cases hm : (paths (k+1)).Minimal s
    · exact ⟨k+1,le_rfl,s,Finset.Subset.rfl,hc,hm⟩
    unfold Minimal at hm
    push Not at hm
    obtain ⟨u,hu,huc⟩ := hm
    obtain ⟨j,hj,t,ht,hc,hm⟩ := ih (by have := Finset.card_lt_card hu; omega) huc
    exact ⟨j,by omega,t,ht.trans hu.subset,hc,hm⟩

variable {pins} {Z : Type} {place : I → Z} {K e d : ℕ} {gamma alpha : ℝ}

namespace Gates

variable (gate : Gates pins place K gamma alpha)

def Possible (s : Finset I) := ∃ x, s ⊆ gate.pass x

def cuts [Fintype I] (short long : Trial I) :=
  Finset.univ.filter fun s : Finset I => s.card ≤ K ∧ long.Covers s ∧ short.Minimal s ∧ gate.Possible s

@[simp] theorem mem_cuts [Fintype I] {short long : Trial I} {s : Finset I} :
    s ∈ gate.cuts short long ↔ s.card ≤ K ∧ long.Covers s ∧ short.Minimal s ∧ gate.Possible s := by
  simp [cuts]

theorem listed [Fintype I] (tests : Tests place e d) :
    gate.ListAt tests (gate.cuts tests.short tests.long) := by
  intro s hs
  obtain ⟨hk,hc,hm,hp⟩ := gate.mem_cuts.mp hs
  exact ⟨⟨hk,hc,hm⟩,hp⟩

structure Bounds (family : Finset (Finset I)) (M A : ℝ) : Prop where
  mass : pins.mass family ≤ M
  possible : ∀ s ∈ family, s.card ≤ K ∧ gate.Possible s
  link : ∀ s, pins.mass (family.filter (s ⊂ ·)) ≤ A*pins.weight s

variable {gate} {M A : ℝ} {family : Finset (Finset I)}

theorem bounds [Fintype I] {tests : Tests place e d} (hs : gate.Serves tests)
    (hg : 0 < gamma) (ha : 0 ≤ alpha) (change : ∀ z, Nonempty (gate.Resample z))
    {U : ℝ} (cap : p.prob (fun x => tests.long.Covers (gate.pass x)) ≤ U)
    (hM : (Tests.capacity K e d : ℝ)*U ≤ gamma*M)
    (hA : (Tests.capacity K e d : ℝ)*(alpha+(K*e+d+1)*pins.rate) ≤ gamma*A) :
    gate.Bounds (gate.cuts tests.short tests.long) M A := by
  have hl := gate.listed tests
  refine ⟨?_,fun s hh => ⟨(hl s hh).1.1,(hl s hh).2⟩,fun s => ?_⟩
  · apply le_of_mul_le_mul_left _ hg
    exact (hl.bound hs _ (fun t ht _ hx => (hl t ht).1.2.1.mono hx)).trans
      ((mul_le_mul_of_nonneg_left cap (by positivity)).trans hM)
  · apply le_of_mul_le_mul_left _ hg
    rw [← mul_assoc]
    apply le_trans _ (mul_le_mul_of_nonneg_right hA (pins.positive s).le)
    exact (hl.sub (Finset.filter_subset ..)).link hs s change ha (fun _ hh => (Finset.mem_filter.mp hh).2)

theorem Bounds.key (hb : gate.Bounds family M A) (g : I) :
    pins.mass (family.filter (g ∈ ·)) ≤ (1+A)*pins.rate := by
  let one : Finset I := {g}
  have hsub : family.filter (g ∈ ·) ⊆ {one} ∪ family.filter (one ⊂ ·) := by
    intro t ht
    obtain ⟨ht,hg⟩ := Finset.mem_filter.mp ht
    by_cases he : t = one
    · simp [he]
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨ht,Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hg,Ne.symm he⟩⟩)
  apply (pins.mass_mono hsub).trans
  apply (pins.mass_union ..).trans
  have hh := hb.link one
  have he : pins.weight one = pins.rate := by simp [one,Pins.weight]
  rw [he] at hh
  have : pins.mass {one} = pins.rate := by simp [Pins.mass,he]
  linarith

theorem Bounds.loss [Fintype I] (hb : gate.Bounds family M A) (ha : 0 ≤ A) (paths : ℕ → Trial I)
    (bound : ∀ j ≤ K, pins.mass (gate.cuts (paths j) (paths (j+1))) ≤ M) :
    pins.mass (family.filter fun s => ¬(paths (K+1)).Minimal s) ≤ (K+1)*A*M := by
  let cuts := fun j => gate.cuts (paths j) (paths (j+1))
  let hits := fun j => family.filter fun s => ∃ t ∈ cuts j, t ⊂ s
  have one : ∀ j ≤ K, pins.mass (hits j) ≤ A*M := by
    intro j hj
    calc
      _ ≤ ∑ t ∈ cuts j, pins.mass (family.filter (t ⊂ ·)) := by
        apply pins.mass_cover
        intro s hs
        obtain ⟨hs,t,ht,hts⟩ := Finset.mem_filter.mp hs
        exact ⟨t,ht,Finset.mem_filter.mpr ⟨hs,hts⟩⟩
      _ ≤ ∑ t ∈ cuts j, A*pins.weight t := Finset.sum_le_sum fun t _ => hb.link t
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (bound j hj) ha
  calc
    _ ≤ ∑ j ∈ Finset.range (K+1), pins.mass (hits j) := by
      apply pins.mass_cover
      intro s hs
      obtain ⟨hs,hm⟩ := Finset.mem_filter.mp hs
      obtain ⟨hk,x,hx⟩ := hb.possible _ hs
      unfold Minimal at hm
      push Not at hm
      obtain ⟨u,hu,hc⟩ := hm
      obtain ⟨j,hj,t,ht,hc,hm⟩ := plateau paths ((Finset.card_le_card hu.subset).trans hk) hc
      have hts : t ⊂ s := lt_of_le_of_lt ht hu
      exact ⟨j,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hs,t,gate.mem_cuts.mpr
        ⟨(Finset.card_le_card hts.subset).trans hk,hc,hm,x,hts.subset.trans hx⟩,hts⟩⟩
    _ ≤ ∑ _ ∈ Finset.range (K+1), A*M :=
      Finset.sum_le_sum fun j hj => one j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp [mul_assoc]

end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
