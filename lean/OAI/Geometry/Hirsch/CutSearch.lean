import OAI.Geometry.Hirsch.CutPaths

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial.Tests

variable {I Z : Type} {place : I → Z} {e d K M : ℕ} {tests : Tests place e d} {a : Finset I}

def Frontier (tests : Tests place e d) (a : Finset I) (K : ℕ) (start : Finset I)
    (leaves : Finset (Finset I)) :=
  (∀ s ∈ leaves, (s ⊆ a ∧ s.card ≤ K) ∧ (s.card = K ∨ tests.short.Covers s)) ∧
    ∀ t ⊆ a, start ⊆ t → tests.long.Covers t → ∃ s ∈ leaves, s ⊆ t

theorem Branches.search (hb : tests.Branches a K M) (k : ℕ) (s : Finset I)
    (hs : s ⊆ a) (hk : s.card + k = K) :
    ∃ leaves, leaves.card ≤ (M+1)^k ∧ tests.Frontier a K s leaves := by
  induction k generalizing s with
  | zero =>
    refine ⟨{s},by simp,?_,fun t _ ht _ => ⟨s,by simp,ht⟩⟩
    simpa using (show (s ⊆ a ∧ s.card ≤ K) ∧ (s.card = K ∨ tests.short.Covers s) from ⟨⟨hs,by omega⟩,.inl (by omega)⟩)
  | succ k ih =>
    by_cases hc : tests.short.Covers s
    · refine ⟨{s},by simp only [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by omega),
        ?_,fun t _ ht _ => ⟨s,by simp,ht⟩⟩
      simp [hs,hc,show s.card ≤ K by omega]
    obtain ⟨choices,hm,hh⟩ := hb s hs (by omega) hc
    let opts := choices.filter (fun g => g ∈ a ∧ g ∉ s)
    have next : ∀ g : ↥opts, ∃ leaves, leaves.card ≤ (M+1)^k ∧ tests.Frontier a K (insert g.val s) leaves := by
      intro g
      obtain ⟨_,hin,hout⟩ := Finset.mem_filter.mp g.property
      apply ih _ (Finset.insert_subset hin hs)
      rw [Finset.card_insert_of_notMem hout]
      omega
    choose src hn hp using next
    refine ⟨Finset.univ.biUnion src,?_,?_,?_⟩
    · calc
        _ ≤ ∑ i, (src i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ : ↥opts, (M+1)^k := Finset.sum_le_sum fun i _ => hn i
        _ ≤ (M+1)^(k+1) := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,pow_succ']
          apply Nat.mul_le_mul_right
          exact ((Finset.card_filter_le ..).trans hm).trans (by omega)
    · intro u hu
      obtain ⟨g,_,hu⟩ := Finset.mem_biUnion.mp hu
      exact (hp g).1 _ hu
    · intro t ht hst hl
      obtain ⟨g,hg,hgt,hgs⟩ := hh _ ht hst hl
      let opt : ↥opts := ⟨g,Finset.mem_filter.mpr ⟨hg,ht hgt,hgs⟩⟩
      obtain ⟨u,hu,hs⟩ := (hp opt).2 t ht (Finset.insert_subset hgt hst) hl
      exact ⟨u,Finset.mem_biUnion.mpr ⟨opt,Finset.mem_univ _,hu⟩,hs⟩

def capacity (K e d : ℕ) := (K*e+1+d+1)^K

theorem Available.frontier (ha : tests.Available a) (K : ℕ) :
    ∃ leaves, leaves.card ≤ capacity K e d ∧ tests.Frontier a K ∅ leaves :=
  (tests.branch ha K).search K ∅ (Finset.empty_subset _) (by simp)

def Listed (tests : Tests place e d) (K : ℕ) (s : Finset I) :=
  s.card ≤ K ∧ tests.long.Covers s ∧ tests.short.Minimal s

theorem Frontier.includes {leaves : Finset (Finset I)} (hf : tests.Frontier a K ∅ leaves)
    {s : Finset I} (hs : tests.Listed K s) (ha : s ⊆ a) : s ∈ leaves := by
  obtain ⟨t,ht,hsub⟩ := hf.2 s ha (Finset.empty_subset _) hs.2.1
  suffices t = s from this ▸ ht
  rcases (hf.1 t ht).2 with he | hc
  · exact Finset.eq_of_subset_of_card_le hsub (he ▸ hs.1)
  · exact by_contra (fun hn => hs.2.2 t (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hn⟩) hc)

theorem Available.multiplicity (ha : tests.Available a) {list : Finset (Finset I)}
    (hl : ∀ s ∈ list, tests.Listed K s ∧ s ⊆ a) : list.card ≤ capacity K e d := by
  obtain ⟨leaves,hc,hf⟩ := ha.frontier K
  exact (Finset.card_le_card fun s hs => hf.includes (hl _ hs).1 (hl _ hs).2).trans hc

end OAI.Geometry.Hirsch.Layer.Trial.Tests
