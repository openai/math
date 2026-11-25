import OAI.Geometry.Hirsch.Screens

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Trial (I : Type) := Set (List I)

namespace Trial

variable {I Z : Type} (place : I → Z)

def Hit (s : Finset I) (path : List I) := ∃ g ∈ path, g ∈ s

def Covers (paths : Trial I) (s : Finset I) := ∀ path ∈ paths, Hit s path

def Minimal (paths : Trial I) (s : Finset I) := ∀ t ⊂ s, ¬paths.Covers t

def Refines (p q : Trial I) := ∀ s, q.Covers s → p.Covers s

def Transfers (short long : Trial I) (next : I → Trial I) :=
  ∀ pre g rest, pre ++ g :: rest ∈ short → ∀ s, long.Covers s → ¬Hit s pre → g ∉ s → (next g).Covers s

def keysAt (path : List I) (sites : Finset Z) := path.toFinset.filter (fun g => place g ∈ sites)

def Bounded (paths : Trial I) (e : ℕ) := ∀ path ∈ paths, ∀ j, (keysAt place path {j}).card ≤ e

variable {place} {s t : Finset I} {paths : Trial I} {path : List I}

theorem Hit.mono (hh : Hit s path) (hs : s ⊆ t) : Hit t path := by
  obtain ⟨g,hg,hm⟩ := hh
  exact ⟨g,hg,hs hm⟩

theorem Covers.mono (hc : paths.Covers s) (hs : s ⊆ t) : paths.Covers t := fun l hl => (hc l hl).mono hs

theorem Covers.nonempty (hc : paths.Covers s) (hn : paths.Nonempty) : s.Nonempty := by
  obtain ⟨l,hl⟩ := hn
  obtain ⟨g,_,hg⟩ := hc l hl
  exact ⟨g,hg⟩

theorem missed (hn : ¬paths.Covers s) : ∃ path ∈ paths, ¬Hit s path := by
  unfold Covers at hn
  push Not at hn
  exact hn

theorem Hit.first (hh : Hit s path) : ∃ pre g rest, path = pre ++ g :: rest ∧ ¬Hit s pre ∧ g ∈ s := by
  induction path with
  | nil => simp [Hit] at hh
  | cons g rest ih =>
    by_cases hg : g ∈ s
    · exact ⟨[],g,rest,rfl,by simp [Hit],hg⟩
    · have hr : Hit s rest := by simpa [Hit,hg] using hh
      obtain ⟨pre,j,tail,rfl,hn,hj⟩ := ih hr
      exact ⟨g :: pre,j,tail,rfl,by simpa [Hit,hg] using hn,hj⟩

theorem Minimal.essential (hm : paths.Minimal s) (hc : paths.Covers s) {g : I} (hg : g ∈ s) :
    ∃ pre rest, pre ++ g :: rest ∈ paths ∧ ¬ Hit s pre := by
  obtain ⟨path,hp,hn⟩ := missed (hm _ (Finset.erase_ssubset hg))
  obtain ⟨pre,j,rest,rfl,hpre,hj⟩ := (hc path hp).first
  have : j = g := by
    by_contra h
    exact hn ⟨j,by simp,Finset.mem_erase.mpr ⟨h,hj⟩⟩
  subst j
  exact ⟨pre,rest,hp,hpre⟩

@[simp] theorem mem_at {sites : Finset Z} {g : I} :
    g ∈ keysAt place path sites ↔ g ∈ path ∧ place g ∈ sites := by simp [keysAt]

theorem Bounded.sites {e : ℕ} (hb : paths.Bounded place e) (hp : path ∈ paths) (sites : Finset Z) :
    (keysAt place path sites).card ≤ sites.card * e := by
  induction sites using Finset.induction_on with
  | empty => simp [keysAt]
  | @insert j sites hj ih =>
    have he : keysAt place path (insert j sites) = keysAt place path sites ∪ keysAt place path {j} := by
      ext; simp; tauto
    rw [he,Finset.card_insert_of_notMem hj,add_mul,one_mul]
    exact (Finset.card_union_le ..).trans (Nat.add_le_add ih (hb _ hp _))

structure Tests (place : I → Z) (e d : ℕ) where
  short : Trial I
  long : Trial I
  next : I → Trial I
  refines : short.Refines long
  transfer : short.Transfers long next
  shortBound : short.Bounded place e
  nextBound : ∀ g, (next g).Bounded place d

namespace Tests

variable {e d : ℕ} (tests : Tests place e d)

def Available (a : Finset I) :=
  ∀ g ∈ a, ∃ path ∈ tests.next g, ∀ j ∈ path, j ∈ a → place j = place g

def Branches (a : Finset I) (K M : ℕ) :=
  ∀ s ⊆ a, s.card < K → ¬tests.short.Covers s →
    ∃ choices : Finset I, choices.card ≤ M ∧ ∀ t ⊆ a, s ⊆ t → tests.long.Covers t →
      ∃ g ∈ choices, g ∈ t ∧ g ∉ s

theorem branch {a : Finset I} (ha : tests.Available a) (K : ℕ) :
    tests.Branches a K (K*e+1+d) := by
  intro s hsa hK hmiss
  obtain ⟨path,hp,hn⟩ := missed hmiss
  let sites := s.image place
  let first := keysAt place path sites
  have hs : sites.card ≤ K := Finset.card_image_le.trans hK.le
  have hsize : first.card ≤ K*e := (tests.shortBound.sites hp sites).trans (Nat.mul_le_mul_right _ hs)
  have avoid : ∀ g ∈ path, g ∉ s := fun g hg hm => hn ⟨g,hg,hm⟩
  by_cases hh : Hit (a \ first) path
  swap
  · refine ⟨first,by omega,fun t ht _ hc => ?_⟩
    obtain ⟨g,hg,hg'⟩ := tests.refines _ hc _ hp
    exact ⟨g,by_contra (fun h => hh ⟨g,hg,Finset.mem_sdiff.mpr ⟨ht hg',h⟩⟩),hg',avoid g hg⟩
  obtain ⟨pre,g,rest,he,hpre,hg⟩ := hh.first
  have hp' : g ∈ path := by simp [he]
  obtain ⟨hga,hnf⟩ := Finset.mem_sdiff.mp hg
  have free : place g ∉ sites := fun h => hnf (mem_at.mpr ⟨hp',h⟩)
  obtain ⟨tail,ht,hallow⟩ := ha g hga
  let extra := keysAt place tail {place g}
  have hex : extra.card ≤ d := tests.nextBound g tail ht _
  refine ⟨insert g (first ∪ extra),?_,fun t hta _ hc => ?_⟩
  · have := Finset.card_insert_le g (first ∪ extra)
    have := Finset.card_union_le first extra
    omega
  by_cases hgf : ∃ j ∈ first, j ∈ t
  · obtain ⟨j,hj,hm⟩ := hgf
    exact ⟨j,by simp [hj],hm,avoid j (mem_at.mp hj).1⟩
  by_cases hgt : g ∈ t
  · exact ⟨g,by simp,hgt,avoid g hp'⟩
  have sub : t ⊆ a \ first := fun j hj => Finset.mem_sdiff.mpr ⟨hta hj,fun h => hgf ⟨j,h,hj⟩⟩
  obtain ⟨j,hj,hm⟩ := tests.transfer _ _ _ (he ▸ hp) t hc (fun h => hpre (h.mono sub)) hgt tail ht
  have hsite := hallow j hj (hta hm)
  have hj' : j ∈ extra := mem_at.mpr ⟨hj,Finset.mem_singleton.mpr hsite⟩
  refine ⟨j,by simp [hj'],hm,fun h => ?_⟩
  exact free (hsite ▸ Finset.mem_image_of_mem _ h)

end Tests
end Trial
end OAI.Geometry.Hirsch.Layer
