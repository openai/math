import OAI.Geometry.Hirsch.CutLoss

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial

variable {I : Type} {s t : Finset I}

theorem Hit.append_left {p q : List I} (hh : Hit s p) : Hit s (p ++ q) := by
  obtain ⟨g,hg,hm⟩ := hh
  exact ⟨g,List.mem_append_left _ hg,hm⟩

def Before (paths : Trial I) (s t : Finset I) :=
  ∀ pre g rest, pre ++ g :: rest ∈ paths → g ∈ t → Hit s pre

theorem Before.missed {paths : Trial I} (hb : paths.Before s t) {pre tail : List I}
    (hh : pre ++ tail ∈ paths) (hn : ¬Hit s pre) : ¬Hit t pre := by
  intro hit
  obtain ⟨a,g,b,rfl,_,hg⟩ := hit.first
  exact hn (hb a g (b ++ tail) (by simpa using hh) hg).append_left

def Falls (rank : I → ℕ) (next : I → Trial I) :=
  ∀ g path, path ∈ next g → ∀ j ∈ path, rank j < rank g

theorem Falls.older {rank : I → ℕ} {next : I → Trial I} (hf : Falls rank next) {g : I}
    (hc : (next g).Covers s) (hm : (next g).Minimal s) : ∀ j ∈ s, rank j < rank g := by
  intro j hj
  obtain ⟨pre,rest,hp,_⟩ := hm.essential hc hj
  exact hf _ _ hp j (by simp)

structure Core (rank : I → ℕ) where
  short : Trial I
  long : Trial I
  paths : Trial I
  near : I → Trial I
  far : I → Trial I
  inhabited : short.Nonempty
  includes : short ⊆ paths
  refines : short.Refines long
  transfer : paths.Transfers long far
  nested : ∀ g, (near g).Refines (far g)
  falls : Falls rank near

namespace Core

variable {rank : I → ℕ} (core : Core rank)

def Cut (s : Finset I) := core.long.Covers s ∧ core.short.Minimal s

def Good (s t : Finset I) :=
  Disjoint s t ∧ (∀ g ∈ s, (core.near g).Minimal t) ∧ (∀ g ∈ t, (core.near g).Minimal s)

def Newer (s t : Finset I) := core.Good s t ∧ core.paths.Before s t ∧
  ∀ g ∈ s, (core.far g).Covers t ∧ ∀ j ∈ t, rank j < rank g

variable {core}

theorem Good.symm (hg : core.Good s t) : core.Good t s := ⟨hg.1.symm,hg.2.2,hg.2.1⟩

theorem Good.at_key (hg : core.Good s t) (ht : core.Cut t) {pre rest : List I} {g : I}
    (hp : pre ++ g :: rest ∈ core.paths) (hm : g ∈ s) (hn : ¬Hit t pre) :
    (core.far g).Covers t ∧ ∀ j ∈ t, rank j < rank g := by
  have hc := core.transfer _ _ _ hp _ ht.1 hn (Finset.disjoint_left.mp hg.1 hm)
  exact ⟨hc,core.falls.older (core.nested g _ hc) (hg.2.1 g hm)⟩

theorem Good.newer (hg : core.Good s t) (hs : core.Cut s) (ht : core.Cut t)
    (hn : ¬core.paths.Before t s) : core.Newer s t := by
  unfold Before at hn
  push Not at hn
  obtain ⟨pre,g,rest,hp,hm,hn⟩ := hn
  have hb := (hg.at_key ht hp hm hn).2
  have first : core.paths.Before s t := by
    intro a j b hh hj
    by_contra hmiss
    exact (hb j hj).not_gt ((hg.symm.at_key hs hh hj hmiss).2 g hm)
  refine ⟨hg,first,fun j hj => ?_⟩
  obtain ⟨a,b,hh,hmiss⟩ := hs.2.essential (core.refines _ hs.1) hj
  have hf := core.includes hh
  exact hg.at_key ht hf hj (first.missed hf hmiss)

theorem Good.order (hg : core.Good s t) (hs : core.Cut s) (ht : core.Cut t) :
    core.Newer s t ∨ core.Newer t s := by
  by_cases hf : core.paths.Before t s
  swap
  · exact .inl (hg.newer hs ht hf)
  right
  apply hg.symm.newer ht hs
  intro hb
  obtain ⟨path,hp⟩ := core.inhabited
  obtain ⟨pre,g,rest,he,hn,hm⟩ := (core.refines _ hs.1 _ hp).first
  have hh := core.includes (he ▸ hp)
  exact hb.missed hh hn (hf _ _ _ hh hm)

end Core
end OAI.Geometry.Hirsch.Layer.Trial
