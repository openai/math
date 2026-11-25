import OAI.Geometry.Hirsch.Grid

noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

variable {X Ω : Type} [Fintype Ω] {D base bits chance h k : ℕ} [NeZero base] [NeZero bits]
  {p : Law Ω} {w : World X (base^h*(k+2))}

def width (base k i : ℕ) := base^i*(k+2)

theorem width_next (base k i : ℕ) : width base k (i+1) = width base k i * base := by
  simp only [width,pow_succ]; ring

def Hierarchy (w : World X (base^h*(k+2))) (p : Law Ω) (chance D : ℕ) :=
  ∀ i : Fin h, w.Potential p chance D (width base k i) base

abbrev Address (base bits : ℕ) := Fin base ↪ (Fin bits → Bool)

def read (w : World X (base^h*(k+2))) (key : Address base bits) (i : Fin h) (x : X) :=
  key (w.digit (width base k i) base x)

namespace Hierarchy

variable (seq : Hierarchy w p chance D) (key : Address base bits) (x : X) (tuple : Fin h → Ω)

def Excludes (mask : Fin h → Fin bits) (low : ℕ) (y : X) :=
  w.Blank (k+2) y ∨ ∃ i : Fin h, low ≤ i.val ∧
    (tuple i ∉ (seq i).sets y ∨ w.read key i y (mask i) ≠ w.read key i x (mask i))

theorem distinguish (i : Fin h) (j : ℕ) (hj : j ≠ w.block (width base k i) x) :
    ∃ b, ∀ y, w.block (width base k (i.val+1)) y = w.block (width base k (i.val+1)) x →
      w.block (width base k i) y = j → w.read key i y b ≠ w.read key i x b := by
  classical
  let P := fun y => w.block (width base k (i.val+1)) y = w.block (width base k (i.val+1)) x ∧
    w.block (width base k i) y = j
  by_cases he : ∃ y, P y
  swap
  · exact ⟨0,fun y hp hs => (he ⟨y,hp,hs⟩).elim⟩
  obtain ⟨y,hp,hs⟩ := he
  have hn : w.read key i y ≠ w.read key i x := by
    intro hh
    rw [width_next] at hp
    exact hj (hs.symm.trans (w.index_inj hp (key.injective hh)))
  obtain ⟨b,hb⟩ := Function.ne_iff.mp hn
  refine ⟨b,fun z _ hz => ?_⟩
  simpa only [read,digit,hz,hs] using hb

theorem from_blank (low : ℕ) (hl : low ≤ h) (y : X) (hy : w.Blank (width base k low) y)
    (he : w.block (width base k low) y = w.block (width base k low) x) :
    ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask low) y d ((h-low)*(D+1)) := by
  classical
  induction hl using Nat.decreasingInduction generalizing y with
  | self =>
    have hb := w.blank_mono (dvd_mul_left (k+2) (base^h)) hy
    exact ⟨fun _ => 0,fun _ => .done (.inl hb) (w.boundary hy)⟩
  | of_succ low hl ih =>
    let i : Fin h := ⟨low,hl⟩
    obtain ⟨j,hj,path⟩ := (seq i).path y hy (tuple i)
    have he' : w.block (width base k (low+1)) y = w.block (width base k (low+1)) x := by
      rw [width_next,parent,parent,he]
    obtain ⟨b,hb⟩ := distinguish key x i j (fun h => hj (h.trans he.symm))
    rw [← width_next] at path
    obtain ⟨z,hz,hs,hw⟩ := path.endpoint
    let rest := (h-(low+1))*(D+1)
    have more : ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask (low+1)) z d rest ∨ ¬w.live z := by
      rcases hs with hs | hs
      · exact ⟨fun _ => 0,fun _ => .inr hs⟩
      · obtain ⟨mask,hm⟩ := ih z hs (hz.1.trans he')
        exact ⟨mask,fun d => .inl (hm d)⟩
    obtain ⟨mask,hm⟩ := more
    let updated := Function.update mask i b
    let good := seq.Excludes key x tuple updated low
    have here : ∀ u, w.block (width base k (low+1)) u = w.block (width base k (low+1)) y ∧
        (tuple i ∈ (seq i).sets u → w.block (width base k low) u = j) → good u := by
      rintro u ⟨hp,hm⟩
      refine .inr ⟨i,le_rfl,?_⟩
      by_cases hu : tuple i ∈ (seq i).sets u
      · exact .inr (by simpa [updated] using hb u (hp.trans he') (hm hu))
      · exact .inl hu
    have later : ∀ u, seq.Excludes key x tuple mask (low+1) u → good u := by
      rintro u (hb | ⟨a,ha,hm⟩)
      · exact .inl hb
      · have hn : a ≠ i := by intro he; subst a; change low+1 ≤ low at ha; omega
        exact .inr ⟨a,by omega,by simpa [updated,hn] using hm⟩
    have endpath : ∀ u, u = z → ∀ d, w.Escape good u d rest := by
      rintro _ rfl d
      rcases hm d with ht | ht
      · exact ht.mono later (fun _ h => h)
      · exact .done (here _ hz) ht
    refine ⟨updated,fun d => ?_⟩
    have walk := (((hw.mono here (fun _ h => h)).redirect d).append endpath)
    apply walk.more
    unfold rest
    rw [show h-low = 1+(h-(low+1)) by omega,add_mul,one_mul]

theorem escape : ∃ mask, ∀ d, w.Escape
    (fun y => w.site y = w.site x ∨ seq.Excludes key x tuple mask 0 y) x d (h*(D+1)+1) := by
  obtain ⟨y,hy,hs,hw⟩ := (w.spine (k+2) false x).endpoint
  have more : ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask 0) y d (h*(D+1)) ∨ ¬w.live y := by
    rcases hs with hs | hs
    · exact ⟨fun _ => 0,fun _ => .inr hs⟩
    · obtain ⟨mask,hm⟩ := seq.from_blank key x tuple 0 (by omega) y (by simpa [width] using hs)
        (by simpa [width] using hy)
      exact ⟨mask,fun d => .inl (hm d)⟩
  obtain ⟨mask,hm⟩ := more
  let good := fun y => w.site y = w.site x ∨ seq.Excludes key x tuple mask 0 y
  have start : w.Walk good (· = y) x false 0 :=
    hw.mono (fun _ hh => .inl (Fin.ext hh)) (fun _ hh => hh)
  have finish : ∀ u, u = y → ∀ d, w.Escape good u d (h*(D+1)) := by
    rintro _ rfl d
    rcases hm d with ht | ht
    · exact ht.mono (fun _ hh => .inr hh) (fun _ hh => hh)
    · exact .done (.inl (Fin.ext hy)) ht
  exact ⟨mask,fun d => ((start.append finish).redirect d).more (by omega)⟩

end Hierarchy
end OAI.Geometry.Hirsch.Layer.World
