import OAI.Geometry.Hirsch.PathSlack

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {X A : Type} {L k V D : ℕ}

namespace World

variable (w : World X (L*(k+2)))

def site (x : X) : Fin L :=
  ⟨w.layer x / (k+2),(Nat.div_lt_iff_lt_mul (by omega)).mpr (w.bound x)⟩

theorem site_micro {x : X} {s : Fin L} {j : Fin k} (hx : w.layer x = micro s j) : w.site x = s := by
  apply Fin.ext
  simp only [site,hx,micro,add_assoc]
  rw [mul_comm s.val, Nat.mul_add_div (by omega : 0 < k+2),Nat.div_eq_of_lt (by omega),add_zero]

def Away (t : Fin L) (d : Bool) (x : X) := if d then t < w.site x else w.site x < t

theorem away_ne {t d x} (ha : w.Away t d x) : t ≠ w.site x := by
  cases d
  · exact ne_of_gt ha
  · exact ne_of_lt ha

theorem away_step {t d x} (ha : w.Away t d x) (hl : w.live x) : w.Away t d (w.step x d) := by
  cases d
  · have hh : w.site (w.step x false) ≤ w.site x :=
      Nat.div_le_div_right (by have := w.west x hl; omega)
    exact lt_of_le_of_lt hh ha
  · have hh : w.site x ≤ w.site (w.step x true) :=
      Nat.div_le_div_right (by have := w.east x hl; omega)
    exact lt_of_lt_of_le ha hh

structure Emissions (A : Type) (D : ℕ) where
  emit : X → Option A
  micro : ∀ (s : Fin L) (j : Fin k) x, w.layer x = Layer.micro s j → ∃ i, emit x = some i
  escape : ∀ x i, emit x = some i → ∀ d, w.Escape (fun y => emit y = some i → w.site y = w.site x) x d D

end World

namespace Bundles

variable (code : Bundles L V)

structure Separates : Prop where
  index : ∀ s t i j a b, code.label s i a = code.label t j b → i = j
  separates : ∀ e : code.Contest, ∀ s, e.1 ≠ s →
    ∃ l, code.member e l ∧ ∀ a, code.label s e.2.1 a ≠ l

def avoids {w : World X (L*(k+2))} (p : w.Emissions code.idx D) (l : Fin V) (x : X) :=
  ∀ i, p.emit x = some i → ∀ a, code.label (w.site x) i a ≠ l

variable {code} {w : World X (L*(k+2))} (sep : code.Separates) (p : w.Emissions code.idx D)

include sep in
theorem avoids_other {e : code.Contest} {l : Fin V} (hl : code.member e l)
    {x : X} (hn : p.emit x ≠ some e.2.1) : code.avoids p l x := by
  obtain ⟨a,_,ha⟩ := hl
  intro j hj b hb
  have he := sep.index _ _ _ _ _ _ (hb.trans ha.symm)
  exact hn (he ▸ hj)

include sep in
theorem avoids_escape (e : code.Contest) (d : Bool) :
    ∀ x, w.Away e.1 d x → ∃ l, code.member e l ∧ w.Escape (code.avoids p l) x d D := by
  apply w.induct
  intro x ih hx
  by_cases he : p.emit x = some e.2.1
  · obtain ⟨l,hl,ha⟩ := sep.separates e _ (w.away_ne hx)
    refine ⟨l,hl,(p.escape x _ he d).mono ?_ (fun _ h => h)⟩
    intro y hy
    by_cases hh : p.emit y = some e.2.1
    · intro j hj a
      rw [Option.some.inj (hj.symm.trans hh),hy hh]
      exact ha a
    · exact avoids_other sep p hl hh
  · by_cases hv : w.live x
    · obtain ⟨l,hl,hh⟩ := ih hv d (w.away_step hx hv)
      exact ⟨l,hl,.go (avoids_other sep p hl he) hv (by simp [World.turn]) hh⟩
    · obtain ⟨l,hl,_⟩ := sep.separates e _ (w.away_ne hx)
      exact ⟨l,hl,.done (avoids_other sep p hl he) hv⟩

include sep p in
theorem sequence (hw : w.Full) : Nonempty (StateSequence code ((2*(D+1)+1)^V) k (1/4)) := by
  apply World.sequence D (code.avoids p) w hw
  intro s j x hx
  obtain ⟨i,hi⟩ := p.micro s j x hx
  have he := w.site_micro hx
  refine ⟨⟨i,fun a => w.slack_zero D _ (fun hh => hh i hi a (by rw [he]))⟩,fun e hn => ?_⟩
  obtain ⟨d,hd⟩ : ∃ d, w.Away e.1 d x := by
    rw [← he] at hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · exact ⟨true,hh⟩
    · exact ⟨false,hh⟩
  obtain ⟨l,hl,hh⟩ := avoids_escape sep p e d x hd
  exact ⟨l,hl,(w.slack_pos D _ hh).ne'⟩

end Bundles
end OAI.Geometry.Hirsch.Layer
