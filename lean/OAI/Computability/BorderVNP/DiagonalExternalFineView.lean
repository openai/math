import OAI.Computability.BorderVNP.DiagonalTaggedStep

/-! # Reading the real public bits of a stored grouped network

Each real public bit names one lane of an attached word. The local table reads
that bit at the word's host and assigns false to every unnamed lane. All internal
cable assignments and all unary power owners remain at their original sites.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FineView

open Crossing CellEntries
open scoped Classical BigOperators

variable {D : ℕ} {A P : Type} {width : A → ℕ} (N : Network D A width)
    (lane : P ↪ Σ a, Fin (width a))

/-- Give each real lane a width-one port at the host of the containing word. -/
def layout : Network D P (fun _ => 1) where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width := N.width
  attach p := N.attach (lane p).1
  position := N.position
  in_ball := N.in_ball

/-- Read a real bit with evidence of its location, clamping an unused lane to zero. -/
private noncomputable def fill (s : Σ a, Fin (width a))
    (get : ∀ p : P, lane p = s → Bool) : Bool :=
  if h : ∃ p, lane p = s then get h.choose h.choose_spec else false

/-- Extend a fine input to all grouped words using the specified zero padding. -/
noncomputable def extend (x : Ports (fun _ : P => 1)) : Ports width :=
  fun a i => fill lane ⟨a,i⟩ (fun p _ => x p 0)

/-- Every real lane reads precisely the width-one bit assigned to its named port. -/
theorem extend_lane (x : Ports (fun _ : P => 1)) (p : P) :
    extend lane x (lane p).1 (lane p).2 = x p 0 := by
  have h : ∃ q, lane q = lane p := ⟨p,rfl⟩
  unfold extend fill
  rw [dite_eq_left h]
  exact congrArg (fun q => x q 0) (lane.injective h.choose_spec)

/-- A lane outside the embedding is clamped to the fixed padding bit. -/
theorem extend_unused (x : Ports (fun _ : P => 1)) (a : A) (i : Fin (width a))
    (h : ¬ ∃ p, lane p = ⟨a,i⟩) : extend lane x a i = false := by
  simp only [extend,fill,dite_eq_right h]

/-- Each old grouped table reads only the real slots owned by its host and the
fixed false values of the unnamed lanes of its words. -/
noncomputable def tables {K : Type*} (T : N.Tables K) : (layout N lane).Tables K :=
  fun v z x => T v z fun a i => fill lane ⟨a.val,i⟩ fun p hp =>
    x ⟨p,(congrArg (fun s : Σ a, Fin (width a) => N.attach s.1) hp).trans a.property⟩ 0

/-- Pointwise agreement for any internal cable assignment and every real input. -/
theorem read {K : Type*} (T : N.Tables K) (a : N.Assignment)
    (x : Ports (fun _ : P => 1)) (v : N.Site) :
    (layout N lane).read (tables N lane T) a x v = N.read T a (extend lane x) v := rfl

/-- The resulting tensor equals the grouped tensor at the actual zero extension. -/
theorem value {K : Type*} [CommSemiring K] (T : N.Tables K) (x : Ports (fun _ : P => 1)) :
    (layout N lane).value (tables N lane T) x = N.value T (extend lane x) := rfl

variable {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}

/-- Every original unary power occurrence reads its local use bit through the
same port restriction as the interpreted entry at its owner. -/
noncomputable def words {tags : N.Tables (Entry Param Gadget)}
    (w : PowerWords Team Param Gadget b N tags) :
    PowerWords Team Param Gadget b (layout N lane) (tables N lane tags) where
  site := w.site
  selected := tables N lane w.selected
  located v _ _ i h := w.located v _ _ i h
  exact v _ _ := w.exact v _ _

/-- The fine-slot presentation of a stored tagged network and all its power words. -/
noncomputable def tracked (t : Tracked Team Param Gadget b N) :
    Tracked Team Param Gadget b (layout N lane) :=
  ⟨tables N lane t.tags, words N lane t.words⟩

/-- The polynomial tensor agrees for all gadget interpretations and arbitrary
literal, pin and exterior settings of the fine inputs. -/
theorem tracked_tensor {K : Type*} [CommSemiring K] (t : Tracked Team Param Gadget b N)
    (values : Gadget → K) (x : Ports (fun _ : P => 1)) :
    ((tracked N lane t).valued values).tensor x =
      (t.valued values).tensor (extend lane x) := rfl

end Diagonal.ExternalSew.FineView

end BorderVNP
end Computability
end OAI
