import OAI.Computability.IntegerMultiplication.Loom.Tracks

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims
variable {X J : Type} [DecidableEq J] {n : ℕ} (x : Series X) (f : J ≃ Fin n)
def fromOrder (X : Type) : (Fin n → X) ≃ (J→X) where
  toFun w := w ∘ f
  invFun w := w ∘ f.symm
  left_inv w := by ext; simp
  right_inv w := by ext; simp
omit [DecidableEq J] in
@[simp] theorem use_f (w : J→X) (q : Fin n) :
    (fromOrder f X).symm w q=w (f.symm q) := rfl

abbrev threads := (Track x n).via (fromOrder f X)
abbrev pullback : Adopt (threads x f) (Track x n) := (Adopt.turn _ _).back

def undye {d} (e : Seal x d) : Seal (threads x f) (Rack d n) :=
  (pullback x f).thenDo (park x d e n)

private theorem replaced {w : J→X} (i : J) (a : X) :
    (pullback x f).cast (Function.update w i a) =
    Function.update ((pullback x f).cast w) (f i) a := by
  ext j
  obtain ⟨j,rfl⟩ := f.surjective j
  change Function.update w i a _ = _
  have hz (w : J→X) : (pullback x f).cast w = (fromOrder f X).symm w := rfl
  by_cases e : j=i
  · simp [hz,e]
  have y : f j≠f i := fun h => e (f.injective h)
  -- goal ?m after change?
  simp [hz,y,e]

theorem monoRay {d : Tape} (e : Seal x d) (i : J) :
    ∃ (q : Slot (threads x f) (Rack d (f i).val) x (Rack d (n-(f i).val-1))),
      ∀ z v,q.read z=z i ∧ q.alter z v=Function.update z i v := by
  let s := pick x d e (f i)
  have hi := s.pos; have hs := s.size
  have hu : s.after = n-(f i).val-1 := by omega
  rw [← hu,← hi]
  refine ⟨s.shape.arrive (pullback x f),fun w v => ⟨?_,?_⟩⟩
  · rw [Slot.pull,s.who]
    change (fromOrder f X).symm w _=_
    simp
  · apply (pullback x f).cast.injective; rw [Slot.endorse,s.put,replaced]

theorem doubleRay {d : Tape} (e : Seal x d) (i j : J) (h : (f i)<f j) :
    ∃ (q : Axis (threads x f) (Rack d (f i).val) x (Rack d ((f j).val-(f i).val-1))
      x (Rack d (n-(f j).val-1))), ∀ z v,q.pair z=(z i,z j) ∧
      q.bridge z v=Function.update (Function.update z i v.1) j v.2 := by
  let s := pickTwo x d e (f i) (f j) h
  have hi := s.pos; have ht := s.through; have hs := s.size
  have hg : s.middle=(f j).val-(f i).val-1 := by omega
  have hu : s.after = n-(f j).val-1 := by omega
  rw [← hg,← hu,← hi]
  refine ⟨s.shape.arrive (pullback x f),fun w v => ⟨?_,?_⟩⟩
  · rw [Axis.pull,s.who]
    change ((fromOrder f X).symm w _,(fromOrder f X).symm w _)=_
    simp
  · apply (pullback x f).cast.injective; rw [Axis.endorse,s.put,replaced,replaced]
end Loom

end IntegerMultiplication
end Computability
end OAI
