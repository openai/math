import OAI.Computability.BorderVNP.PackedInheritedRoundValue

/-! # Exact fibers of inherited sparse observations

The interval rows stage the prior incident words uniquely for each old private
guess. This gives a bijection of accepting guesses for every fixed list of
observed entries, without specializing any scalar in the field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep
open scoped Classical

/-- The private guesses at a fixed site input that produce the specified complete
sequence of observed signs and gadget identifiers. -/
abbrev Site.Fiber (s : Site) (input : Fin s.incoming → Bool) (obs : List (Bool × Option ℕ)) :=
  {g : Fin s.work → Bool // s.observe (bits g input) = some obs}

variable (s : Site) (loc : s.Local) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read) (input : Fin n → Bool) (obs : List (Bool × Option ℕ))

/-- Append the forced former cable and port words to each old successful guess. -/
def extendFiber (s : Site) (loc : s.Local) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read) (input : Fin n → Bool) (obs : List (Bool × Option ℕ))
    (g : s.Fiber (input ∘ read) obs) : (s.retain n cuts).Fiber input obs :=
  ⟨Fin.append g.val (input ∘ read),by
    exact (observe_layer s loc cuts read cover g.val (input ∘ read) input).trans
      ((ite_eq_left rfl).trans g.property)⟩

/-- Retention gives a bijection on each individual observation fiber. Every valid
new guess arises by appending exactly the forced input to its unique old work prefix. -/
noncomputable def retainFiberEquiv (s : Site) (loc : s.Local) {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n)
    (cover : Covers s.incoming n cuts read) (input : Fin n → Bool) (obs : List (Bool × Option ℕ)) : s.Fiber (input ∘ read) obs ≃ (s.retain n cuts).Fiber input obs := by
  apply Equiv.ofBijective (extendFiber s loc cuts read cover input obs)
  constructor
  · intro x y he
    apply Subtype.ext
    funext i
    have h := congrArg (fun u : (s.retain n cuts).Fiber input obs => u.val (i.castAdd s.incoming)) he
    exact (Fin.append_left x.val (input ∘ read) i).symm.trans (h.trans (Fin.append_left y.val (input ∘ read) i))
  · intro u
    obtain ⟨⟨g,old⟩,h⟩ := (Fin.appendEquiv (α := Bool) s.work s.incoming).surjective u.val
    change Fin.append g old = u.val at h
    have hu := (observe_layer s loc cuts read cover g old input).symm.trans
      ((congrArg (fun w : Fin (s.work+s.incoming) → Bool => (s.retain n cuts).observe (bits w input)) h).trans u.property)
    by_cases ho : old = input ∘ read
    · subst old
      rw [ite_eq_left rfl] at hu
      exact ⟨⟨g,hu⟩,Subtype.ext h⟩
    · rw [ite_eq_right ho] at hu
      contradiction

/-- The bijection preserves every original guessed bit at its original index. -/
theorem retainFiber_prefix (g : s.Fiber (input ∘ read) obs) (i : Fin s.work) :
    (retainFiberEquiv s loc cuts read cover input obs g).val (i.castAdd s.incoming) = g.val i :=
  Fin.append_left g.val _ i

/-- Its appended suffix is the forced input, including lanes at either kind of cut hook. -/
theorem retainFiber_suffix (g : s.Fiber (input ∘ read) obs) (i : Fin s.incoming) :
    (retainFiberEquiv s loc cuts read cover input obs g).val (i.natAdd s.work) = input (read i) :=
  Fin.append_right g.val _ i

variable {D m old next np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (name : A → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (v : p.layout.Site) (oldID : p.layout.Edge ↪ Fin old)
    (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next) (portID : P ↪ Fin np)
    (hs : s.incoming = incoming p.layout v)
    (y : (output e p bin perm positive first q).layout.Assignment) (x : Ports bits)

/-- Observation fibers of the concrete sewn site are equivalent to the former site's
fibers on the physically reconstructed whole cable and port words. -/
noncomputable def retainedObservationFiber (s : Site) (hs : s.incoming = incoming p.layout v) (loc : s.Local) :
    s.Fiber (fun k => inputWords p.layout oldID portID v
      (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) (Fin.cast hs k)) obs ≃
    (retained e p bin perm name positive first q v oldID nextID portID s).Fiber
      (successorInput e p bin perm positive first q v nextID portID y x) obs := by
  let new := successorInput e p bin perm positive first q v nextID portID y x
  let projection := layerRead e p bin perm positive first q v oldID nextID portID ∘ Fin.cast hs
  have h : new ∘ projection = (fun k => inputWords p.layout oldID portID v
      (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) (Fin.cast hs k)) := by
    funext k
    exact congrFun (layerRead_inputs e p bin perm positive first q v oldID nextID portID y x) (Fin.cast hs k)
  rw [← h]
  exact retainFiberEquiv s loc _ projection ((layer_covers e p bin perm name positive first q v oldID nextID portID).castOld hs) new obs

end Packing.Inherited

end BorderVNP
end Computability
end OAI
