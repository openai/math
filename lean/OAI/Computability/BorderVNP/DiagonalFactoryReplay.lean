import OAI.Computability.BorderVNP.DiagonalOuterReplay
import OAI.Computability.BorderVNP.PackedSiteEpochs

/-! # Tagged replay on an arbitrary physical factory's own output indices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.FactoryReplay

open Crossing Shortening Adaptive Packing Packing.PhysicalEpochs
open scoped BigOperators Classical

variable {D exp : ℕ} {K E Team Param Gadget P Hidden : Type}
    [Field K] [Field E] [Fintype Team] [Fintype Param] [Fintype P]
    {bits : P → ℕ} (F : Factory D K) {T start : ℕ} (deep : F.floor+1+F.drop*T ≤ start)

/-- Row-major enumeration of the original batches after these packing stages. -/
noncomputable local instance {n : ℕ} : Fintype (Port F.fan Team n) := Replay.batchFinite F.fan Team n

/-- Tagged output on the very same index returned by the geometric factory. -/
abbrev Emit := ∀ (t : ℕ) (ht : t < T) (child : Fin F.fan → F.State bits start t)
  (_tagged : ∀ i, Tracked (Port F.fan Team t) Param Gadget exp (child i).pack.layout)
  (j : Fin (F.output deep ht child).terms), Tracked (Port F.fan Team (t+1)) Param Gadget exp
    ((F.output deep ht child).pack j).layout

variable (emit : Emit (Team := Team) (Param := Param) (Gadget := Gadget) (exp := exp) (bits := bits) F deep)

private def move {A : Type*} {V : A → Type*} {p q : ProfileSum A} (h : p = q)
    (terms : ∀ j : p.Index, V (p.term j)) : ∀ j : q.Index, V (q.term j) := h ▸ terms

private theorem sum_move {A R : Type*} [AddCommMonoid R] {V : A → Type*} {p q : ProfileSum A}
    (h : p = q) (terms : ∀ j : p.Index, V (p.term j)) (eval : ∀ a, V a → R) :
    (∑ j, eval (q.term j) (move h terms j)) = ∑ j, eval (p.term j) (terms j) := by cases h; rfl

/-- Insert the tagged arithmetic terms at the corresponding factory node.
There are no public histories beyond the chosen terminal level. -/
noncomputable def advance : Outer.Advance (Team := Team) (Param := Param) (Gadget := Gadget) (b := exp)
    (fun _ (p : F.State bits start _) => p.pack.layout) (F.epoch deep) := by
  intro t child tagged
  let V := fun p : F.State bits start (t+1) => Tracked (Port F.fan Team (t+1)) Param Gadget exp p.pack.layout
  by_cases ht : t < T
  · exact move (V := V) (dite_eq_left ht : F.epoch deep t child = _).symm (emit t ht child tagged)
  · exact move (V := V) (dite_eq_right ht : F.epoch deep t child = _).symm (fun j : Empty => j.elim)

variable (values : Gadget → E)
    (correct : ∀ t ht child tagged x,
      (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((emit t ht child tagged j).valued values).tensor x)

include correct in
private theorem advance_sum (t : ℕ) (ht : t < T) (child : Fin F.fan → F.State bits start t)
    (tagged : ∀ i, Tracked (Port F.fan Team t) Param Gadget exp (child i).pack.layout)
    (x : Ports (width bits F.fan (t+1))) :
    (∏ i, ((tagged i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((advance F deep emit t child tagged q).valued values).tensor x := by
  let V := fun p : F.State bits start (t+1) => Tracked (Port F.fan Team (t+1)) Param Gadget exp p.pack.layout
  let v := fun p (w : V p) => (w.valued values).tensor x
  refine (correct t ht child tagged x).trans ?_
  unfold advance
  rw [dite_eq_left ht]
  exact (sum_move (V := V) (dite_eq_left ht : F.epoch deep t child = _).symm (emit t ht child tagged) v).symm

variable [Fintype Hidden] (bottom : F.State bits start 0) (base : Hidden → Tracked Team Param Gadget exp bottom.pack.layout)

/-- The terminal tagged term before flattening, with its own private bottom assignments. -/
noncomputable def terminal (q : (F.histories deep bottom T).Index) (z : Fin (F.fan^T) → Hidden) :
    Tracked (Port F.fan Team T) Param Gadget exp ((F.histories deep bottom T).term q).pack.layout :=
  Outer.term (fun _ (p : F.State bits start _) => p.pack.layout) bottom (F.epoch deep) base
    (advance F deep emit) T z q

include correct in
/-- On the very histories and public layouts of the factory, with any actual
proved local arithmetic replay, independent private input choices can be
summed after the public histogram. -/
theorem terminal_sum (x : Ports (fun q : Fin (F.fan^T) × P => bits q.2)) :
    (∏ i, ∑ z : Hidden, ((base z).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ∑ z, ((terminal F deep emit bottom base q z).flat.valued values).tensor x :=
  Outer.sum_private_and_public (fun _ (p : F.State bits start _) => p.pack.layout)
    bottom (F.epoch deep) base (advance F deep emit) values T
    (advance_sum F deep emit values correct) T le_rfl x

end Diagonal.CellEntries.FactoryReplay

end BorderVNP
end Computability
end OAI
