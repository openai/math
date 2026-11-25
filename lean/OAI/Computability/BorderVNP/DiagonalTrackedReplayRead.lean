import OAI.Computability.BorderVNP.DiagonalTrackedPowerRead

/-! # Reading a power slot of the original leaf through a complete normalized epoch

An arbitrary terminal assignment is pulled back along the selected history, using
the cable words at the chosen slot's actual owner. The same row-major leaf number
selects the input tag and the original team at every depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseReplay

open Crossing Shortening Shortening.Adaptive Packing PackedHistoryCircuit.Normalized Diagonal.ExternalSew
open scoped Classical
set_option maxHeartbeats 1800000

variable {k steps exp D m : ℕ} [NeZero D] {I P Team Param Gadget K E : Type}
    [Fintype I] [Fintype Team] [Fintype Param] [Field K] [Field E]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin steps → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : PackedHistoryCircuit.Normalized.Program (B := B) e view) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget) (save : Saved F)

/-- The nested team positions are the row-major batch digits. -/
local instance replayPowerTeams {n : ℕ} : Fintype (Port k Team n) := Replay.batchFinite k Team n

private noncomputable abbrev replayNet := fun n (z : A n) => (view n z).pack.layout

/-- Read the original leaf's incident words using the actual selected histograms,
stable cable renumberings and chosen branch at each depth. -/
noncomputable def replayPowerInput :
    (n : ℕ) → (hn : n ≤ steps) → (a : Fin (k^n) → A 0) →
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout) →
    (q : (F.system.histories n hn (leavesEquiv k _ n a)).Index) →
    (w : PowerSlot (Port k Team n) Param exp) →
    PowerInput (replayNet (view := view) n ((F.system.layer n).state
      ((F.system.histories n hn (leavesEquiv k _ n a)).term q))) →
      PowerInput (view 0 (a (portEquiv k Team n w.1).1)).pack.layout
  | 0, _, _, _, _, _, x => x
  | n+1, hn, a, t, q, w, x => by
    let h := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,h⟩
    let sub := fun (j : Fin k) (z : Fin (k^n)) => a (copyIndex k n (j,z))
    let lower := fun (j : Fin k) (z : Fin (k^n)) => t (copyIndex k n (j,z))
    let H := fun j : Fin k => F.system.histories n h.le (leavesEquiv k _ n (sub j))
    let c := fun j : Fin k => (F.system.layer n).state ((H j).term (q.1 j))
    let tag := fun j : Fin k => Replay.publicReplay F.system (replayNet (view := view)) (move F y hy pos save)
      n h.le (leavesEquiv k _ n (sub j)) (Replay.flatInputs (replayNet (view := view) 0) n (sub j) (lower j)) (q.1 j)
    let child := w.1.1
    let v := (tag child).words.site (w.1.2,w.2)
    let restored := (save i c q.2).powerInput x
    exact replayPowerInput n h.le (sub child) (lower child) (q.1 child) (w.1.2,w.2)
      (childPowerInput (F.stage i c) e q.2 ⟨child,v⟩ restored)

/-- Each publicly selected stored summand reads the same bit as its original
leaf on its reconstructed input, including when the bit is zero. -/
theorem replay_power_read (n : ℕ) (hn : n ≤ steps) (a : Fin (k^n) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout)
    (q : (F.system.histories n hn (leavesEquiv k _ n a)).Index) (w : PowerSlot (Port k Team n) Param exp)
    (x : PowerInput (replayNet (view := view) n ((F.system.layer n).state
      ((F.system.histories n hn (leavesEquiv k _ n a)).term q)))) :
    let leaf := portEquiv k Team n w.1
    (Replay.publicReplay F.system (replayNet (view := view)) (move F y hy pos save) n hn (leavesEquiv k _ n a)
      (Replay.flatInputs (replayNet (view := view) 0) n a t) q).powerRead w x =
      (t leaf.1).powerRead (leaf.2,w.2) (replayPowerInput F y hy pos save n hn a t q w x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let i : Fin steps := ⟨n,h⟩
    let sub := fun (j : Fin k) (z : Fin (k^n)) => a (copyIndex k n (j,z))
    let lower := fun (j : Fin k) (z : Fin (k^n)) => t (copyIndex k n (j,z))
    let H := fun j : Fin k => F.system.histories n h.le (leavesEquiv k _ n (sub j))
    let c := fun j : Fin k => (F.system.layer n).state ((H j).term (q.1 j))
    let tag := fun j : Fin k => Replay.publicReplay F.system (replayNet (view := view)) (move F y hy pos save)
      n h.le (leavesEquiv k _ n (sub j)) (Replay.flatInputs (replayNet (view := view) 0) n (sub j) (lower j)) (q.1 j)
    let child := w.1.1
    let v := (tag child).words.site (w.1.2,w.2)
    let restored := (save i c q.2).powerInput x
    let old := childPowerInput (F.stage i c) e q.2 ⟨child,v⟩ restored
    exact ((save i c q.2).powerRead (stageOutput (F.stage i c) tag e y hy pos q.2) w x).trans
      ((stage_power_read (F.stage i c) tag e y hy pos q.2 w restored).trans
        (ih h.le (sub child) (lower child) (q.1 child) (w.1.2,w.2) old))

/-- Reassemble the source words of a particular flattened batch/parameter/bit.
Only the external ports change when passing back to the nested terminal. -/
noncomputable def flatPowerInput (a : Fin (k^steps) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout)
    (q : F.Hist a) (w : PowerSlot (Fin (k^steps) × Team) Param exp)
    (x : PowerInput (Replay.flatLayout steps (replayNet (view := view) steps ((F.system.layer steps).state
      ((F.system.histories steps le_rfl (leavesEquiv k _ steps a)).term q))))) : PowerInput (view 0 (a w.1.1)).pack.layout :=
  let index := portEquiv k Team steps
  let z := replayPowerInput F y hy pos save steps le_rfl a t q (index.symm w.1,w.2)
    ⟨x.edges,nestedPorts bits k steps x.ports⟩
  Eq.mp (congrArg (fun j : Fin (k^steps) × Team => PowerInput (view 0 (a j.1)).pack.layout) (index.apply_symm_apply w.1)) z

/-- The public flattened epoch reads precisely the original input bit on the
actual words pulled back from its incident cables and exterior ports. -/
theorem flat_power_read (a : Fin (k^steps) → A 0)
    (t : ∀ j, Tracked Team Param Gadget exp (view 0 (a j)).pack.layout)
    (q : F.Hist a) (w : PowerSlot (Fin (k^steps) × Team) Param exp)
    (x : PowerInput (Replay.flatLayout steps (replayNet (view := view) steps ((F.system.layer steps).state
      ((F.system.histories steps le_rfl (leavesEquiv k _ steps a)).term q))))) :
    (Replay.publicFlat F.system (replayNet (view := view)) (move F y hy pos save) steps le_rfl a t q).powerRead w x =
      (t w.1.1).powerRead (w.1.2,w.2) (flatPowerInput F y hy pos save a t q w x) := by
  let idx := portEquiv k Team steps
  let old := (idx.symm w.1,w.2)
  let input : PowerInput (replayNet (view := view) steps ((F.system.layer steps).state
      ((F.system.histories steps le_rfl (leavesEquiv k _ steps a)).term q))) := ⟨x.edges,nestedPorts bits k steps x.ports⟩
  have castRead (j j' : Fin (k^steps) × Team) (h : j = j') (z : PowerInput (view 0 (a j.1)).pack.layout) :
      (t j.1).powerRead (j.2,w.2) z =
      (t j'.1).powerRead (j'.2,w.2) (Eq.mp (congrArg (fun l : Fin (k^steps) × Team => PowerInput (view 0 (a l.1)).pack.layout) h) z) := by
    subst j'
    rfl
  exact (replay_power_read F y hy pos save steps le_rfl a t q old input).trans
    (castRead _ w.1 (idx.apply_symm_apply w.1) _)

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
