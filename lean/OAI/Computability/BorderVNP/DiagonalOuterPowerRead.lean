import OAI.Computability.BorderVNP.DiagonalTrackedReplayRead
import OAI.Computability.BorderVNP.DiagonalTrackedSubdivisionRead
import OAI.Computability.BorderVNP.DiagonalOuterPowerHosts

/-! # Pointwise original power bits on the complete enriched outer history

The pullback follows the actual retained site in every selected histogram and
subdivision. Starting with arbitrary final endpoint words, the result specifies
the original leaf, private assignment, parameter and exponent bit read there.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedOuterReplay

open Crossing Shortening Adaptive Packing Cover Epoch Epoch.Round PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter PublicCapacity Diagonal.ExternalSew
open private move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
universe u

variable {D m start T exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E]
    [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start}
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- The nested team digits selecting the child cable words at an outer level. -/
noncomputable local instance outerReadPowerTeams {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

section Step
variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (M : EnrichedOuter.Epoch.{u} deep ht good V w) (c : Fin (fan S) → Admissible good t)
    (tags : ∀ i, Tracked (Port (fan S) Team t) Param Gadget exp (c i).val.pack.layout)

/-- Pull the words supplied to a final epoch owner back to its chosen child site. -/
noncomputable def emitPowerInput (q : (M.choice c).Index) (w : PowerSlot (Port (fan S) Team (t+1)) Param exp)
    (x : PowerInput ((M.choice c).term q).val.pack.layout) : PowerInput (c w.1.1).val.pack.layout := by
  let : Fintype (Port (fan S) P t) := portFintype
  let run := M.run c
  let ts := fun i => EnrichedSiteReplay.installed run i (tags i)
  let old := DenseReplay.flatPowerInput M.F y hy pos (EnrichedSiteReplay.storage M.saveNames) run.flat ts q w x
  exact EnrichedSiteReplay.installedPowerInput run w.1.1 ((tags w.1.1).words.site (w.1.2,w.2)) old

theorem emit_power_read (q : (M.choice c).Index) (w : PowerSlot (Port (fan S) Team (t+1)) Param exp)
    (x : PowerInput ((M.choice c).term q).val.pack.layout) :
    (emit M y hy pos c tags q).powerRead w x =
      (tags w.1.1).powerRead (w.1.2,w.2) (emitPowerInput y hy pos M c tags q w x) := by
  let : Fintype (Port (fan S) P t) := portFintype
  let run := M.run c
  let ts := fun i => EnrichedSiteReplay.installed run i (tags i)
  exact (DenseReplay.flat_power_read M.F y hy pos (EnrichedSiteReplay.storage M.saveNames) run.flat ts q w x).trans
    (EnrichedSiteReplay.installed_power_read run w.1.1 (tags w.1.1) (w.1.2,w.2) _)

end Step

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {width : ℕ → ℕ → ℕ}
    (M : EnrichedOuter.Machine.{0,u} deep good V width)

/-- The same owner-word pullback on the branch index of the actual outer program. -/
noncomputable def advancePowerInput (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (tags : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (w : PowerSlot (Port (fan S) Team (n+1)) Param exp) :
    (q : (M.epoch n c).Index) → PowerInput ((M.epoch n c).term q).val.pack.layout → PowerInput (c w.1.1).val.pack.layout :=
  move (V := fun a => PowerInput a.val.pack.layout → PowerInput (c w.1.1).val.pack.layout)
    (dite_eq_left hn : M.epoch n c = _).symm (fun j => emitPowerInput y hy pos (M n hn) c tags j w)

theorem advance_power_read (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (tags : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (w : PowerSlot (Port (fan S) Team (n+1)) Param exp) (q : (M.epoch n c).Index)
    (x : PowerInput ((M.epoch n c).term q).val.pack.layout) :
    (advance M y hy pos n c tags q).powerRead w x =
      (tags w.1.1).powerRead (w.1.2,w.2) (advancePowerInput y hy pos M n hn c tags w q x) := by
  let state := fun a : Admissible good (n+1) => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout
  let env := fun a : Admissible good (n+1) => PowerInput a.val.pack.layout → PowerInput (c w.1.1).val.pack.layout
  have carry {z z' : ProfileSum (Admissible good (n+1))} (he : z=z') (f : ∀ j, state (z'.term j))
      (g : ∀ j, env (z'.term j)) (hf : ∀ j x', (f j).powerRead w x' = (tags w.1.1).powerRead (w.1.2,w.2) (g j x')) :
      ∀ j x', (move (V := state) he.symm f j).powerRead w x' =
        (tags w.1.1).powerRead (w.1.2,w.2) (move (V := env) he.symm g j x') := by
    subst z'
    exact hf
  unfold advance
  rw [dite_eq_left hn]
  exact carry (dite_eq_left hn) (emit (M n hn) y hy pos c tags) (fun j => emitPowerInput y hy pos (M n hn) c tags j w)
    (fun j => emit_power_read y hy pos (M n hn) c tags j w) q x

variable {Hidden : Type} (bottom : Admissible good 0) (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

private abbrev layout (n : ℕ) (c : Admissible good n) := c.val.pack.layout

/-- Reassemble the original input words for the chosen site through all the actual
outer histograms, taking exactly its child at every branch. -/
noncomputable def historyPowerInput : (n : ℕ) → n ≤ T → (z : Fin ((fan S)^n) → Hidden) →
    (q : (packHistory bottom M.epoch n).Index) → PowerSlot (Port (fan S) Team n) Param exp →
      PowerInput ((packHistory bottom M.epoch n).term q).val.pack.layout → PowerInput bottom.val.pack.layout
  | 0, _, _, _, _, x => x
  | n+1, hn, z, q, w, x =>
    let h := Nat.lt_of_succ_le hn
    let H := packHistory bottom M.epoch n
    let c := fun j : Fin (fan S) => H.term (q.1 j)
    let sub := fun j : Fin (fan S) => fun i => z (copyIndex (fan S) n (j,i))
    let tag := fun j => Outer.term (layout (good := good)) bottom M.epoch base (advance M y hy pos) n (sub j) (q.1 j)
    historyPowerInput n h.le (sub w.1.1) (q.1 w.1.1) (w.1.2,w.2) (advancePowerInput y hy pos M n h c tag w q.2 x)

/-- The terminal tracked read is the true original bit at the designated leaf and
inside batch, on the explicitly reassembled physical words for that retained site. -/
theorem terminal_power_read (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden)
    (w : PowerSlot (Port (fan S) Team T) Param exp) (x : PowerInput ((packHistory bottom M.epoch T).term q).val.pack.layout) :
    let idx := portEquiv (fan S) Team T w.1
    (terminal M y hy pos bottom base q z).powerRead w x =
      (base (z idx.1)).powerRead (idx.2,w.2) (historyPowerInput y hy pos M bottom base T le_rfl z q w x) := by
  have nested (n : ℕ) (hn : n≤T) (q' : (packHistory bottom M.epoch n).Index) (z' : Fin ((fan S)^n) → Hidden)
      (w' : PowerSlot (Port (fan S) Team n) Param exp) (x' : PowerInput ((packHistory bottom M.epoch n).term q').val.pack.layout) :
      let idx := portEquiv (fan S) Team n w'.1
      (Outer.term (layout (good := good)) bottom M.epoch base (advance M y hy pos) n z' q').powerRead w' x' =
        (base (z' idx.1)).powerRead (idx.2,w'.2) (historyPowerInput y hy pos M bottom base n hn z' q' w' x') := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let h := Nat.lt_of_succ_le hn
      let H := packHistory bottom M.epoch n
      let c := fun j : Fin (fan S) => H.term (q'.1 j)
      let sub := fun j : Fin (fan S) => fun i => z' (copyIndex (fan S) n (j,i))
      let tag := fun j => Outer.term (layout (good := good)) bottom M.epoch base (advance M y hy pos) n (sub j) (q'.1 j)
      exact (advance_power_read y hy pos M n h c tag w' q'.2 x').trans
        (ih h.le (q'.1 w'.1.1) (sub w'.1.1) (w'.1.2,w'.2) _)
  exact nested T le_rfl q z w x

end Diagonal.CellEntries.EnrichedOuterReplay

end BorderVNP
end Computability
end OAI
