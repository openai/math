import OAI.Computability.BorderVNP.DiagonalSubdivisionBirthInputs
import OAI.Computability.BorderVNP.DiagonalInnerBirthInputs
import OAI.Computability.BorderVNP.DiagonalOuterPowerRead
import OAI.Computability.BorderVNP.DiagonalFlatBirthInput

/-! # Original physical birth lanes through the attained enriched outer history

At each tracked power slot, its private program and its mathematical selected
table pull the very same incidence words back through the entire replay.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Diagonal.ExternalSew Diagonal.CellEntries Diagonal.CellEntries.EnrichedOuterReplay
open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Site.Lineage PublicCapacity
open private move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2500000
set_option maxRecDepth 6000

universe u
variable {D m start T exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E]
    [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start}
    (y : e.Entry → E) (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

/-- Enumerate the tracked team labels in the same nested order as the replay. -/
noncomputable local instance {n : ℕ} : Fintype (Port (fan S) Team n) := Replay.batchFinite (fan S) Team n

namespace Epoch

variable {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {width : ℕ → ℕ}
    (M : Epoch.{u} deep ht good V width) (rows : M.F.SiteRows) {oldCap newCap : ℕ}
    (oldPort : Port (fan S) P t ↪ Fin oldCap) (nextPort : Port (fan S) P (t+1) ↪ Fin newCap)
    (fieldRows : M.FieldRows rows oldPort nextPort) (number : e.Entry → ℕ)
    (c : Fin (fan S) → Admissible good t)
    (old : ∀ j, @Site.Programs D _ (portFintype (k := fan S) (P := P) (b := t)) _ (c j).val.pack.layout)
    (tag : ∀ i, Tracked (Port (fan S) Team t) Param Gadget exp (c i).val.pack.layout)

include fieldRows in
/-- Every saved birth input lane at the selected power slot is the lane
read by the same retained child program before this epoch. -/
theorem privatePrograms_birthInput (q : (M.choice c).Index) (w : PowerSlot (Port (fan S) Team (t+1)) Param exp)
    (x : PowerInput ((M.choice c).term q).val.pack.layout) :
    let : Fintype (Port (fan S) P t) := portFintype
    let : Fintype (Port (fan S) P (t+1)) := portFintype
    let v := (emit M y hy pos c tag q).words.site w
    let v' := (tag w.1.1).words.site (w.1.2,w.2)
    birthInput ((M.choice c).term q).val.pack.layout ((M.choice c).term q).val.rows.edge nextPort
      v (M.privatePrograms rows c old number q v) x =
      birthInput (c w.1.1).val.pack.layout (c w.1.1).val.rows.edge oldPort v' (old w.1.1 v')
        (emitPowerInput y hy pos M c tag q w x) := by
  let : Fintype (Port (fan S) P t) := portFintype
  let : Fintype (Port (fan S) P (t+1)) := portFintype
  let run := M.run c
  let init := M.installedPrivatePrograms rows c old
  let input := fun i => EnrichedSiteReplay.installed run i (tag i)
  let final := ((M.choice c).term q).val.pack.layout
  let v := (emit M y hy pos c tag q).words.site w
  let v' := (tag w.1.1).words.site (w.1.2,w.2)
  let edge := fieldRows.layout.edges S.rounds (run.root q)
  let port := Flat.portRows S.rounds (rows.ports S.rounds)
  let progs := M.privatePrograms rows c old number q
  let f₁ := portFintype (k := fan S) (P := P) (b := t+1)
  let f₀ := instFintypeProd (Fin (fan S)) (Port (fan S) P t)
  let flatProgs := M.F.flatPrivatePrograms M.saveNames rows number run.flat init q
  have atFinal := birthInput_numbered final edge nextPort v (progs v) _ fieldRows.outputCap (fieldRows.outputRows c q) x
  have atPorts := birthInput_portNumbered final edge port progs nextPort fieldRows.outputPortCap fieldRows.outputPorts v x
  have changed := birthInput_instance f₀ f₁ final edge port flatProgs v x
  let before := DenseReplay.flatPowerInput M.F y hy pos (EnrichedSiteReplay.storage M.saveNames) run.flat input q w x
  have hi := M.installedPrivatePrograms_birthInput rows oldPort nextPort fieldRows c old w.1.1 v' before
  have hs := installed_power_site M c tag w.1.1 (w.1.2,w.2)
  have atInit : birthInput (M.view 0 (run.flat w.1.1)).pack.layout (fieldRows.layout.edges 0 (run.flat w.1.1)) (rows.ports 0)
      ((input w.1.1).words.site (w.1.2,w.2)) (init w.1.1 _) before =
      birthInput (c w.1.1).val.pack.layout (c w.1.1).val.rows.edge oldPort v' (old w.1.1 v')
        (EnrichedSiteReplay.installedPowerInput run w.1.1 v' before) :=
    (congrArg (fun s => birthInput (M.view 0 (run.flat w.1.1)).pack.layout (fieldRows.layout.edges 0 (run.flat w.1.1))
      (rows.ports 0) s (init w.1.1 s) before) hs).trans hi
  have pulled := M.F.flatPrivatePrograms_birthInput M.saveNames rows fieldRows.layout number y hy pos run.flat init input q w x
  exact (atFinal.trans (atPorts.trans changed)).trans (pulled.trans atInit)

end Epoch

namespace Machine

variable {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {width : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V width) (rows : ∀ n hn, (M n hn).F.SiteRows)
    {cap : ℕ → ℕ} (ports : ∀ n, Port (fan S) P n ↪ Fin (cap n))
    (fieldRows : ∀ n hn, (M n hn).FieldRows (rows n hn) (ports n) (ports (n+1)))
    (number : e.Entry → ℕ)

private abbrev geometry (n : ℕ) (a : Admissible good n) := a.val.pack.layout

include fieldRows in
/-- The physical birth input at a power slot after the actual indexed outer step. -/
theorem stepPrivatePrograms_birthInput (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, @Site.Programs D _ (portFintype (k := fan S) (P := P) (b := n)) _ (c j).val.pack.layout)
    (tag : ∀ i, Tracked (Port (fan S) Team n) Param Gadget exp (c i).val.pack.layout)
    (q : (M.epoch n c).Index) (w : PowerSlot (Port (fan S) Team (n+1)) Param exp)
    (x : PowerInput ((M.epoch n c).term q).val.pack.layout) :
    let : Fintype (Port (fan S) P n) := portFintype
    let : Fintype (Port (fan S) P (n+1)) := portFintype
    let v := (advance M y hy pos n c tag q).words.site w
    let v' := (tag w.1.1).words.site (w.1.2,w.2)
    birthInput ((M.epoch n c).term q).val.pack.layout ((M.epoch n c).term q).val.rows.edge (ports (n+1))
      v (M.stepPrivatePrograms rows number hn c old q v) x =
      birthInput (c w.1.1).val.pack.layout (c w.1.1).val.rows.edge (ports n) v' (old w.1.1 v')
        (advancePowerInput y hy pos M n hn c tag w q x) := by
  let : Fintype (Port (fan S) P n) := portFintype
  let : Fintype (Port (fan S) P (n+1)) := portFintype
  let state := fun a : Admissible good (n+1) => Tracked (Port (fan S) Team (n+1)) Param Gadget exp a.val.pack.layout
  let env := fun a : Admissible good (n+1) => PowerInput a.val.pack.layout → PowerInput (c w.1.1).val.pack.layout
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  let value (a : Admissible good (n+1)) (t : state a) (p : Site.Programs a.val.pack.layout) (x' : PowerInput a.val.pack.layout) :=
    birthInput a.val.pack.layout a.val.rows.edge (ports (n+1)) (t.words.site w) (p _) x'
  let prior (x' : PowerInput (c w.1.1).val.pack.layout) := birthInput (c w.1.1).val.pack.layout (c w.1.1).val.rows.edge
    (ports n) ((tag w.1.1).words.site (w.1.2,w.2)) (old w.1.1 _) x'
  have carry {z z' : ProfileSum (Admissible good (n+1))} (he : z=z') (f : ∀ j, state (z'.term j))
      (g : ∀ j, env (z'.term j)) (p : family z') (ok : ∀ j x', value _ (f j) (p j) x' = prior (g j x')) :
      ∀ j x', value _ (move (V := state) he.symm f j) (Eq.mpr (congrArg family he) p j) x' =
        prior (move (V := env) he.symm g j x') := by
    subst z'
    exact ok
  unfold advance
  rw [dite_eq_left hn]
  exact carry (dite_eq_left hn) (emit (M n hn) y hy pos c tag)
    (fun j => emitPowerInput y hy pos (M n hn) c tag j w) ((M n hn).privatePrograms (rows n hn) c old number)
    (fun j => (M n hn).privatePrograms_birthInput y hy pos (rows n hn) (ports n) (ports (n+1)) (fieldRows n hn) number c old tag j w) q x

variable {Hidden : Type} (bottom : Admissible good 0)
    (base : @Site.Programs D _ (portFintype (k := fan S) (P := P) (b := 0)) _ bottom.val.pack.layout)
    (seed : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

include fieldRows in
/-- All original birth lanes agree on the actual retained owner and row-major
leaf through the complete selected outer history. -/
theorem historyPrivatePrograms_birthInput (n : ℕ) (hn : n≤T) (z : Fin ((fan S)^n) → Hidden)
    (q : (packHistory bottom M.epoch n).Index) (w : PowerSlot (Port (fan S) Team n) Param exp)
    (x : PowerInput ((packHistory bottom M.epoch n).term q).val.pack.layout) :
    let : Fintype (Port (fan S) P n) := portFintype
    let a := (packHistory bottom M.epoch n).term q
    let v := (Outer.term (geometry (good := good)) bottom M.epoch seed (advance M y hy pos) n z q).words.site w
    let : Fintype (Port (fan S) P 0) := portFintype
    let idx := portEquiv (fan S) Team n w.1
    let old := (seed (z idx.1)).words.site (idx.2,w.2)
    birthInput a.val.pack.layout a.val.rows.edge (ports n) v (M.historyPrivatePrograms rows number bottom base n hn q v) x =
      birthInput bottom.val.pack.layout bottom.val.rows.edge (ports 0) old (base old)
        (historyPowerInput y hy pos M bottom seed n hn z q w x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let H := packHistory bottom M.epoch n
    let c := fun j : Fin (fan S) => H.term (q.1 j)
    let sub := fun j : Fin (fan S) => fun i => z (copyIndex (fan S) n (j,i))
    let tag := fun j => Outer.term (geometry (good := good)) bottom M.epoch seed (advance M y hy pos) n (sub j) (q.1 j)
    let old := fun j => M.historyPrivatePrograms rows number bottom base n h.le (q.1 j)
    exact (M.stepPrivatePrograms_birthInput y hy pos rows ports fieldRows number n h c old tag q.2 w x).trans
      (ih h.le (sub w.1.1) (q.1 w.1.1) (w.1.2,w.2) _)

include fieldRows in
/-- In the flattened outer directory each retained native birth lane equals its
original input lane on the reconstructed original leaf. -/
theorem terminalPrivatePrograms_birthInput (q : (packHistory bottom M.epoch T).Index) (z : Fin ((fan S)^T) → Hidden)
    (w : PowerSlot (Port (fan S) Team T) Param exp)
    (x : PowerInput (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout) :
    let : Fintype (Port (fan S) P T) := portFintype
    let a := (packHistory bottom M.epoch T).term q
    let v := (terminal M y hy pos bottom seed q z).words.site w
    let : Fintype (Port (fan S) P 0) := portFintype
    let idx := portEquiv (fan S) Team T w.1
    let old := (seed (z idx.1)).words.site (idx.2,w.2)
    birthInput (flattenPack T a.val.pack).layout a.val.rows.edge (Flat.portRows T (ports T))
      v (M.terminalPrivatePrograms rows number bottom base q v) x =
      birthInput bottom.val.pack.layout bottom.val.rows.edge (ports 0) old (base old)
        (historyPowerInput y hy pos M bottom seed T le_rfl z q w ⟨x.edges,nestedPorts bits (fan S) T x.ports⟩) := by
  let : Fintype (Port (fan S) P T) := portFintype
  let a := (packHistory bottom M.epoch T).term q
  let v := (terminal M y hy pos bottom seed q z).words.site w
  exact (birthInput_flat T a.val.pack a.val.rows.edge (ports T) v
    (M.historyPrivatePrograms rows number bottom base T le_rfl q v) x).trans
    (M.historyPrivatePrograms_birthInput y hy pos rows ports fieldRows number bottom base seed T le_rfl z q w _)

end Machine
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
