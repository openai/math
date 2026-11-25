import OAI.Computability.BorderVNP.DiagonalSavedBirthInputs
import OAI.Computability.BorderVNP.DiagonalFlatBirthInput
import OAI.Computability.BorderVNP.DiagonalTrackedReplayRead
import OAI.Computability.BorderVNP.PackedHistoryLeafPrograms

/-! # Private birth inputs at the tracked power slots of a normalized epoch

Following one physical site through the saved histogram tree recovers the input
of its original program on the same edge and port words as the tracked table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Adaptive Packing Packing.Inherited Epoch.Round
open Diagonal.CellEntries Diagonal.ExternalSew Site.Lineage
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 6000

private theorem birthInput_cast {D ne np : ℕ} {Q : Type} {bits : Q → ℕ} {f g : Fintype Q}
    (N : Network D Q bits) (edge : N.Edge ↪ Fin ne) (port : Q ↪ Fin np) (v : N.Site)
    (p : Site.Lineage (@Inherited.incoming D Q f bits N v)) (x : PowerInput N) :
    @birthInput D ne np Q g bits N edge port v (p.castWidth (incoming_instances N v)) x =
      @birthInput D ne np Q f bits N edge port v p x := by
  obtain rfl : g = f := Subsingleton.elim _ _
  rfl

variable {D m k b exp : ℕ} [NeZero D] {K I P E Team Param Gadget : Type}
    [Field K] [Field E] [Fintype I] [Fintype P] [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e : PaidIdentity K D m} (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows)
    (layout : F.SiteModelRows store rows) (number : e.Entry → ℕ) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

local notation3 "leaf₀" => (fun a => (view 0 a).pack)
local notation3 "net₀" => (fun n a => (view n a).pack.layout)
local notation3 "save₀" => namesStorage F store
local notation3 "move₀" => DenseReplay.move (Team := Team) (Param := Param) (exp := exp) F y hy pos save₀

/-- Every lane of the private birth input at the tracked owner agrees with its
original leaf's input on the words reconstructed through the selected inner history. -/
theorem replayPrivatePrograms_birthInput (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (input : ∀ i, Tracked Team Param Gadget exp (view 0 (flat i)).pack.layout)
    (q : (F.system.histories n hn (leavesEquiv k _ n flat)).Index)
    (w : PowerSlot (Port k Team n) Param exp)
    (x : PowerInput (net₀ n (RowTrace.state F.system n hn (leavesEquiv k _ n flat) q))) :
    let a := leavesEquiv k _ n flat
    let state := RowTrace.state F.system n hn a q
    let tracked := Replay.publicReplay F.system net₀ move₀ n hn a (Replay.flatInputs (net₀ 0) n flat input) q
    let v := let : Fintype (Port k Team n) := Replay.batchFinite k Team n; tracked.words.site w
    let bank := F.replayPrivatePrograms store rows number n hn a (nestedPrivatePrograms leaf₀ n flat initial) q
    let idx := portEquiv k Team n w.1
    let u := (input idx.1).words.site (idx.2,w.2)
    birthInput (net₀ n state) (layout.edges n state) (rows.ports n) v (bank v) x =
      birthInput (net₀ 0 (flat idx.1)) (layout.edges 0 (flat idx.1)) (rows.ports 0) u (initial idx.1 u)
        (DenseReplay.replayPowerInput F y hy pos save₀ n hn flat input q w x) := by
  induction n with
  | zero =>
    let v := (input 0).words.site w
    exact birthInput_cast (g := portFintype (k := k) (P := P) (b := 0))
      (net₀ 0 (flat 0)) (layout.edges 0 (flat 0)) (rows.ports 0) v (initial 0 v) x
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let i : Fin b := ⟨n,h⟩
    let a := leavesEquiv k _ (n+1) flat
    let sub (j : Fin k) (l : Fin (k^n)) := flat (copyIndex k n (j,l))
    let lower (j : Fin k) (l : Fin (k^n)) := input (copyIndex k n (j,l))
    let c (j : Fin k) := RowTrace.state F.system n h.le (a j) (q.1 j)
    let tag (j : Fin k) := Replay.publicReplay F.system net₀ move₀ n h.le (a j)
      (Replay.flatInputs (net₀ 0) n (sub j) (lower j)) (q.1 j)
    let bank := nestedPrivatePrograms leaf₀ (n+1) flat initial
    let old (j : Fin k) := F.replayPrivatePrograms store rows number n h.le (a j)
      (subInitial (view := view) n a bank j) (q.1 j)
    let child := w.1.1
    let u := let : Fintype (Port k Team n) := Replay.batchFinite k Team n; (tag child).words.site (w.1.2,w.2)
    let v : (raw (fun j => view n (c j))).layout.Site := ⟨child,u⟩
    let pre := DenseReplay.childPowerInput (F.stage i c) e q.2 v ((save₀ i c q.2).powerInput x)
    have step := F.savePrivatePrograms_birthInput store rows layout number i c q.2 old v x
    exact step.trans (ih h.le (sub child) (fun l => initial (copyIndex k n (child,l)))
      (lower child) (q.1 child) (w.1.2,w.2) pre)

/-- On the flat terminal, the checker at the selected power slot reads the entire
original birth input on the inverse row-major edge and port assignment. -/
theorem flatPrivatePrograms_birthInput (flat : Fin (k^b) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (input : ∀ i, Tracked Team Param Gadget exp (view 0 (flat i)).pack.layout)
    (q : F.Hist flat) (w : PowerSlot (Fin (k^b) × Team) Param exp)
    (x : PowerInput (flattenPack b (F.terminal flat q).pack).layout) :
    let state := RowTrace.state F.system b le_rfl (leavesEquiv k _ b flat) q
    let tracked := Replay.publicFlat F.system net₀ move₀ b le_rfl flat input q
    let v := tracked.words.site w
    let u := (input w.1.1).words.site (w.1.2,w.2)
    birthInput (flattenPack b (F.terminal flat q).pack).layout (layout.edges b state) (Flat.portRows b (rows.ports b))
      v (F.flatPrivatePrograms store rows number flat initial q v) x =
      birthInput (net₀ 0 (flat w.1.1)) (layout.edges 0 (flat w.1.1)) (rows.ports 0) u (initial w.1.1 u)
        (DenseReplay.flatPowerInput F y hy pos save₀ flat input q w x) := by
  let a := leavesEquiv k _ b flat
  let state := RowTrace.state F.system b le_rfl a q
  let prior := F.replayPrivatePrograms store rows number b le_rfl a (nestedPrivatePrograms leaf₀ b flat initial) q
  let tracked := Replay.publicReplay F.system net₀ move₀ b le_rfl a (Replay.flatInputs (net₀ 0) b flat input) q
  let idx := portEquiv k Team b
  let w' := (idx.symm w.1,w.2)
  let v := let : Fintype (Port k Team b) := Replay.batchFinite k Team b; tracked.words.site w'
  let z : PowerInput (net₀ b state) := ⟨x.edges,nestedPorts bits k b x.ports⟩
  have flatRead := birthInput_flat b (F.terminal flat q).pack (layout.edges b state) (rows.ports b) v (prior v) x
  have hist := F.replayPrivatePrograms_birthInput store rows layout number y hy pos b le_rfl flat initial input q w' z
  let val (j : Fin (k^b) × Team) (r : PowerInput (net₀ 0 (flat j.1))) :=
    let u := (input j.1).words.site (j.2,w.2)
    birthInput (net₀ 0 (flat j.1)) (layout.edges 0 (flat j.1)) (rows.ports 0) u (initial j.1 u) r
  have castRead {j j' : Fin (k^b) × Team} (h : j=j') (r : PowerInput (net₀ 0 (flat j.1))) :
      val j r = val j' (Eq.mp (congrArg (fun l : Fin (k^b) × Team => PowerInput (net₀ 0 (flat l.1))) h) r) := by
    subst j'
    rfl
  exact flatRead.trans (hist.trans (castRead (idx.apply_symm_apply w.1) _))

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
