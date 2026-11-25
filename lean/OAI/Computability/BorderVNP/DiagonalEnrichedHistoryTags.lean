import OAI.Computability.BorderVNP.DiagonalEnrichedEpochTags
import OAI.Computability.BorderVNP.DiagonalEnrichedTerminal

/-! # All original work predicates and birth observations on the terminal history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Diagonal.ExternalSew Diagonal.CellEntries Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Site.Programs PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
open private move from OAI.Computability.BorderVNP.DiagonalFactoryReplay
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

universe u

variable {D m start T exp : ℕ} [NeZero D] {K E P Team Param Gadget Hidden : Type} [Field K] [Field E] [Fintype P]
    [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start}
    {V : ℕ → ℕ → Type} [∀ j i, Fintype (V j i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ t ht, (M t ht).F.SiteRows) {cap : ℕ → ℕ}
    (ports : ∀ t, Port (fan S) P t ↪ Fin (cap t))
    (layout : ∀ t ht, (M t ht).FieldRows (rows t ht) (ports t) (ports (t+1)))
    (y : e.Entry → E) (hy : ∀ p : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry p = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y p = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)


include layout in
/-- One actual machine step transports its private programs, specialized tags
and retained host map together along the very same dependent profile choice. -/
theorem stepPrivatePrograms_tagModels {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n)
    (old : ∀ j, Site.Programs (c j).val.pack.layout)
    (tags : ∀ j, @Tracked _ _ _ (Port (fan S) Team n) Param Gadget (Replay.batchFinite (fan S) Team n) inferInstance exp ((c j).val.pack.layout))
    (pred : ∀ j, (c j).val.pack.layout.Site → (ℕ → Bool) → Prop)
    (prior : ∀ j, TagModels (c j).val.pack.layout (c j).val.rows.edge (ports n) (old j) (@Tracked.tags _ _ _ (Port (fan S) Team n) Param Gadget (Replay.batchFinite (fan S) Team n) inferInstance exp _ (tags j)) num (pred j))
    (q : (M.epoch n c).Index) :
    TagModels ((M.epoch n c).term q).val.pack.layout ((M.epoch n c).term q).val.rows.edge (ports (n+1))
      (M.stepPrivatePrograms rows (num ∘ pos) hn c old q) (@Tracked.tags _ _ _ (Port (fan S) Team (n+1)) Param Gadget (Replay.batchFinite (fan S) Team (n+1)) inferInstance exp _ (EnrichedOuterReplay.advance M y hy pos n c tags q)) num
      (carryPred (enrichedStepHosts M hn c q).site (fun v => pred v.1 v.2)) := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  let hosts (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) →
    Retains (parallelPacks fun i => (c i).val.pack).layout (z.term j).val.pack.layout
  let tracks := fun z : Admissible good (n+1) => @Tracked _ _ _ (Port (fan S) Team (n+1)) Param Gadget (Replay.batchFinite (fan S) Team (n+1)) inferInstance exp (z.val.pack.layout)
  let models (z : ProfileSum (Admissible good (n+1))) (p : family z) (h : hosts z) (a : ∀ j, tracks (z.term j)) :=
    ∀ j, TagModels (z.term j).val.pack.layout (z.term j).val.rows.edge (ports (n+1)) (p j) (@Tracked.tags _ _ _ (Port (fan S) Team (n+1)) Param Gadget (Replay.batchFinite (fan S) Team (n+1)) inferInstance exp _ (a j)) num
      (carryPred (h j).site (fun v => pred v.1 v.2))
  have carry {z t : ProfileSum (Admissible good (n+1))} (e : z=t) (p : family t) (h : hosts t)
      (a : ∀ j, tracks (t.term j)) (ok : models t p h a) :
      models z ((congrArg family e).mpr p) ((congrArg hosts e).mpr h) (move (V:=tracks) e.symm a) := by
    subst t
    exact ok
  have eqn : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  unfold EnrichedOuterReplay.advance
  rw [dite_eq_left hn]
  exact carry eqn ((M n hn).privatePrograms (rows n hn) c old (num ∘ pos))
    (enrichedEpochHosts ((M n hn).run c) (M n hn).saveNames) (EnrichedOuterReplay.emit (M n hn) y hy pos c tags)
    ((M n hn).privatePrograms_tagModels (rows n hn) (ports n) (ports (n+1)) (layout n hn) y hy pos num c old tags pred prior) q

variable (bottom : Admissible good 0) (progs : Site.Programs bottom.val.pack.layout)
    (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)
    (condition : Hidden → bottom.val.pack.layout.Site → (ℕ → Bool) → Prop)
    (seed : ∀ h, TagModels bottom.val.pack.layout bottom.val.rows.edge (ports 0) progs (base h).tags num (condition h))

include layout seed in
/-- Every original private birth obeys exactly its own copy's predicate throughout
the complete attained public history, on the physical sparse edge and port names. -/
theorem historyPrivatePrograms_tagModels (n : ℕ) (hn : n≤T) (q : (packHistory bottom M.epoch n).Index)
    (z : Fin ((fan S)^n) → Hidden) :
    let state := ((packHistory bottom M.epoch n).term q).val
    let tag := Outer.term (fun _ (s : Admissible good _) => s.val.pack.layout) bottom M.epoch base
      (EnrichedOuterReplay.advance M y hy pos) n z q
    let names := originalNames (k:=fan S) (fun _ : Unit => bottom.val.pack) n (fun _ => ())
    let pred := fun v => condition (z (names v).1) (names v).2
    TagModels state.pack.layout state.rows.edge (ports n) (M.historyPrivatePrograms rows (num ∘ pos) bottom progs n hn q)
      (@Tracked.tags _ _ _ (Port (fan S) Team n) Param Gadget (Replay.batchFinite (fan S) Team n) inferInstance exp _ tag) num (carryPred (enrichedNestedHosts M bottom n hn q).site pred) := by
  induction n with
  | zero =>
    intro state tag names pred v
    exact (seed (z 0) v).congrPred fun g => (carryPred_old (Retains.id bottom.val.pack.layout).site pred v (extendWork g)).symm
  | succ n ih =>
    intro state tag names pred
    let h := Nat.lt_of_succ_le hn
    let H := packHistory bottom M.epoch n
    let c i := H.term (q.1 i)
    let old i := M.historyPrivatePrograms rows (num ∘ pos) bottom progs n h.le (q.1 i)
    let block (i : Fin (fan S)) (j : Fin ((fan S)^n)) := z (copyIndex (fan S) n (i,j))
    let child i := Outer.term (fun _ (s : Admissible good _) => s.val.pack.layout) bottom M.epoch base
      (EnrichedOuterReplay.advance M y hy pos) n (block i) (q.1 i)
    let orig := originalNames (k:=fan S) (fun _ : Unit => bottom.val.pack) n (fun _ => ())
    let keep i := enrichedNestedHosts M bottom n h.le (q.1 i)
    let childPred i := carryPred (keep i).site (fun v => condition (block i (orig v).1) (orig v).2)
    have next := M.stepPrivatePrograms_tagModels rows ports layout y hy pos num h c old child childPred
      (fun i => ih h.le (q.1 i) (block i)) q.2
    have lifts : carryPred (Retains.parallel keep).site pred = (fun v => childPred v.1 v.2) :=
      carryPred_parallel keep pred
    have join := (congrArg (carryPred (enrichedStepHosts M h c q.2).site) lifts.symm).trans
      (carryPred_trans (Retains.parallel keep).site (enrichedStepHosts M h c q.2).site pred)
    intro v
    exact (next v).congrPred fun g => Iff.of_eq (congrFun (congrFun join v) (extendWork g))

include layout seed in
/-- The row-major flattened terminal presents every original independent work
predicate on its actual retained physical host, and every scalar read belongs
to the specialized tag at that site's exact incidence input. -/
theorem terminalPrivatePrograms_tagModels (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((fan S)^T) → Hidden) :
    let state := ((packHistory bottom M.epoch T).term q).val
    TagModels (flattenPack T state.pack).layout state.rows.edge (Flat.portRows T (ports T))
      (M.terminalPrivatePrograms rows (num ∘ pos) bottom progs q)
      (@Tracked.tags _ _ _ (Port (fan S) Team T) Param Gadget (Replay.batchFinite (fan S) Team T) inferInstance exp _ (@Tracked.flat _ _ _ _ _ _ _ (Replay.batchFinite (fan S) Team T) inferInstance _ _ _ (EnrichedOuterReplay.terminal M y hy pos bottom base q z))) num
      (carryPred (enrichedOuterHosts M bottom q).site (fun v => condition (z v.1) v.2)) := by
  intro state
  let orig := originalNames (k:=fan S) (fun _ : Unit => bottom.val.pack) T (fun _ => ())
  let nested := enrichedNestedHosts M bottom T le_rfl q
  let pred := fun v : (parallelPacks fun _ : Fin ((fan S)^T) => bottom.val.pack).layout.Site =>
    condition (z v.1) v.2
  let tag := EnrichedOuterReplay.terminal M y hy pos bottom base q z
  let p : Pack D _ _ (Entry Param Gadget) := ⟨state.pack.layout,@Tracked.tags _ _ _ (Port (fan S) Team T) Param Gadget (Replay.batchFinite (fan S) Team T) inferInstance exp _ tag⟩
  have old := M.historyPrivatePrograms_tagModels rows ports layout y hy pos num bottom progs base condition seed T le_rfl q z
  have flat := TagModels.flatten T p state.rows.edge (ports T)
    (M.historyPrivatePrograms rows (num ∘ pos) bottom progs T le_rfl q) num (carryPred nested.site (pred ∘ orig)) old
  have same : carryPred nested.site (pred ∘ orig) = carryPred (enrichedOuterHosts M bottom q).site pred := by
    rw [←carryPred_equiv orig pred]
    exact carryPred_trans orig.symm.toEmbedding nested.site pred
  intro v
  exact (flat v).congrPred fun g => Iff.of_eq (congrFun (congrFun same v) (extendWork g))

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
