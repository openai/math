import OAI.Computability.BorderVNP.ShortenExecutedEpoch
import OAI.Computability.BorderVNP.PackedGridRepeat
import OAI.Computability.BorderVNP.PackedHistoryBounds
import OAI.Computability.BorderVNP.PackedCoverScale

/-!
# Repeated physical shortening at decreasing cover depths

Each outer node applies the same physical site-epoch construction to the
networks selected at its children. Its local choice is a valid histogram
of that particular run. The bottom pack may use the repeated-width public
grid and its exact private table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Finset
open scoped Classical
attribute [local instance] portFintype

variable {D : ℕ} {K : Type*} [Field K]

/-- The tile count is independent of which finite enumeration of the product
deck was used by the physical epoch. -/
theorem card_eq_sites (I : Type*) [Fintype I] (d : ℕ) (f : Fintype (I → Deck (d+1))) :
    @Fintype.card _ f = CoverScale.sites I d := by
  unfold CoverScale.sites
  simp only [← Nat.card_eq_fintype_card]

/-- Fixed data of a physical shortening epoch, including the chosen joint
histogram expansion for every actual input on every sufficiently deep cover. -/
structure Factory (D : ℕ) (K : Type*) [Field K] where
  /-- Maximum length of an integral site move. -/
  L : ℝ
  /-- The site length bound is positive. -/
  hL : 0 < L
  /-- Single-coordinate public routing letters are allowed site moves. -/
  generators : ∀ s : Cube D → gamma 1, s ≠ 1 →
    (∀ i, s i = 1 ∨ (s i).val ∈ routingGenerators) → s ∈ allowedMoves (Cube D) L
  /-- Inner stages in one epoch. -/
  stages : ℕ
  /-- The epoch contains a positive number of stages. -/
  stages_pos : 0 < stages
  /-- Number of packs entering each inner combining step. -/
  k : ℕ
  /-- Each inner step combines at least two packs. -/
  k_two : 2 ≤ k
  /-- Congruence levels consumed by an entire epoch. -/
  drop : ℕ
  /-- Lower threshold for the output depth less one. -/
  floor : ℕ
  /-- Coefficient of site incidence in the potential. -/
  weight : ℝ
  /-- The coefficient of incidence is positive. -/
  weight_pos : 0 < weight
  /-- Additive loss per tile in (6.1). -/
  E : ℝ
  /-- The additive coefficient is positive. -/
  E_pos : 0 < E
  /-- The concrete physical summands on the flattened ports of this input. -/
  choose : ∀ d ≥ floor, ∀ {P : Type} [Fintype P] {bits : P → ℕ}
    (input : Fin (k^stages) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (d+1+drop) L),
    SiteExpansion (outputDepth := d+1) (show 0 < k by omega) input route weight E

namespace Factory

/-- Use the specified machines, fixed independently of their child tuples,
and the actual executions of those machines. Every output and its enumeration
are definitionally the projection of this same execution. -/
noncomputable def ofSchedule [NeZero D] {m : ℕ} {e : PaidIdentity K D m} (S : SiteSchedule e)
    (machine : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ), S.Machine d P bits)
    (run : ∀ d (hd : d ≥ S.floor) (P : Type) [Fintype P] (bits : P → ℕ)
      (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
      (route : ∀ i, SiteRoutes (input i) (Cube D) (S.inputLevel d) S.budget),
      S.Execution (machine d hd P bits) input route) : Factory D K where
  L := S.budget
  hL := S.positiveBudget
  generators := S.generators
  stages := S.rounds
  stages_pos := S.positiveRounds
  k := S.fanIn
  k_two := S.atLeastTwo
  drop := S.drop
  floor := S.floor
  weight := S.weight
  weight_pos := S.positiveWeight
  E := S.error
  E_pos := S.positiveError
  choose d hd _ _ _ input route := (run d hd _ _ input route).expansion

variable (F : Factory D K)

/-- Outer fan-in, fixed before the first pack. -/
abbrev fan := F.k ^ F.stages

/-- Physical depth after exactly this many completed epochs. -/
def depth (start t : ℕ) := start - F.drop*t

/-- An actual valued network and its integral site routes at this depth. -/
structure State {P : Type} (bits : P → ℕ) (start t : ℕ) where
  /-- A pack on all its original copy-indexed free slots. -/
  pack : Pack D (Port F.fan P t) (width bits F.fan t) K
  /-- Physical origin of every vertex and allowed move of every charged cable. -/
  route : SiteRoutes pack (Cube D) (F.depth start t) F.L

variable {P : Type} [Fintype P] {bits : P → ℕ} {start T : ℕ}
variable (deep : F.floor + 1 + F.drop*T ≤ start)

include deep in
/-- Consecutive routed levels agree with the exact level loss in the epoch. -/
theorem levels {t : ℕ} (ht : t < T) :
    let low := F.depth start (t+1) - 1
    F.floor ≤ low ∧ low + 1 = F.depth start (t+1) ∧
      low + 1 + F.drop = F.depth start t := by
  have ht' := Nat.mul_le_mul_left F.drop (Nat.succ_le_of_lt ht)
  dsimp [depth]
  rw [Nat.mul_succ] at ht' ⊢
  omega

/-- The expansion of this tuple, on the level required by the one-epoch theorem. -/
noncomputable def output {t : ℕ} (ht : t < T) (c : Fin F.fan → F.State bits start t) :=
  F.choose (F.depth start (t+1)-1) (F.levels deep ht).1 (fun i => (c i).pack)
    (fun i => reindexRoutes (F.levels deep ht).2.2.symm (c i).route)

/-- One node of the outer tree on its real histograms. Beyond the last level
there are no further choices. -/
noncomputable def epoch (t : ℕ) (c : Fin F.fan → F.State bits start t) :
    ProfileSum (F.State bits start (t+1)) :=
  if ht : t < T then
    let H := F.output deep ht c
    ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
  else ⟨Empty,inferInstance,Empty.elim⟩

/-- The complete dependent history retains all physical routes of the final branch. -/
noncomputable def histories (bottom : F.State bits start 0) (t : ℕ) :=
  packHistory bottom (F.epoch deep) t

private theorem epoch_tensor {t : ℕ} (ht : t < T) (c : Fin F.fan → F.State bits start t)
    (x : Ports (width bits F.fan (t+1))) :
    (parallelPacks fun i => (c i).pack).tensor x = ∑ j, ((F.epoch deep t c).term j).pack.tensor x := by
  let H := F.output deep ht c
  let Z : ProfileSum (F.State bits start (t+1)) :=
    ⟨Fin H.terms,inferInstance,fun j => ⟨H.pack j,reindexRoutes (F.levels deep ht).2.1 (H.routes j)⟩⟩
  have he : F.epoch deep t c = Z := dite_eq_left ht
  exact (H.tensor x).trans (congrArg (fun (s : ProfileSum (F.State bits start (t+1))) =>
    ∑ j : s.Index, (s.term j).pack.tensor x) he.symm)

/-- Independent copies of the bottom tensor on the nested free slots. The
bottom slots may each encode a whole interval shared across its copies. -/
def copies (original : Pack D P bits K) : (t : ℕ) → Pack D (Port F.fan P t) (width bits F.fan t) K
  | 0 => original
  | t+1 => parallelPacks (fun _ : Fin F.fan => copies original t)

/-- Summing the physically selected outputs gives the original product tensor
on every exterior bit assignment. The bottom tensor may be represented by a
single grid of repeated-width channels. -/
theorem histories_tensor (original : Pack D P bits K) (bottom : F.State bits start 0)
    (base : bottom.pack.tensor = original.tensor)
    (t : ℕ) (ht : t ≤ T) (x : Ports (width bits F.fan t)) :
    (F.copies original t).tensor x =
      ∑ j, ((F.histories deep bottom t).term j).pack.tensor x := by
  classical
  induction t with
  | zero =>
    change original.tensor x = ∑ _ : PUnit, bottom.pack.tensor x
    rw [Fintype.sum_unique, base]
  | succ t ih =>
    let H := F.histories deep bottom t
    let source := F.copies original t
    change (parallelPacks fun _ : Fin F.fan => source).tensor x = _
    rw [show (parallelPacks fun _ : Fin F.fan => source).tensor x =
      ∏ i : Fin F.fan, source.tensor (fun p => x (i,p)) from
      Network.parallel_value (fun _ : Fin F.fan => source.layout) (fun _ => source.table) x]
    trans ∏ i : Fin F.fan, ∑ j : H.Index, (H.term j).pack.tensor (fun p => x (i,p))
    · exact prod_congr rfl fun i _ => ih (by omega) (fun p => x (i,p))
    rw [Fintype.prod_sum]
    change _ = ∑ j : Σ c : Fin F.fan → H.Index, (F.epoch deep t fun i => H.term (c i)).Index, _
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro c _
    exact (Network.parallel_value (fun i => (H.term (c i)).pack.layout)
      (fun i => (H.term (c i)).pack.table) x).symm.trans
        (F.epoch_tensor deep (Nat.lt_of_succ_le ht) (fun i => H.term (c i)) x)

/-- The same sum holds after reconnecting the physical links, external pins
or any other exterior tensor. -/
theorem histories_sewn (original : Pack D P bits K) (bottom : F.State bits start 0)
    (base : bottom.pack.tensor = original.tensor)
    (t : ℕ) (ht : t ≤ T) {Q : Type*} {free : Q → ℕ}
    (outside : Network D (Q ⊕ Port F.fan P t) (Sum.elim free (width bits F.fan t)))
    (outer : outside.Tables K) (x : Ports free) :
    let source := F.copies original t
    let H := F.histories deep bottom t
    (outside.sew source.layout).value (outside.sewTables source.layout outer source.table) x =
      ∑ j, (outside.sew (H.term j).pack.layout).value
        (outside.sewTables (H.term j).pack.layout outer (H.term j).pack.table) x :=
  Network.value_sew_sum outside outer _ _ _ _ (F.histories_tensor deep original bottom base t ht) x

end Factory

/-- The paid crossing identity supplies one schedule and genuine physical
executions for every level, slot list and field-valued input tuple. -/
theorem nonempty_factory [NeZero D] {m : ℕ} (e : PaidIdentity K D m) (hm : 0 < m) :
    Nonempty (Factory D K) := by
  obtain ⟨S,h⟩ := exists_site_executions e hm
  let M (d : ℕ) (hd : d ≥ S.floor) (P : Type) [Fintype P] (bits : P → ℕ) :=
    (h d hd P bits).1.some
  exact ⟨Factory.ofSchedule S M (fun d hd P _ bits input route =>
    ((h d hd P bits).2 (M d hd P bits) input route).some)⟩

end Packing.PhysicalEpochs

end BorderVNP
end Computability
end OAI
