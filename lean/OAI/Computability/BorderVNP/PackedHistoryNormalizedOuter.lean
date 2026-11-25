import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched
import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.PackedHistoryOuter

/-! # Iterating the site-to-site frame on its complete stored rows

The physical state at each outer node retains its valued network, integral
routes, sparse row names and all bits returned by the preceding frame. The
next epoch runs on precisely these children. Its dependent local index is
the inner program's native joint histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter

open Crossing Epoch Epoch.Round Cover Shortening Packing Catalog Adaptive PublicCapacity VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- Number of whole site packs entering one epoch. -/
abbrev fan := S.fanIn^S.rounds

/-- Outer congruence depth after the specified number of epochs. -/
def depth (start t : ℕ) := start-S.drop*t

/-- Output level parameter for the epoch above the children at stage t. -/
def offset (start t : ℕ) := depth S start (t+1)-1

/-- Both boundary levels agree exactly with the prescribed outer depths. -/
theorem levels {start T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) :
    S.floor ≤ offset S start t ∧ offset S start t+1 = depth S start (t+1) ∧
      S.high (offset S start t) = depth S start t := by
  have h := Nat.mul_le_mul_left S.drop (Nat.succ_le_of_lt ht)
  simp only [offset,depth,SiteSchedule.high,Nat.mul_succ] at *
  omega

/-- Actual physical boundary state, including the slots occupied by zero-width
cables and the entire assigned pin vector consumed by the next epoch. -/
structure State (start : ℕ) (P : Type) (bits : P → ℕ) (shape : ℕ → Shape) (W : ℕ → Type) (t : ℕ) where
  /-- Valued network on the true nested ports. -/
  pack : Pack D (Port (fan S) P t) (width bits (fan S) t) K
  /-- Integral site routing at its outer congruence level. -/
  route : SiteRoutes pack (Cube D) (depth S start t) S.budget
  /-- Stable occupied rows in the allocated rectangle. -/
  rows : Rows (shape t) pack.layout
  /-- Endpoint of the dummy loop used at a vacant cable row. -/
  dummy : Fin (shape t).edges → pack.layout.Site
  /-- All bits of the assigned outer frame. -/
  words : W t → Bool

variable {S} {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
    {good : ∀ t, State S start P bits shape W t → Prop}

/-- Only physical rows satisfying the incoming invariant are used as children. -/
abbrev Admissible (good : ∀ t, State S start P bits shape W t → Prop) (t : ℕ) := {s // good t s}

variable (deep : S.floor+1+S.drop*T ≤ start)

/-- The actual child routes transported to the starting level of this inner program. -/
noncomputable def routes {t : ℕ} (ht : t<T) (c : Fin (fan S) → Admissible good t) (i : Fin (fan S)) :=
  reindexRoutes (levels S deep ht).2.2.symm (c i).val.route

/-- Count pins for one inner round inside this outer epoch. -/
abbrev Count (S : SiteSchedule e) (start t : ℕ) (w : ℕ → ℕ) :=
  Physical.Pin (Cube D) (fun i => (S.source.pattern i).bins.Bin) (S.level (offset S start t)) e.count w

/-- Input assignment at the single public subdivision frame. -/
def childWords {t : ℕ} (c : Fin (fan S) → Admissible good t) : Fin (fan S) × W t → Bool :=
  fun a => (c a.1).val.words a.2

variable [∀ j, Fintype (W j)]

/-- A uniform inner program and its physical frames at this level. Every
child tuple uses the same circuits, with its own actual input assignments. -/
structure Epoch {t : ℕ} (ht : t<T) (good : ∀ t, State S start P bits shape W t → Prop)
    (V : ℕ → Type) [∀ j, Fintype (V j)] (w : ℕ → ℕ) where
  /-- Complete admissible states used inside this epoch. -/
  Inner : ℕ → Type u
  /-- Actual placement of each complete state. -/
  view : S.GeometricView (offset S start t) (Port (fan S) P t) (width bits (fan S) t) Inner
  /-- Program installed on these states. -/
  F : S.EnrichedProgram (offset S start t) view
  /-- The destination cable numbering and dense saved state for each inner-round histogram. -/
  saveNames : F.SaveNames
  records : ∀ i c, (F.stage i c).RecordFactor e (S.source.pattern i).record
  room : F.Fits w
  /-- All assigned bits of each stored state. -/
  pins : ∀ j, Inner j → V j → Bool
  /-- Public input subdivision, actual inner stages, and terminal placement. -/
  pre : Frame (Fin (fan S) × W t) (Fin (fan S) × V 0)
  /-- Inner-round circuits that read count pins and advance the stored state words. -/
  step : Steps S.fanIn S.rounds V (Count S start t w)
  /-- Terminal frame computing the next outer words from the original children and the final inner state. -/
  post : Frame ((Fin (fan S) × W t) ⊕ V S.rounds) (W (t+1))
  checked : LocalCorrect (F.codec room) (fun j z a => z = pins j a) step
  /-- Native enriched physical run on the supplied child packs and routes. -/
  run : ∀ c : Fin (fan S) → Admissible good t,
    SiteSchedule.EnrichedExecution F (fun i => (c i).val.pack) (routes deep ht c)
  initial : ∀ c i, (fun j => pre.eval (childWords c) (i,j)) = pins 0 ((run c).flat i)
  /-- Stable row names of each final routed histogram. -/
  rows : ∀ c (q : F.Hist (run c).flat),
    Rows (shape (t+1)) (flattenPack S.rounds (F.terminal (run c).flat q).pack).layout
  /-- Actual dummy loop endpoint carried by each vacant row. -/
  dummy : ∀ c (q : F.Hist (run c).flat),
    Fin (shape (t+1)).edges → (flattenPack S.rounds (F.terminal (run c).flat q).pack).layout.Site
  /-- The returned physical pack, names and computed pin vector meet the
  next stage's input invariant on this exact histogram. -/
  closed : ∀ c (q : F.Hist (run c).flat), good (t+1)
    ⟨flattenPack S.rounds (F.terminal (run c).flat q).pack,
      reindexRoutes (levels S deep ht).2.1 ((run c).output.out q).routes.flatten,
      rows c q,dummy c q,post.eval (Sum.elim (childWords c) (pins S.rounds ((run c).root q)))⟩

namespace Epoch

variable {deep} {t : ℕ} {ht : t<T} {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (E : Epoch deep ht good V w) (c : Fin (fan S) → Admissible good t)

/-- The true stored successor, including every assigned post-frame output bit. -/
noncomputable def term (q : E.F.Hist (E.run c).flat) : Admissible good (t+1) :=
  ⟨_,E.closed c q⟩

/-- Every complete inner histogram appears once with its actual routed pack. -/
noncomputable def choice : ProfileSum (Admissible good (t+1)) :=
  ⟨E.F.Hist (E.run c).flat,inferInstance,E.term c⟩

/-- The local tensor equality uses the very native histogram index of the circuit. -/
theorem epochTensor (x : Ports (width bits (fan S) (t+1))) :
    (parallelPacks (fun i => (c i).val.pack)).tensor x =
      ∑ q : E.F.Hist (E.run c).flat, ((E.term c q).val.pack).tensor x := by
  have h := (E.run c).output.tensor x
  rwa [funext (E.run c).originalPack] at h

set_option maxHeartbeats 1400000 in
/-- Equation (6.1) for each actual returned routed branch on these children. -/
theorem epochBound (q : E.F.Hist (E.run c).flat) :
    (E.term c q).val.route.potential S.weight / (S.fanIn : ℝ)^S.rounds ≤
      maximumLeaf S.positiveFanIn id (fun i => (c i).val.route.potential S.weight)/2 +
      S.error*Fintype.card (Cube D → Deck (depth S start t+1)) := by
  have h := (E.run c).output.bound q
  rw [funext (E.run c).originalPotential] at h
  have left := reindexRoutes_potential (levels S deep ht).2.1 ((E.run c).output.out q).routes.flatten S.weight
  have inputs : (fun i => (routes deep ht c i).potential S.weight) =
      (fun i => (c i).val.route.potential S.weight) :=
    funext fun i => reindexRoutes_potential (levels S deep ht).2.2.symm _ _
  rw [inputs,(levels S deep ht).2.2] at h
  have heq : (E.term c q).val.route.potential S.weight = ((E.run c).output.out q).routes.potential S.weight :=
    left.trans (((E.run c).output.out q).routes.flatten_potential S.weight)
  rw [heq]
  exact h

end Epoch
end PackedHistoryCircuit.Normalized.EnrichedOuter

end BorderVNP
end Computability
end OAI
