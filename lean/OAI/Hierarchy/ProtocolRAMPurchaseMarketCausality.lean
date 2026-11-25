import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult
import OAI.Hierarchy.TaggedWireReadBanks

namespace OAI
/-! # Causality of the frozen purchase table and its residual tile words

The two executions may use different initial memories and different slab fixtures.
At a given permutation and threshold, every published word depends on the true
signed stock cells at entry. The frame also identifies the addresses outside the
working interval that retain their original contents.
-/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe PurchaseCT
open WireTelescope.ReadBanks
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

/-- Address of the true signed inventory word for one geometric tile and axis. -/
def stockAddress (sh : Shelf) (t : StageAt z d) (r : Fin (2^z)) (a : Fin k × Bool) : ℕ :=
  sh.stockBase + PurchaseInventory.slot (.inr ((r,stageNumber t),a))

theorem stockAddress_bounds (sh : Shelf) (t : StageAt z d) (r : Fin (2^z)) (a : Fin k × Bool) :
    sh.stockBase ≤ sh.stockAddress t r a ∧
      sh.stockAddress t r a < sh.stockBase + PurchaseInventory.footprint z (2*rounds d+1) k :=
  ⟨Nat.le_add_right .., Nat.add_lt_add_left (PurchaseInventory.slot_lt (.inr ((r,stageNumber t),a))) _⟩

def SameStock (sh : Shelf) (k : ℕ) (left right : Mem z d) : Prop :=
  ∀ (t : StageAt z d) (r : Fin (2^z)) (a : Fin k × Bool),
    left (sh.stockAddress t r a) = right (sh.stockAddress t r a)

theorem sameStock_of_agree (sh : Shelf) {future : ℕ → Prop} {left right : Mem z d}
    (agree : Agree future left right)
    («public» : ∀ (t : StageAt z d) (r : Fin (2^z)) (a : Fin k × Bool), ¬future (sh.stockAddress t r a)) :
    sh.SameStock k left right := fun t r a => agree _ («public» t r a)

theorem sameStock_of_public_interval (sh : Shelf) {future : ℕ → Prop} {left right : Mem z d}
    (agree : Agree future left right)
    («public» : ∀ x, sh.stockBase ≤ x → x < sh.stockBase + PurchaseInventory.footprint z (2*rounds d+1) k →
      ¬future x) : sh.SameStock k left right :=
  sh.sameStock_of_agree agree fun t r a =>
    «public» _ (sh.stockAddress_bounds t r a).1 (sh.stockAddress_bounds t r a).2

theorem marked_congr (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ) {left right : Mem z d}
    (same : sh.SameStock k left right) (i : Key z d k) :
    sh.marked phase T kind left i = sh.marked phase T kind right i := by
  ext r
  let t := stage i
  have tested : PurchaseMarks.tested (k:=k) phase T kind sh.table (sh.stock (k:=k) t) left (r.val:Word _) =
      PurchaseMarks.tested (k:=k) phase T kind sh.table (sh.stock (k:=k) t) right (r.val:Word _) := by
    funext j
    have room := (height_extent z d).trans (extent_word z d copies).le
    have stockEq := congrArg Fin.val (same t r (PurchaseMarks.signedDirection k j))
    have a := PurchaseInventory.read sh.stockBase (stageNumber t) j r left room
    have b := PurchaseInventory.read sh.stockBase (stageNumber t) j r right room
    have eqWord : ((sh.stock (k:=k) t j).read left (r.val:Word _)).val =
        ((sh.stock (k:=k) t j).read right (r.val:Word _)).val := a.trans (stockEq.trans b.symm)
    simp only [PurchaseMarks.tested,eqWord]
  simp only [marked,PurchaseMarks.stratum,Finset.mem_filter,t] at tested ⊢
  rw [tested]

/-- The complete range in which the native frozen market can change memory. -/
def workRegion (sh : Shelf) (S : PurchaseSampler) (z d k depth a : ℕ) : Prop :=
  sh.firstBase ≤ a ∧ a < sh.flagsBase S z d k depth + count z d k * paths z S.degree depth

/-- The locally preserved sampler and gate directories. -/
def romAddress (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (a : ℕ) : Prop :=
  let L := sh.L S depth i
  (L.start≤ a ∧ a< L.signed.base) ∨ (L.gates.base≤ a ∧ a< L.packed)

structure Control (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (left right : Mem z d) : Prop where
  packed : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
    let addr := sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val
    sh.result S k depth left addr = sh.result S k depth right addr
  slabFlags : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
    let addr := PurchaseStage.decisionBase (sh.desc S depth i)+r.val
    sh.result S k depth left addr = sh.result S k depth right addr
  remaining : ∀ (i : Key z d k) (r : Fin (2^z)),
    let addr := (sh.desc S depth i).work+4+r.val
    sh.result S k depth left addr = sh.result S k depth right addr
  rows : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)) (j : Fin (depth+1)),
    let addr := (sh.L S depth i).source.base+(j.val*paths z S.degree depth+r.val)
    sh.result S k depth left addr = sh.result S k depth right addr
  rom : ∀ (i : Key z d k) (a : ℕ), sh.romAddress S depth i a → left a=right a →
    sh.result S k depth left a = sh.result S k depth right a
  leftFrame : sh.Untouched (k:=k) S depth left (sh.result S k depth left)
  rightFrame : sh.Untouched (k:=k) S depth right (sh.result S k depth right)

/-- Physical decision, residual, and trajectory fields published to later passes. -/
inductive Published (sh : Shelf) (S : PurchaseSampler) (z d k depth : ℕ) : ℕ → Prop where
  | packed (i : Key z d k) (r : Fin (paths z S.degree depth)) :
      Published sh S z d k depth (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)
  | slabFlag (i : Key z d k) (r : Fin (paths z S.degree depth)) :
      Published sh S z d k depth (PurchaseStage.decisionBase (sh.desc S depth i)+r.val)
  | residue (i : Key z d k) (r : Fin (2^z)) :
      Published sh S z d k depth ((sh.desc S depth i).work+4+r.val)
  | tile (i : Key z d k) (r : Fin (paths z S.degree depth)) (j : Fin (depth+1)) :
      Published sh S z d k depth ((sh.L S depth i).source.base+(j.val*paths z S.degree depth+r.val))

theorem Control.published {sh : Shelf} {S : PurchaseSampler} {depth : ℕ} {left right : Mem z d}
    (h : sh.Control S k depth left right) (a : ℕ) (ha : sh.Published S z d k depth a) :
    sh.result S k depth left a = sh.result S k depth right a := by
  cases ha with
  | packed i r => exact h.packed i r
  | slabFlag i r => exact h.slabFlags i r
  | residue i r => exact h.remaining i r
  | tile i r j => exact h.rows i r j

/-- The exact live predicate for expressions that read the published table or a
public word outside the work slab. -/
theorem Control.observed {sh : Shelf} {S : PurchaseSampler} {depth : ℕ} {left right : Mem z d}
    (h : sh.Control S k depth left right) {future : ℕ → Prop} (start : Agree future left right) :
    ∀ a, ((¬future a ∧ (a < sh.firstBase ∨
        sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤ a)) ∨
        sh.Published S z d k depth a) →
      sh.result S k depth left a = sh.result S k depth right a :=
  WireTelescope.ReadBanks.published _ _ _ start h.leftFrame h.rightFrame h.published

/-- Endpoint scans may also read invariant directory words outside the future selector region. -/
theorem Control.observed_with_rom {sh : Shelf} {S : PurchaseSampler} {depth : ℕ} {left right : Mem z d}
    (h : sh.Control S k depth left right) {future : ℕ → Prop} (start : Agree future left right) :
    ∀ a, ((¬future a ∧ (a < sh.firstBase ∨
        sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤ a ∨
        ∃ i : Key z d k, sh.romAddress S depth i a)) ∨ sh.Published S z d k depth a) →
      sh.result S k depth left a = sh.result S k depth right a := by
  rintro a (⟨old,before|after|⟨i,inside⟩⟩|published)
  · exact h.observed start a (Or.inl ⟨old,Or.inl before⟩)
  · exact h.observed start a (Or.inl ⟨old,Or.inr after⟩)
  · exact h.rom i a inside (start a old)
  · exact h.published a published

/-- Both outputs are equal everywhere outside future cells and the working interval.
Within that interval the named published fields are equal by the other control clauses. -/
theorem Control.agree {sh : Shelf} {S : PurchaseSampler} {depth : ℕ} {left right : Mem z d}
    (h : sh.Control S k depth left right) {future : ℕ → Prop} (start : Agree future left right) :
    Agree (fun a => future a ∨ sh.workRegion S z d k depth a)
      (sh.result S k depth left) (sh.result S k depth right) := by
  intro a keep
  have prior := start a (fun hit => keep (Or.inl hit))
  have away : ¬sh.workRegion S z d k depth a := fun hit => keep (Or.inr hit)
  unfold workRegion at away
  have outside : a < sh.firstBase ∨ sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤ a := by omega
  exact (h.leftFrame a outside).trans (prior.trans (h.rightFrame a outside).symm)

/-- Equal true inventory words give equal native decisions and residual tile flags.
Other incoming words may differ whenever each memory satisfies its own entry conditions. -/
theorem result_control (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤ d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (left right fixtureL fixtureR : Mem z d)
    (inputL : sh.Incoming (k:=k) S π depth phase T kind left)
    (inputR : sh.Incoming (k:=k) S π depth phase T kind right)
    (preparedL : ∀ i : Key z d k, sh.Prepared S depth fixtureL i left)
    (preparedR : ∀ i : Key z d k, sh.Prepared S depth fixtureR i right)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies)
    (same : sh.SameStock k left right) : sh.Control S k depth left right := by
  obtain ⟨_,frameL,viewL,packedL⟩ := sh.run S π depth hd phase T kind left fixtureL inputL preparedL room
  obtain ⟨_,frameR,viewR,packedR⟩ := sh.run S π depth hd phase T kind right fixtureR inputR preparedR room
  have sets := sh.marked_congr phase T kind same
  have bits (i : Key z d k) :
      sh.decisions S π depth phase T kind left i = sh.decisions S π depth phase T kind right i := by
    simp only [decisions,sets i]
  refine ⟨?_,?_,?_,?_,?_,frameL,frameR⟩
  · intro i r
    simp only [packedL i r,packedR i r,bits i]
  · intro i r
    simp only [(viewL i).flags r,(viewR i).flags r,bits i]
  · intro i r
    simp only [(viewL i).residual r,(viewR i).residual r,sets i]
  · intro i r j
    let index : Fin (PurchaseDFS.layout (2^z) S.degree depth).length :=
      ⟨r.val,by simpa only [PurchaseDFS.length_layout,paths] using r.isLt⟩
    have both := ((viewL i).tiles index j).trans ((viewR i).tiles index j).symm
    simpa only [index,PurchaseDFS.length_layout,paths] using both
  · intro i a inside equal
    exact ((viewL i).rom a inside).trans (equal.trans ((viewR i).rom a inside).symm)

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
