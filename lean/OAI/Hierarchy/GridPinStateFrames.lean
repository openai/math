import OAI.Hierarchy.GridPinPublisher
import OAI.Hierarchy.GridPinPrefixFrames
import OAI.Hierarchy.GridPinBankRoom

namespace OAI
/-! # Read-only bank frames across the three native prefix passes -/

namespace Hierarchy.GridPinPublisher

open Computability.VPVNP.BurstRAM PrivateRAM GridPinNativeLoops

variable {W rawSize fullLanes : ℕ} {P : Plan}

/-- The machine computes factor addresses modulo the original factor count, and
the bucket pass advances the factor bases written by the preceding pass. -/
structure PrefixGeometry (W : ℕ) (P : Plan) (fullLanes : ℕ) : Prop where
  factorCount : P.factors≤2^W
  itemsFit : P.factor.items<2^W
  itemsPos : 0<P.factors→0<P.factor.items
  lanesFit : P.lanes≤fullLanes
  cursors : P.bucket.cursors=P.factor.bases

/-- Initial range checks on the two owner banks used for indirect addressing. -/
structure PrefixOwners (P : Plan) (m : Memory W) : Prop where
  factor : ∀ f : Fin P.factor.items,(m (P.factor.owners+f.val)).val<P.ticks
  lane : ∀ b : Fin P.lanes,(m (P.bucket.owners+b.val)).val<P.factor.items

/-- An address is outside the part of memory reserved to a named bank. -/
def Bank.Outside (b : Bank) (P : Plan) (rawSize fullLanes a : ℕ) : Prop :=
  outside (b.base P) (b.length P rawSize fullLanes) a

variable (R : BankRoom W P rawSize fullLanes)
include R

theorem BankRoom.seeded_outside (m : Memory W) (a : ℕ) (ht : Bank.ticks.Outside P rawSize fullLanes a) :
    P.seeded m a=m a :=
  seed_frame _ _ _ _ m (R.fit .ticks) a ht

theorem BankRoom.seeded_read (m : Memory W) (b : Bank) (h : b≠.ticks)
    (i : ℕ) (hi : i<b.length P rawSize fullLanes) : P.seeded m (b.base P+i)=m (b.base P+i) :=
  R.seeded_outside m _ (R.away b .ticks h hi)

theorem BankRoom.factorized_outside (G : PrefixGeometry W P fullLanes) (m : Memory W)
    (owner : ∀ f : Fin P.factor.items,(m (P.factor.owners+f.val)).val<P.ticks)
    (a : ℕ) (ht : Bank.ticks.Outside P rawSize fullLanes a)
    (hf : Bank.factors.Outside P rawSize fullLanes a) : P.factorized m a=m a := by
  have frame := factor_frame P.factor (P.seeded m) P.factors P.ticks
    G.itemsPos G.factorCount G.itemsFit (R.fit .owners) (R.fit .factors) (R.fit .ticks)
    (fun f=>by
      have h := R.seeded_read m .owners (by decide) _ f.isLt
      change P.seeded m (P.factor.owners+f.val)=m (P.factor.owners+f.val) at h
      rw [h]
      exact owner f)
    (fun f=>⟨R.away .owners .ticks (by decide) f.isLt,
      R.away .owners .factors (by decide) f.isLt⟩) a ht hf
  exact frame.trans (R.seeded_outside m a ht)

theorem BankRoom.factorized_read (G : PrefixGeometry W P fullLanes) (m : Memory W)
    (owner : ∀ f : Fin P.factor.items,(m (P.factor.owners+f.val)).val<P.ticks)
    (b : Bank) (bt : b≠.ticks) (bf : b≠.factors)
    (i : ℕ) (hi : i<b.length P rawSize fullLanes) : P.factorized m (b.base P+i)=m (b.base P+i) :=
  R.factorized_outside G m owner _ (R.away b .ticks bt hi) (R.away b .factors bf hi)

/-- Every immutable word can be followed from the incoming tape through tick
initialization, factor allocation and the active prefix of the lane archive. -/
theorem BankRoom.bucketed_outside (G : PrefixGeometry W P fullLanes) (m : Memory W) (owners : PrefixOwners P m)
    (a : ℕ) (ht : Bank.ticks.Outside P rawSize fullLanes a)
    (hf : Bank.factors.Outside P rawSize fullLanes a) (hb : Bank.blocks.Outside P rawSize fullLanes a) :
    P.bucketed m a=m a := by
  have srcFit : P.bucket.owners+P.lanes≤2^W := by
    have h : P.bucket.owners+fullLanes≤2^W := R.fit .ancestors
    exact (Nat.add_le_add_left G.lanesFit _).trans h
  have cpFit : P.bucket.cursors+P.factor.items≤2^W := by rw [G.cursors]; exact R.fit .factors
  have own (b : Fin P.lanes) : ((P.factorized m) (P.bucket.owners+b.val)).val<P.factor.items := by
    have h := R.factorized_read G m owners.factor .ancestors (by decide) (by decide) _ (b.isLt.trans_le G.lanesFit)
    change P.factorized m (P.bucket.owners+b.val)=m (P.bucket.owners+b.val) at h
    rw [h]
    exact owners.lane b
  have away (b : Fin P.lanes) : outside P.bucket.cursors P.factor.items (P.bucket.owners+b.val) ∧
      outside P.bucket.blocks P.lanes (P.bucket.owners+b.val) := by
    rw [G.cursors]
    exact ⟨R.away .ancestors .factors (by decide) (b.isLt.trans_le G.lanesFit),
      R.away .ancestors .blocks (by decide) (b.isLt.trans_le G.lanesFit)⟩
  have frame := bucket_frame P.bucket (P.factorized m) P.lanes P.factor.items srcFit
    (R.fit .blocks) cpFit own away a (by rw [G.cursors]; exact hf) hb
  exact frame.trans (R.factorized_outside G m owners.factor a ht hf)

theorem BankRoom.bucketed_read (G : PrefixGeometry W P fullLanes) (m : Memory W) (owners : PrefixOwners P m)
    (b : Bank) (bt : b≠.ticks) (bf : b≠.factors) (bb : b≠.blocks)
    (i : ℕ) (hi : i<b.length P rawSize fullLanes) : P.bucketed m (b.base P+i)=m (b.base P+i) :=
  R.bucketed_outside G m owners _ (R.away b .ticks bt hi) (R.away b .factors bf hi) (R.away b .blocks bb hi)

end Hierarchy.GridPinPublisher

end OAI
