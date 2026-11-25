import OAI.Hierarchy.ProbeColumnWires
import OAI.Hierarchy.ProbeDisjointStrips
import OAI.Hierarchy.ProbePayloadPlacement

namespace OAI
/-! # Identifying the unique physical source of an external catalyst debit -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ProbeStage ColumnWires
open scoped BigOperators Classical

variable {R C H E G : Type*} {k balls D : ℕ}

variable [Fintype C] [Fintype H] [Fintype E]

def catalystPort (bound : Fintype.card (Role C H E k)≤D) : C × Fin k ↪ Fin D :=
  let role : C × Fin k ↪ Role C H E k := {
    toFun := fun z=>.catalyst z.1 z.2
    inj' := by rintro ⟨c,i⟩ ⟨d,j⟩ same; simpa only [Role.catalyst.injEq,Prod.mk.injEq] using same }
  (role.trans (Fintype.equivFin _).toEmbedding).trans (Fin.castLEEmb bound)

/-- Zero-based ball and role addresses on the actual padded rectangle. -/
def portCell (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D) :
    R × (C × Fin k) ↪ Fin balls × Fin D := ballsAt.prodMap (catalystPort bound)

theorem no_padding (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (z : R × (C × Fin k)) : (portCell ballsAt bound z).2.val < Fintype.card (Role C H E k) :=
  ((Fintype.equivFin _) (.catalyst z.2.1 z.2.2 : Role C H E k)).isLt

/-- The key used by the reserve scatter retains the physical column and the axis. -/
def physical (cols : R × C ↪ G) : R × (C × Fin k) ↪ G × Fin k where
  toFun z := (cols (z.1,z.2.1),z.2.2)
  inj' := by
    rintro ⟨r,c,j⟩ ⟨s,e,i⟩ eq
    have pair := cols.injective (congrArg Prod.fst eq)
    have row : r=s := congrArg (fun x : R × C=>x.1) pair
    have col : c=e := congrArg (fun x : R × C=>x.2) pair
    have axis : j=i := congrArg (fun x : G × Fin k=>x.2) eq
    exact Prod.ext row (Prod.ext col axis)

/-- Row-major address of the reserve counters. This is also the arithmetic
used by the owner scanner on an actual column word. -/
def pairKeys (G : Type*) [Fintype G] (k : ℕ) : G × Fin k ≃ Fin (Fintype.card G*k) :=
  ((Fintype.equivFin G).prodCongr (Equiv.refl (Fin k))).trans finProdFinEquiv

theorem pairKeys_val [Fintype G] (c : G) (j : Fin k) :
    (pairKeys G k (c,j)).val=j.val+k*((Fintype.equivFin G) c).val := rfl

def payloadPairs {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) :=
  physical (k:=k) (payloadPlaceAll (d:=d) π)

def paidPairs {h d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h)))
    (unique : ∀ s c c' r, r ∈ marked s c → r ∈ marked s c' → c = c') :
    LiveChains S π depth marked × (ChainStrip.Columns depth × Fin k) ↪ PayloadColumns h d × Fin k :=
  let stage : StageColumns h d ↪ PayloadColumns h d := {
    toFun := fun c=>.inr (.inl c)
    inj' := fun _ _ e=>Sum.inl.inj (Sum.inr.inj e) }
  physical ((allStripColumns S π depth marked unique).trans stage)

/-- The outer check only uses the original payload prefix of its padded
physical market. -/
def payloadBalls (h balls : ℕ) (room : 2^h≤balls) : Fin (2^h) ↪ Fin balls := Fin.castLEEmb room

theorem payload_covered {h balls : ℕ} (room : 2^h≤balls) (j : Fin balls) (enters : j.val<2^h) :
    ∃r,payloadBalls h balls room r=j := ⟨⟨j.val,enters⟩,Fin.ext rfl⟩

/-- The purchased scan retains the original native row ordinal from its flag
word. The actual live-chain equivalence is supplied by `StripDirectory.liveBoardEquiv`. -/
def boughtBalls {n : ℕ} (flag : Fin n→Prop) (board : {i : Fin n // flag i} ≃ R) : R ↪ Fin n :=
  board.symm.toEmbedding.trans (Function.Embedding.subtype (p:=flag))

theorem bought_covered {n : ℕ} (flag : Fin n→Prop) (board : {i : Fin n // flag i} ≃ R)
    (j : Fin n) (affirmative : flag j) : ∃r,boughtBalls flag board r=j := by
  refine ⟨board ⟨j,affirmative⟩,?_⟩
  change (board.symm (board ⟨j,affirmative⟩)).val=j
  rw [Equiv.symm_apply_apply]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
