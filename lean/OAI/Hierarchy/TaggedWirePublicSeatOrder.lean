import OAI.Hierarchy.TaggedWireWordSeats
import OAI.Hierarchy.TaggedWireHistorySockets
import OAI.Hierarchy.TaggedWireRoleTableROM
import Mathlib.Data.Fin.Embedding

namespace OAI
/-! # Uniform public seat numbers including fixed identity turns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.WordSeats
open AdaptiveProbe ReportSockets HistoryRoles
open scoped Classical
set_option synthInstance.maxSize 1024

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
  (marked : Marks h W k attempts) (unique : Exclusive marked)

def fixedRoom := Incident.room k S.degree attempts + (1+2*k)+1

def room := fixedRoom (k:=k) (attempts:=attempts) S + (1+9*k)

abbrev All := (Catalogue S π depth marked × Bool) ⊕ Turn h (2^W) k

def fixedSite (x : Catalogue S π depth marked × Bool) :=
  Incident.choose (actualEnds S π depth marked x.1) x.2

def allSite : All S π depth marked → Site h (2^W) k := Sum.elim (fixedSite S π depth marked) (site π)

/-- The per-site number of each global role is a single public ROM lookup.
It depends only on the public site assignment and the global role name. -/
def publicOrdinal (v : Site h (2^W) k) :
    Incident.Fiber (HistoryRoles.site S (attempts:=attempts)) v ↪ Fin (fixedRoom (k:=k) (attempts:=attempts) S) where
  toFun p := ⟨HistoryRoles.code S p.val, HistoryRoles.code_bound S p.val⟩
  inj' a b eq := (HistoryRoles.code_unique S v a b).mp (congrArg Fin.val eq)

def fixedRole (v : Site h (2^W) k) :
    Incident.Fiber (fixedSite S π depth marked) v ↪
      Incident.Fiber (HistoryRoles.site S (attempts:=attempts)) v where
  toFun x := ⟨.inl (paid S π depth marked unique x.val),
    (paid_site S π depth marked unique x.val.1 x.val.2).trans x.property⟩
  inj' _ _ e := Subtype.ext ((paid S π depth marked unique).injective (Sum.inl.inj (congrArg Subtype.val e)))

/-- Fixed identities occupy the public half-port prefix. All live word paths
then use the same fixed family, axis and phase offsets at every site. -/
def allSeat (v : Site h (2^W) k) : Incident.Fiber (allSite S π depth marked) v ↪
    Fin (room (k:=k) (attempts:=attempts) S) :=
  (Incident.split (fixedSite S π depth marked) (site π) v).toEmbedding.trans
    ((((fixedRole S π depth marked unique v).trans (publicOrdinal S v)).sumMap (seat π v)).trans
      finSumFinEquiv.toEmbedding)

include unique in
theorem all_card (v : Site h (2^W) k) :
    Fintype.card (Incident.Fiber (allSite S π depth marked) v) ≤ room (k:=k) (attempts:=attempts) S := by
  exact (Fintype.card_le_of_injective _ (allSeat S π depth marked unique v).injective).trans_eq (Fintype.card_fin _)

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
