import OAI.Hierarchy.ProtocolRAMStoredBoughtLocations
import OAI.Hierarchy.ProtocolRAMBoughtOrdinal
import OAI.Hierarchy.ProtocolRAMPurchaseLiveCount
import Mathlib.Data.Fintype.Fin

namespace OAI
/-! # A purchased typed chain's actual affirmative padded DFS ordinal -/

namespace Hierarchy.ProtocolRAM.BoughtLocation

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))} {depth : ℕ}
  {marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z))}

/-- Specialization to the actual native controller result. -/
def resultEquiv (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Shelf.Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k)) ≃
      Yes (count z d k*paths z S.degree depth) (sh.flagsBase S z d k depth) (sh.result S k depth frozen) :=
  packedEquiv sh phase T kind frozen _ (sh.run S π depth hd phase T kind frozen fixture input prepared room).2.2.2

@[simp] theorem resultEquiv_val (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Shelf.Mem z d)
    (input prepared room) (p : LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k))) :
    ((resultEquiv sh S π depth hd phase T kind frozen fixture input prepared room) p).val=relative p := rfl

/-- A permanent mode-gated archive keeps the exact ordinals of an accepting run.
The native calendar flag-write theorem supplies the assumed pointwise equality. -/
theorem archive_idle {w n : ℕ} (mode sourceBase archiveBase : ℕ) (source archive : Memory w)
    (idle : mode≠3) (flags : ∀ r : Fin n, archive (archiveBase+r.val)=
      if mode=3 then source (sourceBase+r.val) else 0) : ∀ r : Fin n, archive (archiveBase+r.val)=0 :=
  fun r => by simpa [idle] using flags r

def archiveEquiv {w n : ℕ} (sourceBase archiveBase : ℕ) (source archive : Memory w)
    (flags : ∀ r : Fin n, archive (archiveBase+r.val)=source (sourceBase+r.val)) :
    Yes n sourceBase source ≃ Yes n archiveBase archive where
  toFun r := ⟨r.val, (flags r.val).symm ▸ r.property⟩
  invFun r := ⟨r.val, flags r.val ▸ r.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def actualOfBuy (mode : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d) (buy : mode=3) :
    LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen) ≃
      LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k)) :=
  Equiv.cast (congrArg (LiveChains S π depth) (Shelf.catalogueMarks_buy mode sh phase T kind frozen buy))

/-- The measured catalogue indexes exactly the true reports in the permanent
archive, including attempts at which the controller wrote zero to every report. -/
def catalogueEquiv (mode : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen fixture archive : Shelf.Mem z d) (base : ℕ)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies)
    (flags : ∀ r : Fin (count z d k*paths z S.degree depth), archive (base+r.val)=
      if mode=3 then sh.result S k depth frozen (sh.flagsBase S z d k depth+r.val) else 0) :
    LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen) ≃
      Yes (count z d k*paths z S.degree depth) base archive :=
  if buy : mode=3 then
    ((actualOfBuy mode sh S π depth phase T kind frozen buy).trans
      (resultEquiv sh S π depth hd phase T kind frozen fixture input prepared room)).trans
      (archiveEquiv _ base _ archive (fun r => by simpa only [ite_eq_left buy] using flags r))
  else by
    letI : IsEmpty (LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen)) :=
      Fintype.card_eq_zero_iff.mp (Shelf.card_liveChains_idle mode sh S π depth phase T kind frozen buy)
    letI : IsEmpty (Yes (count z d k*paths z S.degree depth) base archive) :=
      ⟨fun r => r.property (archive_idle mode _ base _ archive buy flags r.val)⟩
    exact Equiv.equivOfIsEmpty _ _

theorem catalogueEquiv_val_of_buy (mode : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth : ℕ) (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen fixture archive : Shelf.Mem z d) (base : ℕ) (input prepared room flags)
    (p : LiveChains S π depth (Shelf.catalogueMarks (k:=k) mode sh phase T kind frozen)) (buy : mode=3) :
    ((catalogueEquiv mode sh S π depth hd phase T kind frozen fixture archive base input prepared room flags) p).val =
      relative (actualOfBuy mode sh S π depth phase T kind frozen buy p) := by
  simp only [catalogueEquiv,dite_eq_left buy,Equiv.trans_apply]; rfl

end
end Hierarchy.ProtocolRAM.BoughtLocation

end OAI
