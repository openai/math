import OAI.Hierarchy.ProtocolRAMBoughtOrdinal
import OAI.Hierarchy.ProtocolRAMStoredPurchaseCount
import Mathlib.Data.Fintype.Fin

namespace OAI
/-! # A purchased typed chain's stored affirmative padded DFS ordinal -/

namespace Hierarchy.ProtocolRAM.BoughtLocation

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))} {depth : ℕ}
  {marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z))}

theorem rows (p : LiveChains S π depth marked) (j : Fin (depth+1)) :
    Shelf.pathRows S π depth (keyOf p) (localIndex p) j=(liveRow S π depth marked p j).castSucc := by
  have hit := (StripDirectory.retainedRows S π depth marked p).choose_spec.2 j
  let first (t : StageAt z d) :=
    PurchaseStage.liveRows (advisedStage z d π t)
      (Fintype.equivFin (stageAt z d t).Group).toEmbedding
      (D:=S.degree) (portDigits (S.rows (stageAt z d t).span)) depth
  change first (stage (keyOf p)) (localIndex p) j = _
  rw [show stage (keyOf p)=p.1 from stage_key ..]
  exact hit

theorem flag (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (p : LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k))) :
    (sh.decisions S π depth phase T kind frozen (keyOf p))[(localIndex p).val]'(by
      simpa [PurchaseFrozen.paths] using (localIndex p).isLt)=true := by
  have hit := (StripDirectory.retainedRows S π depth (StripDirectory.actualMarks sh phase T kind frozen) p).choose_spec.1
  let mark := (sh.marked phase T kind frozen (keyOf p)).map Fin.castSuccEmb
  let ledger (t : StageAt z d) :=
    MarkTape.decisions (PurchaseTape.paths (advisedStage z d π t)
      (Fintype.equivFin (stageAt z d t).Group).toEmbedding (D:=S.degree)
      (portDigits (S.rows (stageAt z d t).span)) depth) mark
  have actual (t : StageAt z d) (atStage : t=p.1)
      (r : (localIndex p).val<(ledger t).length) : (ledger t)[(localIndex p).val]'r=true := by
    subst t
    exact hit
  exact actual (stage (keyOf p)) (stage_key ..)
    (show (localIndex p).val < (sh.decisions S π depth phase T kind frozen (keyOf p)).length from
      by simpa [PurchaseFrozen.paths] using (localIndex p).isLt)

/-- A physical affirmative flag is a predicate on the packed ordinal, so the
result applies equally to a live table and a guarded permanent archive. -/
abbrev Yes {w : ℕ} (n base : ℕ) (m : Memory w) := {r : Fin n // m (base+r.val) ≠ 0}

theorem card_yes {w n : ℕ} (base : ℕ) (m : Memory w) :
    Fintype.card (Yes n base m) =
      (List.ofFn (fun r : Fin n => decide (m (base+r.val)≠0))).count true := by
  rw [Fintype.card_subtype]
  simpa only [List.Vector.get_ofFn, List.Vector.toList_ofFn,decide_eq_true_eq] using
    Fin.card_filter_univ_eq_vector_get_eq_count true
      (List.Vector.ofFn (fun r : Fin n => decide (m (base+r.val)≠0)))

/-- The injection from selected chains to actual true bits is a bijection once
their measured counts agree. Its forward map retains the exact physical ordinal. -/
def equivOfCount {w : ℕ} (base : ℕ) (m : Memory w)
    (hit : ∀ p : LiveChains S π depth marked, m (base+(relative p).val) ≠ 0)
    (number : Fintype.card (LiveChains S π depth marked) =
      (List.ofFn (fun r : Fin (count z d k*paths z S.degree depth) => decide (m (base+r.val)≠0))).count true) :
    LiveChains S π depth marked ≃ Yes (count z d k*paths z S.degree depth) base m :=
  let f := fun p => (⟨relative p,hit p⟩ : Yes _ base m)
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨fun _p _q eq => relative_injective (congrArg Subtype.val eq),number.trans (card_yes base m).symm⟩)

@[simp] theorem equivOfCount_val {w : ℕ} (base : ℕ) (m : Memory w) (hit number)
    (p : LiveChains S π depth marked) : ((equivOfCount base m hit number) p).val=relative p := rfl

/-- Instantiate the bijection with the actual packed word readbacks of the
one native purchase run. -/
def packedEquiv (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen out : Shelf.Mem z d)
    (words : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
      out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)=
        MarkTape.encode (wordBits z d copies) ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp))) :
    LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k)) ≃
      Yes (count z d k*paths z S.degree depth) (sh.flagsBase S z d k depth) out := by
  apply equivOfCount
  · intro p
    have bit := words (keyOf p) (localRow p)
    have active := flag sh phase T kind frozen p
    have physical := bit.trans (congrArg (MarkTape.encode (wordBits z d copies)) active)
    have address : sh.flagsBase S z d k depth+(relative p).val=
        sh.flagsBase S z d k depth+(keyOf p).val*PurchaseFrozen.paths z S.degree depth+(localRow p).val := by
      rw [relative_val]
      change _ = _+(localIndex p).val
      omega
    rw [(congrArg out address).trans physical]
    have width : 0<wordBits z d copies := by unfold wordBits; omega
    exact of_decide_eq_true (PurchaseStage.decode_flag width true)
  · exact (sh.packedCount_liveChains S π depth phase T kind frozen out words).symm

@[simp] theorem packedEquiv_val (sh : Shelf) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (frozen out : Shelf.Mem z d) (words)
    (p : LiveChains S π depth (StripDirectory.actualMarks sh phase T kind frozen (k:=k))) :
    ((packedEquiv sh phase T kind frozen out words) p).val=relative p := rfl

end
end Hierarchy.ProtocolRAM.BoughtLocation

end OAI
