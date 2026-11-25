import OAI.ThreeFlat.Diagonal.HistogramOccupiedNetwork
import OAI.ThreeFlat.Diagonal.HistoryCrossPort
import OAI.ThreeFlat.Diagonal.ShrinkHistogramStep
import OAI.ThreeFlat.Diagonal.ShrinkDemandPointer

namespace OAI
/-! # Both input words of an occupied shrink motif in numbered physical coordinates -/

namespace ThreeFlat.Diagonal.CompressorPacking

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifOuterTerms MotifKernel MotifBinaryPacking
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L F : Type} [Field F]
    [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
    (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ) (code : Arc V H Tag L d c ↪ ℕ)
    (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (x : Histories P base r T) (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (layout : Bool) (n : Fin 4 → ℕ) (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c)
    (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L) {p h : ℕ}

/-- Full inherited row completed by zeros outside the unique parent. -/
def wholeRow (v : Site V Tag L) (z : OwnedRow P w layout v) (i : Position V H Tag L c) : (oldShape P w).Half i :=
  fun a => if yes : P.placement layout i=v then z ⟨i,yes⟩ a else (0 : Fin (2^w a.1.1))

@[simp] theorem oldEnds_whole (v : Site V Tag L) (z : OwnedRow P w layout v) (b : Bool) :
    oldEnds P w (wholeRow P w layout v z) b = ownedWords P w layout v z b := by
  funext a
  unfold oldEnds wholeRow ownedWords
  first | rfl

/-- Old bits are local pins in the site kernel. The only nonincident requests
are completed by literal false, just as in the physical history kernel. -/
def oldPinSource (v : Site V Tag L)
    (old : (i : {i // P.placement layout i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (m : P.Motif) (j : Fin 6) (q : demandGraph.Port j) (bit : Fin (demandWidth P w num m q.1.1)) : BitSource h p :=
  demandBit P code w hQ num (ownerSource P w layout v (fun u port t => .pin (old u port t))) m q.1.2 q.1.1 bit

theorem oldPinSource_read (v : Site V Tag L)
    (old : (i : {i // P.placement layout i=v}) → (a : (oldGraph P).Port i.val) → Fin (w a.1.1) → Fin p)
    (g : Fin h → Bool) (pin : Fin p → Bool) (z : OwnedRow P w layout v)
    (read : ∀ i a t, pin (old i a t) = (word _).symm (z i a) t)
    (m : P.Motif) (j : Fin 6) (q : demandGraph.Port j) (bit : Fin (demandWidth P w num m q.1.1)) :
    (oldPinSource P w code hQ num layout v old m j q bit).read g pin =
      (demandEnd P code w hQ num m (oldEnds P w (wholeRow P w layout v z) false)
        (oldEnds P w (wholeRow P w layout v z) true) q.1.2 q.1.1).val.testBit bit.val := by
  simp only [oldPinSource,oldEnds_whole]
  have ok := ownerSource_read P w layout v (fun u port t => BitSource.pin (internal:=h) (old u port t)) z g pin read
  simpa only [word_bit] using demandBit_read P code w hQ num _ (ownedWords P w layout v z) g pin ok m q.1.2 q.1.1 bit

abbrev outGraph := slotPortGraph (CompressorRefresh.union (shrinkingGraph P layout n order hc hn good) padding)
abbrev oldSupply := crossGraph (fun _ : P.Motif => supplyGraph) (partySite P layout)
abbrev bitsOn (e : CrossEdge P layout) := historyWidth P base r T x e.1 e.2
abbrev divisions (e : CrossEdge P layout) := n (typeIndex P hn good layout e)
abbrev allSlots := allPieceSlots P hn good layout n order hc pad
abbrev outputWidth := SlotRefinement.actualWidth (divisions P hn good layout n) (bitsOn P base r T x layout)
  (allSlots P hn good layout n order hc pad)
abbrev outRead := subdivisionRefines P hn good layout n order hc
    (fun m e => HistogramTileNetwork.Label (x m) (T m).output (T m).bits e) (bitsOn P base r T x layout)
    (fun _e => SlotRefinement.selectorWord _ _ _) positive pad padding

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
/-- The physical index resolves a crossing edge to its incident endpoint,
then to a single parallel slot and bit inside that slot. -/
def crossingPin (v : Site V Tag L)
    (addr : (a : (outGraph P hn good layout n order hc pad padding).Port v) →
      Fin (outputWidth P base r T x hn good layout n order hc pad a.1.1) → Fin p)
    (m : P.Motif) (a : ExternalAt supplyGraph (partySite P layout m) v) (bit : Fin (historyWidth P base r T x m a.val.val)) : Fin p := by
  let b := bitsOn P base r T x layout
  let gs : P.Motif → PortGraph (Fin 6) (Fin 8) := fun _=>supplyGraph
  let q : (oldSupply P layout).Port v := incidentPort gs (partySite P layout) v m a
  have edge : q.1.1=⟨m,a.val⟩ := incidentPort_edge gs (partySite P layout) v m a
  exact SlotRefinement.piecePin (oldSupply P layout) (outGraph P hn good layout n order hc pad padding)
    (divisions P hn good layout n) b (fun e => positive (typeIndex P hn good layout e))
    (allSlots P hn good layout n order hc pad) (physical_ends P hn good layout n order hc pad padding)
    addr q (Fin.cast (congrArg b edge).symm bit)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1600000 in
theorem crossingPin_read (v : Site V Tag L)
    (addr : (a : (outGraph P hn good layout n order hc pad padding).Port v) →
      Fin (outputWidth P base r T x hn good layout n order hc pad a.1.1) → Fin p)
    (pin : Fin p → Bool) (ys : (outGraph P hn good layout n order hc pad padding).State
      (fun e => Fin (2^outputWidth P base r T x hn good layout n order hc pad e)) v)
    (read : ∀ a t, pin (addr a t) = (ys a).val.testBit t.val)
    (m : P.Motif) (a : ExternalAt supplyGraph (partySite P layout m) v) (bit : Fin (historyWidth P base r T x m a.val.val)) :
    pin (crossingPin P base r T x hn good layout n positive order hc pad padding v addr m a bit) =
      (SlotRefinement.selectorWord (r m) (T m).bits (histWidth (T m).output (x m) a.val.val)
        (visible (fun _ : P.Motif=>supplyGraph) (partySite P layout)
          (fun k e=>HistogramTileNetwork.Label (x k) (T k).output (T k).bits e) v
          ((outRead P base r T x hn good layout n positive order hc pad padding).read v ys) m a.val)).val.testBit bit.val := by
  let gs : P.Motif→PortGraph (Fin 6) (Fin 8) := fun _=>supplyGraph
  let I := fun (k : P.Motif) (e : Fin 8)=>HistogramTileNetwork.Label (x k) (T k).output (T k).bits e
  let A := fun e : CrossEdge P layout=>I e.1 e.2
  let b := bitsOn P base r T x layout
  let enc : ∀ e : CrossEdge P layout,A e ≃ Fin (2^b e) :=
    fun e=>SlotRefinement.selectorWord (r e.1) (T e.1).bits (histWidth (T e.1).output (x e.1) e.2)
  let q : (oldSupply P layout).Port v:=incidentPort gs (partySite P layout) v m a
  have edge : q.1.1=⟨m,a.val⟩ := incidentPort_edge gs (partySite P layout) v m a
  let row := (outRead P base r T x hn good layout n positive order hc pad padding).read v ys
  have readBit := SlotRefinement.piecePin_read (A:=A) (oldSupply P layout) (outGraph P hn good layout n order hc pad padding)
    (divisions P hn good layout n) b (fun e => positive (typeIndex P hn good layout e))
    (allSlots P hn good layout n order hc pad) enc (physical_ends P hn good layout n order hc pad padding)
    ys addr pin read q (Fin.cast (congrArg b edge).symm bit)
  have transport {e f : CrossEdge P layout} (h : e=f) (val : A e) :
      (enc e val).val=(enc f (cast (congrArg A h) val)).val := by cases h; rfl
  have hv : cast (congrArg A edge) (row q)=visible gs (partySite P layout) I v row m a.val :=
    incident_read gs (partySite P layout) I v m a row
  have moved := transport edge (row q)
  rw [hv] at moved
  exact readBit.trans (congrArg (fun value : ℕ=>value.testBit bit.val) moved)

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
