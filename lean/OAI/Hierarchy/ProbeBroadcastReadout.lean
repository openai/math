import OAI.Hierarchy.ProbeBroadcastMatrix

namespace OAI
/-! # Reading the unique physical selector at each incident site -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators

variable {k n r : ℕ} {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
    [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

omit [Nonempty (Fin k)] in
/-- The binary packing used by splitPortState places the selector in the
low suffix. Its retained payload begins just above the allocated suffix. -/
theorem split_selector_bit (a q : Widths k) (i : Fin k) (z : State (a+q) i)
    (p : (portGraph k).Port i) (j : Fin (q p.val.1)) :
    (((splitPortState a q i z).2 p).val).testBit j.val=(z p).val.testBit j.val := by
  change ((z p).val % 2^(q p.val.1)).testBit j.val=_
  simp [Nat.testBit_mod_two_pow,j.isLt]

omit [Nonempty (Fin k)] in
theorem split_payload_bit (a q : Widths k) (i : Fin k) (z : State (a+q) i)
    (p : (portGraph k).Port i) (j : ℕ) :
    (((splitPortState a q i z).1 p).val).testBit j=(z p).val.testBit (q p.val.1+j) := by
  change ((z p).val / 2^(q p.val.1)).testBit j=_
  simp [Nat.testBit_div_two_pow,Nat.add_comm]

omit [Nonempty (Fin k)] in
theorem incident_selector (q : Widths k) (h : LooksConnected q n) (i j : Fin k) (sep : i≠j) :
    ∃ p : (portGraph k).Port i, n≤q p.val.1 := by
  classical
  by_contra! absent
  have noTouch (e : Chord k) (size : n≤q e) : e.val.1≠i ∧ e.val.2≠i := by
    constructor
    · intro a
      exact (Nat.not_lt.mpr size) (absent ⟨(e,false),a⟩)
    · intro a
      exact (Nat.not_lt.mpr size) (absent ⟨(e,true),a⟩)
  let hit := fun v : Fin k=>decide (v=i)
  have lam (e : Chord k) (size : n≤q e) : hit e.val.1=hit e.val.2 := by
    simp [hit,(noTouch e size).1,(noTouch e size).2]
  have impossible := h hit lam j i
  simp [hit,sep.symm] at impossible

omit [Nonempty (Fin k)] in
theorem colourState_injective (q : Widths k) (i : Fin k)
    (p : (portGraph k).Port i) (wide : n≤q p.val.1) : Function.Injective (colourState (n:=n) q i) := by
  intro a b same
  exact extendColour_injective q _ wide (congrFun same p)

/-- The site entry on a valid packed selector is one site LUT (and the
native verifier at the root), with the code read off an actual incident
chord. No enumeration of other hidden word arrangements is performed. -/
theorem Packet.broadcastMatrix_entry (P : Packet F edge req) (root : Fin k) (G : PortGraph (Fin k) B)
    (conn : BroadcastConnected G) (h : Histogram (Fin P.terms) r) (i j : Fin k) (apart : i≠j)
    (x : State (P.inputWidths r) i)
    (y : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i)
    (u : {w : Fin r→Fin P.terms // histogram w=h})
    (read : (splitPortState (P.outputWidths h) (G.chordWidths (fun _=>r*P.selectorBits)) i y).2 =
      colourState (G.chordWidths (fun _=>r*P.selectorBits)) i (P.copyCode h u)) :
    P.broadcastMatrix root r G h i x y =
      (if i=root then P.checkEntry h u else 1)*P.siteEntry h u i x
        (splitPortState (P.outputWidths h) (G.chordWidths (fun _=>r*P.selectorBits)) i y).1 := by
  let q:=G.chordWidths (fun _=>r*P.selectorBits)
  obtain ⟨pin,wide⟩ := incident_selector q (actual_links G conn _) i j apart
  have single := (colourState_injective q i pin wide).comp (P.copyCode h).injective
  simp only [broadcastMatrix,read]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ ne
    have diff : colourState q i (P.copyCode h u) ≠ colourState q i (P.copyCode h v) :=
      fun e=>ne (single e).symm
    split <;> rename_i condition
    · exfalso
      apply diff
      first | exact condition
    · exact zero_mul _
  · simp

/-- A malformed collection of incident socket bits contributes zero to
the signed contraction. -/
theorem Packet.broadcastMatrix_reject (P : Packet F edge req) (root : Fin k) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) (i : Fin k) (x : State (P.inputWidths r) i)
    (y : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i)
    (bad : ∀ u : {w : Fin r→Fin P.terms // histogram w=h},
      (splitPortState (P.outputWidths h) (G.chordWidths (fun _=>r*P.selectorBits)) i y).2 ≠
      colourState (G.chordWidths (fun _=>r*P.selectorBits)) i (P.copyCode h u)) :
    P.broadcastMatrix root r G h i x y=0 := by
  simp only [broadcastMatrix,ite_eq_right (bad _),zero_mul,Finset.sum_const_zero]

end Hierarchy.Probe
end

end OAI
