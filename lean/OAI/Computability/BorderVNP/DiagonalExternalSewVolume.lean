import OAI.Computability.BorderVNP.DiagonalExternalSew
import OAI.Computability.BorderVNP.DiagonalExternalSewIntervals
import OAI.Computability.BorderVNP.ShortenEpochLocalRecords

/-! # Record and wire costs of exterior interval sewing

A shared cable contributes one descriptor at each of its two actual ends.
Expanded weights also charge the whole width at each end. Sewing leaves
the old local boxes, cables, histories, and their payloads in place.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Finset
open scoped Classical

variable {D : ℕ} {P Free Cable : Type} [Fintype Cable] {width : Cable → ℕ}
variable {N : Network D P (fun _ => 1)} (B : Bundle N Free Cable width)

/-- The cost of the stored site histories and internal network before charging external ports. -/
noncomputable def boxCableRecords {P : Type} {bits : P → ℕ} (G : Network D P bits) (expanded : Bool)
    (prior payload : G.Site → ℕ) (test : G.Site → Prop) : ℕ :=
  testedWidth (fun v => boxCost expanded (prior v) (payload v)) test +
    testedWidth (fun e => recordCost expanded (G.width e)) (fun e => test (G.src e)) +
    testedWidth (fun e => recordCost expanded (G.width e)) (fun e => test (G.dst e))

/-- The cost at the two ends of all the new exterior intervals. -/
noncomputable def Bundle.endRecords (expanded : Bool) (test : N.Site → Prop) : ℕ :=
  testedWidth (fun x : Bool × Cable => recordCost expanded (width x.2))
    (fun x => test (B.endpoint x.2 x.1))

/-- Exact public or expanded cost at the selected sites after sewing. -/
theorem Bundle.localRecords_layout [Fintype Free] (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : N.Site → Prop) :
    localRecords B.layout expanded prior payload test =
      boxCableRecords N expanded prior payload test +
        testedWidth (fun _ : Free => recordCost expanded 1) (fun f => test (N.attach (B.ports (.inl f)))) +
        B.endRecords expanded test := by
  let w := fun c => recordCost expanded (width c)
  have endSum : ∀ s : Bool, testedWidth (fun e => recordCost expanded (B.layout.width e))
      (fun e => test ((if s then B.layout.dst else B.layout.src) e)) =
      testedWidth (fun e => recordCost expanded (N.width e)) (fun e => test ((if s then N.dst else N.src) e)) +
      testedWidth w (fun c => test (B.endpoint c s)) := by
    intro s
    cases s <;> unfold testedWidth <;>
      change (∑ e : N.Edge ⊕ Cable, _) = _ <;>
      rw [Fintype.sum_sum_type] <;> rfl
  have hw : B.endRecords expanded test =
      testedWidth w (fun c => test (B.endpoint c true)) + testedWidth w (fun c => test (B.endpoint c false)) := by
    unfold Bundle.endRecords testedWidth
    rw [Fintype.sum_prod_type,Fintype.sum_bool]
  unfold localRecords boxCableRecords
  have hs := endSum false
  have hd := endSum true
  simp only [Bool.false_eq_true,ite_false,ite_true] at hs hd
  rw [hs,hd,hw]
  change testedWidth _ test + (_ + _) + (_ + _) + testedWidth (fun _ : Free => recordCost expanded 1) _ =
    testedWidth _ test + _ + _ + testedWidth (fun _ : Free => recordCost expanded 1) _ + (_ + _)
  ac_rfl

/-- The fine one-bit port presentation charges each bit of a linked interval at both
ends. Free inputs keep their separate records in this presentation. -/
theorem Bundle.fine_records [Fintype Free] [Fintype P] (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : N.Site → Prop) :
    localRecords N expanded prior payload test =
      boxCableRecords N expanded prior payload test +
        testedWidth (fun _ : Free => recordCost expanded 1) (fun f => test (N.attach (B.ports (.inl f)))) +
        testedWidth (fun x : Bool × Cable => width x.2 * recordCost expanded 1)
          (fun x => test (B.endpoint x.2 x.1)) := by
  have hp : (∑ p : P, if test (N.attach p) then recordCost expanded 1 else 0) =
      ∑ z, if test (N.attach (B.ports z)) then recordCost expanded 1 else 0 := by
    symm
    apply Fintype.sum_equiv B.ports
    intro _; rfl
  unfold localRecords boxCableRecords testedWidth
  rw [hp]
  have single (s : Bool) (c : Cable) :
      (∑ _ : Fin (width c), if test (B.endpoint c s) then recordCost expanded 1 else 0) =
        if test (B.endpoint c s) then width c * recordCost expanded 1 else 0 := by
    by_cases h : test (B.endpoint c s) <;> simp [h]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_sigma,B.atEnd,single,Nat.add_assoc]

/-- Grouping nonempty exterior intervals can only lower public and expanded record costs. -/
theorem Bundle.localRecords_le_fine [Fintype Free] [Fintype P] (pos : ∀ c, 0 < width c)
    (expanded : Bool) (prior payload : N.Site → ℕ) (test : N.Site → Prop) :
    localRecords B.layout expanded prior payload test ≤ localRecords N expanded prior payload test := by
  rw [B.localRecords_layout,B.fine_records]
  apply Nat.add_le_add_left
  unfold Bundle.endRecords testedWidth
  apply sum_le_sum
  intro x _
  by_cases h : test (B.endpoint x.2 x.1)
  · simp only [h,ite_true]
    have := pos x.2
    cases expanded <;> simp [recordCost] <;> omega
  · simp [h]

/-- Total number of vertices and bit wires, including all open bit positions. -/
noncomputable def wireVolume {P : Type} [Fintype P] {bits : P → ℕ} (G : Network D P bits) : ℕ :=
  Fintype.card G.Site + (∑ e, G.width e) + ∑ p, bits p

/-- One closed bit wire replaces two open bit wires at unchanged vertices. -/
theorem Bundle.volume_layout [Fintype P] [Fintype Free] :
    wireVolume B.layout + ∑ c, width c = wireVolume N := by
  have h := Fintype.card_congr B.ports
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_sigma,Fintype.card_fin] at h
  change Fintype.card N.Site + (∑ e : N.Edge ⊕ Cable, Sum.elim N.width width e) +
    (∑ _ : Free, (1 : ℕ)) + (∑ c, width c) = Fintype.card N.Site + (∑ e, N.width e) + ∑ _ : P, (1 : ℕ)
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,card_univ,nsmul_eq_mul,mul_one]
  simp only [Nat.cast_id] at *
  omega

/-- Width carried by cables whose endpoints have different cell addresses. -/
noncomputable def intercellWidth {P : Type} {bits : P → ℕ} {C : Type*} (G : Network D P bits)
    (cell : G.Site → C) : ℕ := testedWidth G.width (fun e => cell (G.src e) ≠ cell (G.dst e))

/-- Co-located exterior wires need no intercell communication. -/
theorem Bundle.intercell_layout {C : Type*} (cell : N.Site → C) :
    intercellWidth B.layout cell = intercellWidth N cell +
      testedWidth width (fun c => cell (B.endpoint c false) ≠ cell (B.endpoint c true)) := by
  unfold intercellWidth testedWidth
  change (∑ e : N.Edge ⊕ Cable, _) = _
  rw [Fintype.sum_sum_type]
  rfl

/-- Moving or merging cells can charge at most the sum of all exterior cable widths
in addition to the actual surviving internal intercell width. -/
theorem Bundle.intercell_le {C : Type*} (cell : N.Site → C) :
    intercellWidth B.layout cell ≤ intercellWidth N cell + ∑ c, width c := by
  rw [B.intercell_layout]
  apply Nat.add_le_add_left
  exact sum_le_sum fun c _ => by split <;> simp_all

/-- Every bit of every paired field contributes to the global exterior width exactly once. -/
theorem sum_pieceWidth {F : Type} [Fintype F] (start : F → Bool → ℕ) (g link : ℕ) :
    ∑ c : Pieces start g link, pieceWidth start g c = Fintype.card F * link := by
  simpa only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod] using
    Fintype.card_congr (pieceBits (link := link) start g)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
