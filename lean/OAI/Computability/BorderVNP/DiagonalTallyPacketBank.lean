import OAI.Computability.BorderVNP.DiagonalTallyPacketLookup

/-! # Addressing the actual selector, antipodal ends and directed cube edges

Every packet has a fixed slot for its selector, a rectangle for the two kinds of
demand endpoints, and a rectangle for directed edges. Unused slots in the latter
are skipped by the lookup. Their contents are immaterial to the result.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Tally

open VPVNP.MotifBase VPVNP.RAMSerialization

/-- Little-endian integer code of a cube corner's binary coordinate tuple. -/
def vertexOrder (a : ℕ) : Vertex a ≃ Fin (Fintype.card (Vertex a)) :=
  (finFunctionFinEquiv : (Fin a → Fin 2) ≃ Fin (2^a)).trans (finCongr (by simp [Vertex]))

/-- Consecutive directed edges at one corner, ordered by their direction. -/
def edgeOrder (a : ℕ) : Edge a ≃ Fin (Fintype.card (Edge a)) :=
  ((vertexOrder a).prodCongr (Equiv.refl _)).trans
    (finProdFinEquiv.trans (finCongr (by simp [Edge])))

/-- Consecutive source and destination endpoint slots at each antipodal pair. -/
def endOrder (n : ℕ) : Ends n ≃ Fin (Fintype.card (Ends n)) :=
  ((vertexOrder n).prodCongr finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by simp [Ends])))

/-- Copy number followed by the radix edge code of the ordered sequence in the selector. -/
def selectorOrder (n K h : ℕ) : Selector n K h ≃ Fin (Fintype.card (Selector n K h)) :=
  let tuple := (Equiv.piCongrRight fun _ : Fin h => edgeOrder (n+1)).trans finFunctionFinEquiv
  ((Equiv.refl (Fin K)).prodCongr tuple).trans
    (finProdFinEquiv.trans (finCongr (by simp [Selector])))

theorem edgeOrder_val (a : ℕ) (e : Edge a) :
    (edgeOrder a e).val = e.2.val+a*(vertexOrder a e.1).val := rfl

theorem endOrder_val (n : ℕ) (e : Ends n) :
    (endOrder n e).val = e.2.toNat+2*(vertexOrder n e.1).val := by
  cases e with
  | mk v b => cases b <;> rfl

variable {n b h K s D : ℕ}

/-- Per-edge public reservation for every possible selected term. -/
theorem supplyWidth_le (u : Selector n K h) (e : Edge (n+1)) (s : ℕ) :
    payload (onEdge s) u.2 e ≤ h*s := by
  unfold payload
  calc
    _ ≤ ∑ _ : Fin h, s := Finset.sum_le_sum fun _ _ => by unfold onEdge; split <;> omega
    _ = _ := by simp

/-- Width of the single physical selector field. -/
def selectorWidth (n K h : ℕ) : ℕ := Nat.clog 2 (Fintype.card (Selector n K h))

/-- Relative word address of one bit in a local demand endpoint. -/
def demandOffset (n b h K : ℕ) (e : Ends n) (j : Fin (h*b)) : ℕ :=
  selectorWidth n K h+(endOrder n e).val*(h*b)+j.val

/-- First supply word after the entire demand rectangle. -/
def supplyBase (n b h K : ℕ) : ℕ := selectorWidth n K h+Fintype.card (Ends n)*(h*b)

/-- Relative word address of one actual supply digit. The reservation uses the
uniform bound, so another term's narrower edge does not change this base. -/
def supplyOffset (n b h K s : ℕ) (e : Edge (n+1)) (j : ℕ) : ℕ :=
  supplyBase n b h K+(edgeOrder (n+1) e).val*(h*s)+j

/-- Total fixed reservation for one whole packet's publicly addressable bits. -/
def bankWidth (n b h K s : ℕ) : ℕ := supplyBase n b h K+Fintype.card (Edge (n+1))*(h*s)

private theorem rectangle_lt {m k : ℕ} (i : Fin m) {j : ℕ} (hj : j < k) :
    i.val*k+j < m*k := by
  have ht := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at ht
  omega

/-- Endpoint words occupy the half-open interval between selector and supplies. -/
theorem demandOffset_range (e : Ends n) (j : Fin (h*b)) :
    selectorWidth n K h ≤ demandOffset n b h K e j ∧ demandOffset n b h K e j < supplyBase n b h K := by
  have hi := rectangle_lt (endOrder n e) j.isLt
  unfold demandOffset supplyBase; omega

/-- Every true supply edge bit lies inside the reserved packet region. -/
theorem supplyOffset_range (u : Selector n K h) (e : Edge (n+1)) (j : Fin (payload (onEdge s) u.2 e)) :
    supplyBase n b h K ≤ supplyOffset n b h K s e j.val ∧
      supplyOffset n b h K s e j.val < bankWidth n b h K s := by
  have hi := rectangle_lt (edgeOrder (n+1) e) (j.isLt.trans_le (supplyWidth_le u e s))
  unfold supplyOffset bankWidth; omega

private theorem rect_inj {m k : ℕ} {i i' : Fin m} {j j' : ℕ} (hj : j < k) (hj' : j' < k)
    (he : i.val*k+j = i'.val*k+j') : i = i' ∧ j = j' := by
  have h := congrArg (· % k) he
  simp [Nat.add_mod,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hj'] at h
  exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt hj) (Nat.add_right_cancel (h ▸ he))),h⟩

/-- The physical endpoint ordinal is recoverable uniquely from its bit address. -/
theorem demandOffset_injective {e e' : Ends n} {j j' : Fin (h*b)}
    (he : demandOffset n b h K e j = demandOffset n b h K e' j') : e = e' ∧ j = j' := by
  unfold demandOffset at he
  have hx : (endOrder n e).val*(h*b)+j.val = (endOrder n e').val*(h*b)+j'.val := by omega
  obtain ⟨a,z⟩ := rect_inj j.isLt j'.isLt hx
  exact ⟨(endOrder n).injective a, Fin.ext z⟩

/-- The shared supply edge and its digit are recoverable from the reserved address. -/
theorem supplyOffset_injective {e e' : Edge (n+1)} {j j' : ℕ} (hj : j<h*s) (hj' : j'<h*s)
    (he : supplyOffset n b h K s e j = supplyOffset n b h K s e' j') : e=e' ∧ j=j' := by
  unfold supplyOffset at he
  have hx : (edgeOrder (n+1) e).val*(h*s)+j = (edgeOrder (n+1) e').val*(h*s)+j' := by omega
  obtain ⟨a,z⟩ := rect_inj hj hj' hx
  exact ⟨(edgeOrder _).injective a,z⟩

/-- A relative packet address for each row digit. Incident half-edges at the two
vertices of a supply read the same edge-bit location. -/
def rowOffset (u : Selector n K h) (v : Vertex (n+1)) (k : RowBit u v b s) : ℕ :=
  match k with
  | .inl (.inl ⟨e,j⟩) => demandOffset n b h K (e.val,false) j
  | .inl (.inr ⟨e,j⟩) => demandOffset n b h K (e.val,true) j
  | .inr (.inl ⟨e,j⟩) => supplyOffset n b h K s e.val j.val
  | .inr (.inr ⟨e,j⟩) => supplyOffset n b h K s e.val j.val

/-- All locally referenced row digits belong to the packet. -/
theorem rowOffset_lt (u : Selector n K h) (v : Vertex (n+1)) (k : RowBit u v b s) :
    rowOffset u v k < bankWidth n b h K s := by
  cases k with
  | inl x =>
    cases x with
    | inl x | inr x =>
      exact (demandOffset_range ..).2.trans_le (Nat.le_add_right _ _)
  | inr x =>
    cases x with
    | inl x | inr x => exact (supplyOffset_range u _ _).2

end Cube.Tally

end BorderVNP
end Computability
end OAI
