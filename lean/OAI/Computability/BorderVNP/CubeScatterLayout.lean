import OAI.Computability.BorderVNP.CubeScatterImage
import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe
import OAI.Computability.BorderVNP.CubeISAOwnedVertexModel

/-! # The scatter layout for an owned side of a physical cube packet

At each reserved endpoint the team guesses just the bits of its own demands.
A directed supply crossing the cut is copied from the shared group-pair list,
and a supply inside the group is guessed just once for both incident vertices.
Only positions below the selected edge width are used. The fixed table for a
selector, grouping coordinate and forced corner bit is independent of the input size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Tally VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM

variable {n b h K s : ℕ}

/-- Addressed positions of the two rectangles following a packet selector. -/
abbrev BodySlot (n b h s : ℕ) := (Ends n × Fin (h*b)) ⊕ (Edge (n+1) × Fin (h*s))

/-- Width of the demand and supply rectangles. -/
def bodyWidth (n b h s : ℕ) := Fintype.card (Ends n)*(h*b)+Fintype.card (Edge (n+1))*(h*s)

/-- Consecutive rectangle addresses following the selector use the native edge and end orders. -/
def bodyOrder (n b h s : ℕ) : BodySlot n b h s ≃ Fin (bodyWidth n b h s) :=
  (Equiv.sumCongr (((endOrder n).prodCongr (Equiv.refl _)).trans finProdFinEquiv)
    (((edgeOrder (n+1)).prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv

/-- An end's rectangular index agrees with the public bank offset. -/
theorem bodyOrder_end (e : Ends n) (j : Fin (h*b)) :
    selectorWidth n K h+(bodyOrder n b h s (.inl (e,j))).val = demandOffset n b h K e j := by
  change selectorWidth n K h+(j.val+(h*b)*(endOrder n e).val) = _+_*_+_
  ring

/-- A supply's reserved slot agrees with the table lookup's edge address. -/
theorem bodyOrder_supply (e : Edge (n+1)) (j : Fin (h*s)) :
    selectorWidth n K h+(bodyOrder n b h s (.inr (e,j))).val = supplyOffset n b h K s e j.val := by
  change selectorWidth n K h+(Fintype.card (Ends n)*(h*b)+(j.val+(h*s)*(edgeOrder (n+1) e).val)) = (_+_)+_*_+_
  ring

/-- The shared selector prefix uses the little-endian order expected by the lookup. -/
def selectorPositions (u : Selector n K h) : List Position :=
  List.ofFn fun j : Fin (selectorWidth n K h) => Position.selector
    (VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
      (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j)

/-- Placement and input bit of a single position of the two rectangles. -/
def ownedPosition (u : Selector n K h) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    BodySlot n b h s → Position
  | .inl (e,j) =>
    if finTwoEquiv ((if e.2 then stop e.1 else start e.1) i) = bit
    then .localBit (x e j) else .unused
  | .inr (e,j) =>
    if hj : j.val < payload (onEdge s) u.2 e then
      if e.2 = i then .crossing (z e ⟨j.val,hj⟩)
      else if finTwoEquiv (e.1 i) = bit then .localBit (z e ⟨j.val,hj⟩) else .unused
    else .unused

/-- The expected routed or private source at every bank offset after the selector. -/
def bodyPositions (u : Selector n K h) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    List Position := List.ofFn fun j => ownedPosition u i bit x z ((bodyOrder n b h s).symm j)

/-- The fixed source modes depend on the decoded selector and chosen group only. -/
def bodyModes (b s : ℕ) (u : Selector n K h) (i : Fin (n+1)) (bit : Bool) : List Mode :=
  (bodyPositions (b := b) (s := s) u i bit (fun _ _ => false) (fun _ _ => false)).map
    (fun p => p.digit.mode)

/-- The mode table physically inserted in the instruction program applies to all assignments. -/
theorem bodyModes_eq (u : Selector n K h) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    (bodyPositions u i bit x z).map (fun p => p.digit.mode) = bodyModes b s u i bit := by
  simp only [bodyModes,bodyPositions,List.map_ofFn,Function.comp_def]
  congr 1
  funext j
  cases (bodyOrder n b h s).symm j with
  | inl q => rcases q with ⟨e,k⟩; simp only [ownedPosition]; split_ifs <;> rfl
  | inr q => rcases q with ⟨e,k⟩; simp only [ownedPosition]; split_ifs <;> rfl

/-- The scatter creates all and only the data required to look up an owned vertex. -/
theorem image_vertexAt {w : ℕ} (hw : 0 < w) (base : ℕ) (m : Memory w) (u : Selector n K h)
    (i : Fin (n+1)) (bit : Bool) (v : Vertex (n+1)) (hv : finTwoEquiv (v i) = bit)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    let sel := image (selectorPositions u) base m
    let out := image (bodyPositions u i bit x z) (base+selectorWidth n K h) sel
    VertexAt out base u v x z := by
  intro sel out
  have bitval (t : Bool) : (wordBit w t).val = t.toNat := by
    apply Nat.mod_eq_of_lt
    have h : 1 < 2^w := one_lt_pow₀ (by decide) hw.ne'
    exact t.toNat_le.trans_lt h
  have body {q : BodySlot n b h s} {t : Bool} (hq : (ownedPosition u i bit x z q).value = some t) :
      (out (base+selectorWidth n K h+(bodyOrder n b h s q).val)).val = t.toNat := by
    let j := bodyOrder n b h s q
    have len : (bodyPositions u i bit x z).length = bodyWidth n b h s := List.length_ofFn
    have h := image_at (bodyPositions u i bit x z) (base+selectorWidth n K h) sel
      ⟨j.val, by rw [len]; exact j.isLt⟩ (b := t) (by simpa [bodyPositions,j] using hq)
    exact (congrArg Fin.val h).trans (bitval _)
  constructor
  · intro j
    have len : (selectorPositions u).length = selectorWidth n K h := List.length_ofFn
    change (image _ _ sel _).val = _
    rw [image_outside _ _ _ (Or.inl (by have := j.isLt; omega))]
    have hj := image_at (selectorPositions u) base m ⟨j.val,by rw [len]; exact j.isLt⟩
      (b := VPVNP.RAMSerialization.wordBits _ ⟨(selectorOrder n K h u).val,
        (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ j)
      (by simp [selectorPositions,Position.value])
    exact (congrArg Fin.val hj).trans (bitval _)
  · intro e he j
    rw [← bodyOrder_end (s := s) e j, ← Nat.add_assoc]
    apply body
    simp [ownedPosition,he,hv,Position.value]
  · intro e he j
    let k : Fin (h*s) := ⟨j.val,j.isLt.trans_le (supplyWidth_le u e s)⟩
    rw [show j.val = k.val from rfl,← bodyOrder_supply (b := b) e k,← Nat.add_assoc]
    apply body
    simp only [ownedPosition,show k.val < payload (onEdge s) u.2 e from j.isLt,dite_eq_left]
    by_cases hi : e.2 = i
    · simp [hi,Position.value,k]
    · have localBit : finTwoEquiv (e.1 i) = bit := by
        obtain he | he := he
        · simpa [he] using hv
        · have eq : head e i = e.1 i := by simp [head, step, Pi.single_eq_of_ne (Ne.symm hi)]
          rw [← eq,he,hv]
      simp [hi,localBit,Position.value,k]

end Cube.Scatter

end BorderVNP
end Computability
end OAI
