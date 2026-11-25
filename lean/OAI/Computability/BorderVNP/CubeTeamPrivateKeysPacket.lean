import OAI.Computability.BorderVNP.CubeTeamPrivateKeysView
import Mathlib.Data.List.NodupEquivFin

/-! # The private keys of an owned packet in native body order

Each owned antipodal endpoint supplies its demand lanes. An active supply
lane belongs to the tail side only when its edge avoids the chosen cut.
The slot order is the order of the finite native demand and supply rectangles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.VertexIndex Tally VPVNP.MotifBase

open scoped Classical

variable {n d blocks h K : ℕ}

/-- Decode the private key of a physical body slot, skipping unused lanes,
crossing supplies and slots assigned to the opposite symbol group. -/
def packetPrivateKey (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1))
    (p : Packet n d blocks) (high : Bool) : BodySlot n b h s → Option (Assignment.BitIndex b s select)
  | .inl (e,j) =>
    if cornerBits p (Assignment.endVertex e) i = high then some (.inr (.inl (p,e,j))) else none
  | .inr (e,j) =>
    if hj : j.val < payload (onEdge s) (select p).2 e then
      if e.2 ≠ i ∧ cornerBits p e.1 i = high then some (.inr (.inr ⟨p,e,⟨j.val,hj⟩⟩)) else none
    else none

/-- Ordered keys for one high or low packet view in the actual physical body traversal. -/
def packetPrivateKeys (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1))
    (p : Packet n d blocks) (high : Bool) : List (Assignment.BitIndex b s select) :=
  (List.finRange (bodyWidth n b h s)).filterMap fun j =>
    packetPrivateKey b s select i p high ((bodyOrder n b h s).symm j)

private def keySlot {b s : ℕ} {select : Packet n d blocks → Selector n K h} :
    Assignment.BitIndex b s select → Option (BodySlot n b h s)
  | .inl _ => none
  | .inr (.inl (_,e,j)) => some (.inl (e,j))
  | .inr (.inr ⟨p,e,j⟩) => some (.inr (e,⟨j.val,j.isLt.trans_le (supplyWidth_le (select p) e s)⟩))

private theorem successful {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    {p : Packet n d blocks} {high : Bool} {x : BodySlot n b h s} {k : Assignment.BitIndex b s select}
    (hk : packetPrivateKey b s select i p high x = some k) :
    packetBitView i k = some (p,high) ∧ keySlot k = some x := by
  rcases x with ⟨e,j⟩ | ⟨e,j⟩
  · simp only [packetPrivateKey] at hk
    split_ifs at hk with side
    · obtain rfl := Option.some.inj hk
      exact ⟨by simp [packetBitView,side],rfl⟩
  · simp only [packetPrivateKey] at hk
    split_ifs at hk with live side
    · obtain rfl := Option.some.inj hk
      exact ⟨by simp [packetBitView,side.1,side.2],rfl⟩

/-- The private list contains precisely the active packet bits assigned to this oriented view. -/
theorem packetPrivateKeys_mem (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (p : Packet n d blocks) (high : Bool) (k : Assignment.BitIndex b s select) :
    k ∈ packetPrivateKeys b s select i p high ↔ packetBitView i k = some (p,high) := by
  constructor
  · intro hk
    obtain ⟨j,_,eq⟩ := List.mem_filterMap.mp hk
    exact (successful eq).1
  · intro hv
    have emit (x : BodySlot n b h s) (hx : packetPrivateKey b s select i p high x = some k) :
        k ∈ packetPrivateKeys b s select i p high := by
      exact List.mem_filterMap.mpr ⟨bodyOrder n b h s x,List.mem_finRange _,by rw [Equiv.symm_apply_apply,hx]⟩
    rcases k with z | (⟨p',e,j⟩ | ⟨p',e,j⟩)
    · cases hv
    · obtain ⟨rfl,side⟩ := Prod.mk.inj (Option.some.inj hv)
      apply emit (.inl (e,j))
      simp only [packetPrivateKey,ite_eq_left side]
    · by_cases cut : e.2 = i
      · simp [packetBitView,cut] at hv
      · rw [packetBitView,ite_eq_right cut] at hv
        obtain ⟨rfl,side⟩ := Prod.mk.inj (Option.some.inj hv)
        let lane : Fin (h*s) := ⟨j.val,j.isLt.trans_le (supplyWidth_le (select p') e s)⟩
        apply emit (.inr (e,lane))
        simp only [packetPrivateKey,lane,dite_eq_left j.isLt,ite_eq_left (And.intro cut side)]

/-- Every private key occurs once, since it recovers its own physical body address. -/
theorem packetPrivateKeys_nodup (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (p : Packet n d blocks) (high : Bool) :
    (packetPrivateKeys b s select i p high).Nodup := by
  apply (List.pairwise_lt_finRange _).filterMap
  intro j l lt k hk k' hk' eq
  subst k'
  exact lt.ne ((bodyOrder n b h s).symm.injective
    (Option.some.inj ((successful hk).2.symm.trans (successful hk').2)))

/-- Positions in the native private tape are in bijection with the bits of this packet and side. -/
noncomputable def packetPrivateKeysEquiv (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (p : Packet n d blocks) (high : Bool) :
    Fin (packetPrivateKeys b s select i p high).length ≃
      {k : Assignment.BitIndex b s select // packetBitView i k = some (p,high)} :=
  (List.Nodup.getEquiv _ (packetPrivateKeys_nodup ..)).trans
    (Equiv.subtypeEquivProp (funext fun k => propext (packetPrivateKeys_mem b s select i p high k)))

/-- The actual private tape length counts exactly its assigned physical bits. -/
theorem packetPrivateKeys_length (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (p : Packet n d blocks) (high : Bool) :
    (packetPrivateKeys b s select i p high).length =
      Fintype.card {k : Assignment.BitIndex b s select // packetBitView i k = some (p,high)} := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (packetPrivateKeysEquiv b s select i p high)

private theorem corner_eq (p : Packet n d blocks) (v : Vertex (n+1)) (i : Fin (n+1)) (high : Bool) :
    finTwoEquiv (v i) = ownerBit i p.1.2 high ↔ cornerBits p v i = high := by
  by_cases zero : i = 0
  · subst i
    cases hor : p.1.2 <;> cases hbit : finTwoEquiv (v 0) <;> cases high <;> simp [cornerBits,ownerBit,hor,hbit]
  · simp [cornerBits,ownerBit,zero]

/-- The native body consumes exactly the prescribed bits looked up in private key order. -/
theorem packetPrivateKeys_choices {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (p : Packet n d blocks) (high : Bool) {owner : Fin d → Team}
    (bits : Assignment.Choices b s select i owner) :
    ((bodyPositions (select p) i (ownerBit i p.1.2 high) (Assignment.demands bits p)
      (Assignment.supplies bits p)).map Position.digit).flatMap Digit.choices =
      (packetPrivateKeys b s select i p high).map (Assignment.lookup bits) := by
  rw [bodyPositions,List.ofFn_eq_map,List.map_map,List.flatMap_map,packetPrivateKeys,
    List.map_filterMap,List.filterMap_eq_flatMap_toList]
  apply List.flatMap_congr
  intro l _
  dsimp only [Function.comp_apply]
  cases hx : (bodyOrder n b h s).symm l with
  | inl z =>
    rcases z with ⟨e,j⟩
    simp only [ownedPosition,← show Assignment.endVertex e = (if e.2 then stop e.1 else start e.1) from rfl,
      corner_eq,packetPrivateKey]
    split_ifs <;> rfl
  | inr z =>
    rcases z with ⟨e,j⟩
    simp only [ownedPosition,packetPrivateKey,corner_eq]
    split_ifs <;> simp_all [Position.digit,Digit.choices,Assignment.supplies]

end Cube.Scatter

end BorderVNP
end Computability
end OAI
