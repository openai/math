import OAI.Computability.BorderVNP.RoutingLoad
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators

/-!
# Broadcast agreement and the multiplicity of routed link assignments

Section 8.3 fixes an epoch path, selectors, all contraction bits, and the
literal sources of deliveries. A physical block carries a common broadcast and
round-robin bits. A chosen endpoint of each demand checks its own copy, so
a literal delivery can originate at either end. The relay compares its two copies. These local tests and the zero
padding force the entire physical assignment, also on the unit branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

variable {R : ℕ}

/-- A physical block joins two distinct teams. -/
abbrev Block (R : ℕ) := {p : Fin R × Fin R // p.1 < p.2}

/-- An endpoint of the given physical block. -/
def Incident (u : Fin R) (b : Block R) : Prop := u = b.val.1 ∨ u = b.val.2

/-- Each team checks equality of the prefixes in all of its incident blocks. -/
def LocalBroadcast {Header : Type*} (broadcast : Block R → Header) : Prop :=
  ∀ (u : Fin R) (b c : Block R), Incident u b → Incident u c → broadcast b = broadcast c

/-- Connectedness of the complete team graph propagates the common broadcast
between any two physical blocks. -/
theorem broadcast_eq {Header : Type*} {broadcast : Block R → Header}
    (h : LocalBroadcast broadcast) (b c : Block R) : broadcast b = broadcast c := by
  rcases lt_trichotomy b.val.1 c.val.1 with hlt | heq | hgt
  · let d : Block R := ⟨(b.val.1, c.val.1), hlt⟩
    exact (h b.val.1 b d (Or.inl rfl) (Or.inl rfl)).trans
      (h c.val.1 d c (Or.inr rfl) (Or.inl rfl))
  · exact h b.val.1 b c (Or.inl rfl) (Or.inl heq)
  · let d : Block R := ⟨(c.val.1, b.val.1), hgt⟩
    exact (h b.val.1 b d (Or.inl rfl) (Or.inr rfl)).trans
      (h c.val.1 d c (Or.inl rfl) (Or.inl rfl))

/-- The ordinal positions in the `u` to `v` block with `u` an endpoint of
the demand and `v` its intermediate team. -/
abbrev Hop (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R) :=
  (w : Fin R) × ↥(pairBits hR u w v (demand width u w))

/-- The physical indices for both directions occupy exactly the load used in (8.2). -/
theorem card_hop (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u v : Fin R) :
    Fintype.card (Hop hR width u v) = legLoad hR width u v := by
  simp [Hop, legLoad, pairLoad]

private theorem pairBits_swap (hR : 2 < R) (width : Fin R → Fin R → ℕ) (u w v : Fin R) :
    pairBits hR u w v (demand width u w) = pairBits hR w u v (demand width w u) := by
  by_cases h : u = w
  · subst w
    rfl
  · rw [pairBits, pairBits, dite_eq_left h, dite_eq_left (Ne.symm h)]
    simp only [demand, ite_eq_right h, ite_eq_right (Ne.symm h), min_comm w u, max_comm w u]
    simp_rw [relay_swap hR h]

/-- The other hop of a transmission, as inspected by its relay `v`. -/
def otherHop (hR : 2 < R) (width : Fin R → Fin R → ℕ) {u v : Fin R}
    (p : Hop hR width u v) : Hop hR width p.1 v :=
  ⟨u, ⟨p.2.val, (pairBits_swap hR width u p.1 v) ▸ p.2.property⟩⟩

variable {Header Pad : Type*}

/-- A physical assignment with one header per unordered block, one bit in
each used hop position, and one bit in each remaining padding position. -/
structure Messages (hR : 2 < R) (width : Fin R → Fin R → ℕ) (Header Pad : Type*) where
  /-- Broadcast prefix on each physical team block. -/
  broadcast : Block R → Header
  /-- One physical value per used leg of a routed transmission. -/
  hop : (u v : Fin R) → Hop hR width u v → Bool
  /-- Remaining physical bits, checked against zero. -/
  padding : Pad → Bool

/-- The source of a bit is specified relative to the increasing order on its
unordered demand pair. Either endpoint can hold a literal to be delivered. -/
def sourceTeam (high : Fin R → Fin R → ℕ → Bool) (u w : Fin R) (j : ℕ) : Fin R :=
  if high (min u w) (max u w) j then max u w else min u w

private theorem source_swap (high : Fin R → Fin R → ℕ → Bool) (u w : Fin R) (j : ℕ) :
    sourceTeam high u w j = sourceTeam high w u j := by simp [sourceTeam, min_comm, max_comm]

private theorem source_endpoint (high : Fin R → Fin R → ℕ → Bool) (u w : Fin R) (j : ℕ) :
    u = sourceTeam high u w j ∨ w = sourceTeam high u w j := by
  rcases le_total u w with h | h <;> unfold sourceTeam <;> split <;> simp [h]

/-- Local validators for a completely assigned contraction term. The argument
`payload lo hi j` is the fixed value of crossing bit or delivery number `j` on
that demand list. The first leg checks it and the relay checks equality. -/
def Checks (hR : 2 < R) (width : Fin R → Fin R → ℕ) (fixedBlock : Block R)
    (header : Header) (high payload : Fin R → Fin R → ℕ → Bool) (m : Messages hR width Header Pad) :
    Prop :=
  LocalBroadcast m.broadcast ∧ m.broadcast fixedBlock = header ∧
  (∀ (u v : Fin R) (p : Hop hR width u v), u = sourceTeam high u p.1 p.2.val →
    m.hop u v p = payload (min u p.1) (max u p.1) p.2.val) ∧
  (∀ (u v : Fin R) (p : Hop hR width u v), m.hop u v p = m.hop p.1 v (otherHop hR width p)) ∧
  (∀ a, m.padding a = false)

/-- Multiplicity one for all physical communications of a fully assigned
expansion term, including deliveries forced by a literal. Taking a constant
zero payload and the unit-branch header gives the unique unit-branch assignment. -/
theorem existsUnique_messages (hR : 2 < R) (width : Fin R → Fin R → ℕ) (fixedBlock : Block R)
    (header : Header) (high payload : Fin R → Fin R → ℕ → Bool) :
    ∃! m : Messages hR width Header Pad, Checks hR width fixedBlock header high payload m := by
  let m : Messages hR width Header Pad := {
    broadcast := fun _ ↦ header
    hop := fun u _ p ↦ payload (min u p.1) (max u p.1) p.2.val
    padding := fun _ ↦ false }
  refine ⟨m, ⟨fun _ _ _ _ _ ↦ rfl, rfl, ?_, ?_, fun _ ↦ rfl⟩, ?_⟩
  · intro u v p _
    rfl
  · intro u v p
    simp [m, otherHop, min_comm, max_comm]
  · intro n hn
    obtain ⟨hb, hf, hs, hr, hp⟩ := hn
    have hprefix : n.broadcast = m.broadcast :=
      funext fun b ↦ (broadcast_eq hb b fixedBlock).trans hf
    have hhop : n.hop = m.hop := by
      funext u v p
      rcases source_endpoint high u p.1 p.2.val with hu | hw
      · exact hs u v p hu
      · have hsource := hw.trans (source_swap high u p.1 p.2.val)
        rw [hr u v p, hs p.1 v (otherHop hR width p) hsource]
        simp [m, otherHop, min_comm, max_comm]
    have hpad : n.padding = m.padding := funext hp
    change Messages.mk n.broadcast n.hop n.padding = Messages.mk m.broadcast m.hop m.padding
    rw [hprefix, hhop, hpad]

end Routing

end BorderVNP
end Computability
end OAI
