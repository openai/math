import OAI.Computability.VPVNP.SlotIncidence
import OAI.Computability.VPVNP.SlotBitCounts
import Mathlib.Tactic.Ring

/-!
# Exact number of demands per packed bundle

For a fixed bundle, Appendix C counts outgoing thin-endpoint demands in the
original outgoing numbering and incoming demands from thick endpoints in the
original incoming numbering. The tag offset and lane slot are fixed in both
enumerations, leaving only the old arc slot and its color bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup Tag]
variable (P : PackingData V H Tag L d c)

/-- Actual arc at an endpoint with prescribed bundle assignment. The old
incident slot is independent of the assignment's outgoing-slot coordinate. -/
def arcAtBundle (b : Site V Tag L × Fin d) (i : Fin d) (w : BitWord c) :
    Arc V H Tag L d c := ((P.offsetSite.symm b.1, i), w, P.slotLabel.symm b.2)

@[simp] theorem assigned_atBundle (b : Site V Tag L × Fin d) (i : Fin d) (w : BitWord c) :
    P.assignedBundle (sourcePosition (P.arcAtBundle b i w)) = b := by
  simp [arcAtBundle, sourcePosition, assignedBundle]

private theorem arcAtBundle_recover {a : Arc V H Tag L d c} {b : Site V Tag L × Fin d}
    (h : P.assignedBundle (sourcePosition a) = b) : P.arcAtBundle b a.1.2 a.2.1 = a := by
  subst b
  simp [arcAtBundle, assignedBundle, sourcePosition]

/-- A fixed assignment has one fiber for each incident slot, with the bit word
as its only free parameter. -/
def assignedArcEquiv (b : Site V Tag L × Fin d) (p : Arc V H Tag L d c → Prop) :
    {a : Arc V H Tag L d c // p a ∧ P.assignedBundle (sourcePosition a) = b} ≃
      Σ i : Fin d, {w : BitWord c // p (P.arcAtBundle b i w)} where
  toFun a := ⟨a.1.1.2, a.1.2.1, by rw [P.arcAtBundle_recover a.2.2]; exact a.2.1⟩
  invFun a := ⟨P.arcAtBundle b a.1 a.2.1, a.2.2, P.assigned_atBundle ..⟩
  left_inv a := Subtype.ext (P.arcAtBundle_recover a.2.2)
  right_inv _ := rfl

private theorem bit_ne_one (a : ZMod 2) : a ≠ 1 ↔ a = 0 := by
  exact (by decide : ∀ z : ZMod 2, z ≠ 1 ↔ z = 0) a

private theorem c_arithmetic {c : ℕ} (hc : 2 ≤ c) (d : ℕ) :
    d * 2 ^ (c - 1) + d * 2 ^ (c - 2) = 3 * (2 ^ c * d) / 4 ∧
      2 ^ (c - 2) * d = 2 ^ c * d / 4 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hc
  simp only [Nat.add_sub_cancel_left]
  have h : 2 + n - 1 = n + 1 := by omega
  rw [h, pow_succ, pow_add]
  have h₁ : d * (2 ^ n * 2) + d * 2 ^ n = 3 * (2 ^ n * d) := by ring
  have h₂ : 2 ^ 2 * 2 ^ n * d = 4 * (2 ^ n * d) := by ring
  rw [h₁, h₂]
  omega

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

private theorem card_outgoingC (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // ¬ P.thick (sourcePosition a) ∧
      P.assignedBundle (sourcePosition a) = b} = d * 2 ^ (c - 1) := by
  classical
  rw [Fintype.card_congr (P.assignedArcEquiv b (fun a ↦ ¬ P.thick (sourcePosition a))),
    Fintype.card_sigma]
  have hc (i : Fin d) : Fintype.card {w : BitWord c //
      ¬ P.thick (sourcePosition (P.arcAtBundle b i w))} = 2 ^ (c - 1) := by
    change Fintype.card {w : BitWord c // w (P.color b.1.1) ≠ 1} = _
    simpa only [bit_ne_one, Fintype.card_fin] using SlotPacking.card_oneBit (P.color b.1.1) 0
  simp [hc]

variable [AddCommGroup H] [AddCommGroup L]

private theorem card_incomingC (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // P.thick (sourcePosition (P.actual.symm a)) ∧
      ¬ P.thick (sourcePosition a) ∧ P.assignedBundle (sourcePosition a) = b} =
      d * 2 ^ (c - 2) := by
  classical
  let p := fun a : Arc V H Tag L d c ↦ P.thick (sourcePosition (P.actual.symm a)) ∧
    ¬ P.thick (sourcePosition a)
  have e := Equiv.subtypeEquivRight (p := fun a : Arc V H Tag L d c ↦
      P.thick (sourcePosition (P.actual.symm a)) ∧ ¬ P.thick (sourcePosition a) ∧
      P.assignedBundle (sourcePosition a) = b)
    (q := fun a ↦ p a ∧ P.assignedBundle (sourcePosition a) = b) (fun _ ↦ and_assoc.symm)
  rw [Fintype.card_congr (e.trans (P.assignedArcEquiv b p)), Fintype.card_sigma]
  have hc (i : Fin d) : Fintype.card {w : BitWord c // p (P.arcAtBundle b i w)} = 2 ^ (c - 2) := by
    let old := P.slots.target.symm (b.1.1, i)
    have hne : P.color old.1 ≠ P.color b.1.1 := by simpa [old] using P.proper old
    change Fintype.card {w : BitWord c //
      w (P.color old.1) - P.bitShift old (P.color old.1) = 1 ∧ w (P.color b.1.1) ≠ 1} = _
    simpa only [sub_eq_add_neg, add_zero, bit_ne_one, Fintype.card_fin] using
      SlotPacking.card_translatedBits hne (- P.bitShift old (P.color old.1)) 0 1 0
  simp [hc]

/-- Every packed bundle receives exactly Q old wires as CD demands. -/
theorem card_motifs_bundle (hc : 2 ≤ c) (b : Site V Tag L × Fin d) :
    Fintype.card {m : P.Motif // P.bundle m = b} = 3 * (2 ^ c * d) / 4 := by
  unfold bundle
  rw [Fintype.card_congr (P.cdIncidenceEquiv (fun x _ ↦ P.assignedBundle x = b)),
    Fintype.card_sum, P.card_outgoingC, P.card_incomingC]
  exact (c_arithmetic hc d).1

/-- Original base-color bit at a numbered endpoint. -/
def arcBit (a : Arc V H Tag L d c) : ZMod 2 := a.2.1 (P.color a.1.1.1)

/-- For any two endpoint types, a fixed base arc and source site carry K/4
wires of those types, including the bundle's thick–thick wires. -/
theorem card_bundle_types (hc : 2 ≤ c) (b : Site V Tag L × Fin d) (s t : ZMod 2) :
    Fintype.card {a : Arc V H Tag L d c // a.1 = b ∧ P.arcBit a = s ∧ P.arcBit (P.actual a) = t} =
      2 ^ c * d / 4 := by
  let p := fun u : BitWord c ↦ u (P.color b.1.1) = s ∧
    u (P.color (P.slots.target (b.1.1,b.2)).1) +
      P.bitShift (b.1.1,b.2) (P.color (P.slots.target (b.1.1,b.2)).1) = t
  let e : {a : Arc V H Tag L d c // a.1 = b ∧ P.arcBit a = s ∧ P.arcBit (P.actual a) = t} ≃
      {u : BitWord c // p u} × H := {
    toFun := fun a ↦ (⟨a.1.2.1, by
      rcases a with ⟨⟨b',u,h⟩, hbase, hs, ht⟩
      change b' = b at hbase
      subst b'
      exact ⟨hs,ht⟩⟩, a.1.2.2)
    invFun := fun a ↦ ⟨(b, a.1.1, a.2), rfl, a.1.2.1, a.1.2.2⟩
    left_inv := fun a ↦ Subtype.ext (Prod.ext a.2.1.symm rfl)
    right_inv := fun _ ↦ rfl }
  have hp : Fintype.card {u : BitWord c // p u} = 2 ^ (c - 2) := by
    simpa only [p, add_zero, Fintype.card_fin] using SlotPacking.card_translatedBits
      (P.proper (b.1.1,b.2)) 0 (P.bitShift (b.1.1,b.2) (P.color (P.slots.target (b.1.1,b.2)).1)) s t
  have hh : Fintype.card H = d := (Fintype.card_congr P.slotLabel).trans (Fintype.card_fin d)
  rw [Fintype.card_congr e, Fintype.card_prod, hp, hh]
  exact (c_arithmetic hc d).2

/-- Size of the thick–thick bundle whose payload is concatenated in §7.2. -/
theorem card_thick_bundle (hc : 2 ≤ c) (b : Site V Tag L × Fin d) :
    Fintype.card {a : Arc V H Tag L d c // a.1 = b ∧ P.thick (sourcePosition a) ∧
      P.thick (sourcePosition (P.actual a))} = 2 ^ c * d / 4 :=
  P.card_bundle_types hc b 1 1

/-- Count motifs at an endpoint by splitting that endpoint into its ports.
The permutation is the identity for A and the site arc matching for B. -/
private def rolePortEquiv (e : Equiv.Perm (Site V Tag L × Fin d)) (s : Site V Tag L) :
    {m : P.Motif // (e (P.bundle m)).1 = s} ≃
      Σ i : Fin d, {m : P.Motif // P.bundle m = e.symm (s, i)} where
  toFun m := ⟨(e (P.bundle m.1)).2, m.1, e.injective (by
    rw [e.apply_symm_apply]
    exact Prod.ext m.2 rfl)⟩
  invFun a := ⟨a.2.1, by rw [a.2.2, e.apply_symm_apply]⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨i,m,hm⟩
    apply Sigma.ext
    · simp [hm]
    · exact (Subtype.heq_iff_coe_eq (by simp [hm])).mpr rfl

private theorem rolePort_count (hc : 2 ≤ c) (e : Equiv.Perm (Site V Tag L × Fin d))
    (s : Site V Tag L) :
    Fintype.card {m : P.Motif // (e (P.bundle m)).1 = s} = d * (3 * (2 ^ c * d) / 4) := by
  rw [Fintype.card_congr (P.rolePortEquiv e s), Fintype.card_sigma]
  simp [P.card_motifs_bundle hc]

/-- Exactly dQ incidences of A occur at each packed site. -/
theorem card_roleA (hc : 2 ≤ c) (s : Site V Tag L) :
    Fintype.card {m : P.Motif // P.roleA m = s} = d * (3 * (2 ^ c * d) / 4) :=
  P.rolePort_count hc (Equiv.refl _) s

/-- Exactly dQ incidences of B occur at each packed site, including parallel arcs. -/
theorem card_roleB (hc : 2 ≤ c) (s : Site V Tag L) :
    Fintype.card {m : P.Motif // P.roleB m = s} = d * (3 * (2 ^ c * d) / 4) :=
  P.rolePort_count hc P.siteGraph.target s

end Compression.PackingData

end VPVNP
end Computability
end OAI
