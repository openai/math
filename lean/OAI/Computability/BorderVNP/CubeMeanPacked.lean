import OAI.Computability.BorderVNP.CubeMeanBudget
import OAI.Computability.BorderVNP.CubePhysicalPaddingPublic

/-! # Packing the crossing bits with the incident-row label chooser

The algorithm visits every cell once in a prescribed order. Its choices balance the
live cable widths and incoming data simultaneously, and therefore determine an injection
of the live bits into the common packet capacity in Section 8.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Finset

variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)
variable {A : Type*} [Fintype A] (recv : A → Cell) (dataWidth : A → ℕ)

/-- Integer labels selected using the two sets of actual bits. -/
noncomputable def meanPackedCodes (cs : List Cell) (z : ℕ) : Cell → Fin (z+1) :=
  MeanChoice.follow (MeanChoice.loads (fun b : LiveBit N cell => crossSrc N cell b.1)
    (fun b : LiveBit N cell => crossDst N cell b.1) (fun b : Balancing.Bits dataWidth => recv b.1))
    cs ∅ (fun _ => 0)

/-- Product labels decoded from the chosen numeric codes. -/
noncomputable def meanPackedLabel (cs : List Cell) (n d : ℕ) (hd : 0 < d) : Cell → Label (n+1) d :=
  decodeProduct n d hd ∘ meanPackedCodes N cell recv dataWidth cs (d^(n+1)-1)

/-- The incident-row chooser satisfies both capacity inequalities on the packed network. -/
theorem meanPackedLoads (cs : List Cell) (nodup : cs.Nodup) (cover : cs.toFinset = univ)
    (n d : ℕ) (hd : 0 < d) {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1))) :
    let label := meanPackedLabel N cell recv dataWidth cs n d hd
    (∀ u v, Balancing.load (Balancing.cable (fun b : LiveBit N cell => crossSrc N cell b.1)
      (fun b : LiveBit N cell => crossDst N cell b.1) u v) label ≤ 4*W/(d^(n+1) : ℕ)^2) ∧
    ∀ u, Balancing.load (Balancing.datum (fun b : Balancing.Bits dataWidth => recv b.1) u)
      label ≤ 4*W/(d^(n+1) : ℕ) := by
  let Z := d^(n+1)
  let z := Z-1
  have hZ : 0 < Z := pow_pos hd _
  have hz : z+1 = Z := by dsimp only [z]; omega
  have hzR : (z : ℝ)+1 = Z := by exact_mod_cast hz
  have slack := h.variance
  change (Z : ℝ)^2*(4*W*M)+Z*(W*M) ≤ (W/(Z : ℝ)^2)^2 at slack
  rw [← hzR] at slack
  obtain ⟨hc,ha⟩ := MeanChoice.balanced (z := z)
    (fun b : LiveBit N cell => crossSrc N cell b.1) (fun b : LiveBit N cell => crossDst N cell b.1)
    (fun b : Balancing.Bits dataWidth => recv b.1) cs nodup cover W M (fun b => b.1.property)
    h.cableVolume h.dataVolume h.cableIncidence h.dataIncidence slack
  rw [hzR] at hc ha
  refine ⟨balanced_decode (decodeProduct n d hd) (crossSrc N cell) (crossDst N cell)
    (crossWidth N cell) (meanPackedCodes N cell recv dataWidth cs z) (fun e => e.property) _ hc, ?_⟩
  intro u
  have hx := ha ((decodeProduct n d hd).symm u)
  simpa only [Balancing.load, Balancing.datum, Balancing.hit, mem_singleton, forall_eq,
    meanPackedLabel, Function.comp_apply, ← Equiv.eq_symm_apply, meanPackedCodes, z, Z] using hx

/-- The physical crossing-bit embedding obtained by the incident-row chooser. -/
noncomputable def meanPackedEmbedding (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (nodup : cs.Nodup) (cover : cs.toFinset = univ) (n d : ℕ) (hd : 0 < d)
    {bc : ℕ} (hb : 0 < bc) {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1))) :
    LiveBit N cell ↪ Slot n d (blocksFor W bc (d^(n+1))) bc :=
  balancedPackedEmbedding N cell ord (meanPackedLabel N cell recv dataWidth cs n d hd)
    ((Nat.cast_nonneg _).trans h.dataVolume) hb (pow_pos hd _) (meanPackedLoads N cell recv dataWidth
      cs nodup cover n d hd h).1

/-- Exact bin and offset after labeling. This applies also to an edge whose endpoint labels agree. -/
theorem meanPackedEmbedding_address (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (nodup : cs.Nodup) (cover : cs.toFinset = univ) (n d : ℕ) (hd : 0 < d)
    {bc : ℕ} (hb : 0 < bc) {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let label := meanPackedLabel N cell recv dataWidth cs n d hd
    let s := meanPackedEmbedding N cell recv dataWidth ord cs nodup cover n d hd hb h ⟨e,j⟩
    s.1 = (label (crossSrc N cell e), label (crossDst N cell e)) ∧
      s.2.val = intervalStart (cablePair ord (crossSrc N cell) (crossDst N cell) label)
        (crossWidth N cell ∘ ord.symm) (ord e) + j.val := by
  exact packedSlot_address N cell ord _ _ _ _ e j

end Cube.Physical

end BorderVNP
end Computability
end OAI
