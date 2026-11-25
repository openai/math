import OAI.Computability.BorderVNP.CubePhysicalPadding
import OAI.Computability.BorderVNP.CubeScales

/-! # Public label selection for a packed network

The rational balancing scan runs on the actual oriented crossing edges and
incoming data descriptors. Its numeric labels are decoded into base-`d`
coordinates. The two bounds of Lemma 8.2 then hold for these product labels,
so the rounded block capacity embeds every actual crossing bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Finset

variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)
variable {A : Type*} [Fintype A] (recv : A → Cell) (dataWidth : A → ℕ)

/-- Volume, incidence, and variance bounds on the live crossing and incoming
bits. The bound `M` is on bit incidence at a cell, while the algorithm itself
operates on cable and data descriptors. -/
structure PackedLabelBudget (W : ℝ) (M Z : ℕ) : Prop where
  /-- Total live crossing width is at most twice the volume budget. -/
  cableVolume : (Fintype.card (LiveBit N cell) : ℝ) ≤ 2*W
  /-- Total incoming bit volume is at most the volume budget. -/
  dataVolume : (Fintype.card (Balancing.Bits dataWidth) : ℝ) ≤ W
  /-- Live bits incident at either end of a given cell. -/
  cableIncidence : ∀ c : Cell, (univ.filter (fun b : LiveBit N cell =>
    c ∈ ({crossSrc N cell b.1, crossDst N cell b.1} : Finset Cell))).card ≤ M
  /-- Incoming bits delivered to a given cell. -/
  dataIncidence : ∀ c : Cell, (univ.filter (fun b : Balancing.Bits dataWidth => c = recv b.1)).card ≤ M
  /-- The sum of variance bounds is within the squared slack in Lemma 8.2. -/
  variance : (Z : ℝ)^2 * (4*W*M) + Z*(W*M) ≤ (W/(Z : ℝ)^2)^2

omit [Fintype Cell] in
open Filter in
/-- At the paper's alphabet and cell scales the variance inequality follows
uniformly from the volume lower bound and incidence cap. The threshold is
chosen before the packed network, its partition, and its incoming descriptors. -/
theorem eventually_packedLabelBudget {α ξ : ℝ} (hα : 0 < α) (a : ℕ)
    (hgap : 24*α*a + 1/4 < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (W : ℝ) (M : ℕ), (k : ℝ)^(1-ξ)/2 ≤ W → (M : ℝ) ≤ (k : ℝ)^(1/4 : ℝ) →
      ∀ (N : Network D P bits) (cell : N.Site → Cell) (recv : A → Cell) (dataWidth : A → ℕ),
        (Fintype.card (LiveBit N cell) : ℝ) ≤ 2*W → (Fintype.card (Balancing.Bits dataWidth) : ℝ) ≤ W →
        (∀ c : Cell, (univ.filter (fun b : LiveBit N cell =>
          c ∈ ({crossSrc N cell b.1, crossDst N cell b.1} : Finset Cell))).card ≤ M) →
        (∀ c : Cell, (univ.filter (fun b : Balancing.Bits dataWidth => c = recv b.1)).card ≤ M) →
        PackedLabelBudget N cell recv dataWidth W M (labelCount α a k) := by
  filter_upwards [eventually_balancing_slack hα a hgap] with k hk
  intro W M hW hM N cell recv dataWidth hvol hdata hc ha
  exact ⟨hvol, hdata, hc, ha, hk W M hW (Nat.cast_nonneg _) hM⟩

/-- Decode a label code into its base-`d` digits. -/
def decodeProduct (n d : ℕ) (hd : 0 < d) : Fin (d^(n+1)-1+1) ≃ Label (n+1) d :=
  (finCongr (by have := pow_pos hd (n+1); omega)).trans finFunctionFinEquiv.symm

variable [DecidableEq A] [DecidableEq N.Edge]

/-- The integer cell codes output by the public rational label scan. -/
def packedCodes (cs : List Cell) (z : ℕ) : Cell → Fin (z+1) :=
  let bins := Balancing.labelBins (z := z) (crossSrc N cell) (crossDst N cell) recv
    (crossWidth N cell) dataWidth
  Balancing.publicLabels bins (fun j => Balancing.index (bins j)) cs ∅ (fun _ => 0)
    (Balancing.initialMoments bins ∅ (fun _ => 0))

/-- The product labels used to allocate packet intervals for this network. -/
def publicPackedLabel (cs : List Cell) (n d : ℕ) (hd : 0 < d) : Cell → Label (n+1) d :=
  decodeProduct n d hd ∘ packedCodes N cell recv dataWidth cs (d^(n+1)-1)

/-- On the real packed network the public product labels simultaneously balance
every ordered cable bin and every incoming data bin. -/
theorem publicPackedLoads (cs : List Cell) (hcs : cs.toFinset = univ) (n d : ℕ) (hd : 0 < d)
    {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1))) :
    let label := publicPackedLabel N cell recv dataWidth cs n d hd
    (∀ u v, Balancing.load (Balancing.cable (fun b : LiveBit N cell => crossSrc N cell b.1)
      (fun b : LiveBit N cell => crossDst N cell b.1) u v) label ≤ 4*W/(d^(n+1) : ℕ)^2) ∧
    ∀ u, Balancing.load (Balancing.datum (fun b : Balancing.Bits dataWidth => recv b.1) u)
      label ≤ 4*W/(d^(n+1) : ℕ) := by
  let Z := d^(n+1)
  let z := Z-1
  have hZ : 0 < Z := pow_pos hd _
  have hz : z+1 = Z := by dsimp only [z]; omega
  have hzR : (z : ℝ)+1 = Z := by exact_mod_cast hz
  have hnum := h.variance
  change (Z : ℝ)^2 * (4*W*M) + Z*(W*M) ≤ (W/(Z : ℝ)^2)^2 at hnum
  rw [← hzR] at hnum
  obtain ⟨hc,ha⟩ := Balancing.public_labels_balanced (z := z) (crossSrc N cell) (crossDst N cell)
    recv (crossWidth N cell) dataWidth cs hcs W M (fun e => e.property)
    h.cableVolume h.dataVolume h.cableIncidence h.dataIncidence hnum
  rw [hzR] at hc ha
  refine ⟨balanced_decode (decodeProduct n d hd) (crossSrc N cell) (crossDst N cell)
    (crossWidth N cell) (packedCodes N cell recv dataWidth cs z) (fun e => e.property) _ hc, ?_⟩
  intro u
  have hx := ha ((decodeProduct n d hd).symm u)
  simpa only [Balancing.load, Balancing.datum, Balancing.hit, mem_singleton, forall_eq,
    publicPackedLabel, Function.comp_apply, ← Equiv.eq_symm_apply, packedCodes, z, Z] using hx

/-- The actual crossing bits embed into the rounded common block capacity using
the deterministically selected labels. -/
noncomputable def publicPackedEmbedding (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (hcs : cs.toFinset = univ) (n d : ℕ) (hd : 0 < d) {bc : ℕ} (hb : 0 < bc)
    {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1))) :
    LiveBit N cell ↪ Slot n d (blocksFor W bc (d^(n+1))) bc :=
  balancedPackedEmbedding N cell ord (publicPackedLabel N cell recv dataWidth cs n d hd)
    ((Nat.cast_nonneg _).trans h.dataVolume) hb (pow_pos hd _) (publicPackedLoads N cell recv dataWidth
      cs hcs n d hd h).1

/-- A real crossing bit is placed in the bin of its two public labels, at its
within-edge ordinal after the widths of preceding edges in the same bin. -/
theorem publicPackedEmbedding_address (ord : N.CrossingEdge cell ≃ Fin m)
    (cs : List Cell) (hcs : cs.toFinset = univ) (n d : ℕ) (hd : 0 < d) {bc : ℕ} (hb : 0 < bc)
    {W : ℝ} {M : ℕ} (h : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let label := publicPackedLabel N cell recv dataWidth cs n d hd
    let s := publicPackedEmbedding N cell recv dataWidth ord cs hcs n d hd hb h ⟨e,j⟩
    s.1 = (label (crossSrc N cell e), label (crossDst N cell e)) ∧
      s.2.val = intervalStart (cablePair ord (crossSrc N cell) (crossDst N cell) label)
        (crossWidth N cell ∘ ord.symm) (ord e) + j.val := by
  exact packedSlot_address N cell ord _ _ _ _ e j

end Cube.Physical

end BorderVNP
end Computability
end OAI
