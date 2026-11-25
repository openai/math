import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix
import OAI.LinearAlgebra.MatrixExponent.Packing.Occupancy
import OAI.LinearAlgebra.MatrixExponent.Packing.Projection
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Packing.HostReset

/-!
# Packing and matching one dyadic group

Represent a colony by its host and dyadic interval. Each unit wire keeps
its block index, while its two hosts determine its two colonies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset
open scoped Classical

variable {V : Type} [Fintype V] {h : ℕ}

namespace Grouping
variable {N C : V → Finset V} {Δ D k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l)

local instance : DecidableEq g.Colony := Classical.typeDecidableEq _

variable {E : Type} [Fintype E] (src dst : E → V) (ix : E → Cell h)

theorem outgoing (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ v x, u * (univ.filter fun e => src e = v ∧ ix e = x).card ≤ l v x)
    (p : g.Colony) (x : Cell h) :
    u * (univ.filter fun e => g.ends src ix e = p ∧ ix e = x).card ≤ l p.1 x := by
  refine le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card ?_)) hu) (hs _ _)
  intro e he
  obtain ⟨_, hp, hx⟩ := mem_filter.mp he
  exact mem_filter.mpr ⟨mem_univ _, congrArg Sigma.fst hp, hx⟩

theorem destinations (hd : ∀ e, dst e ∈ C (src e)) (p : g.Colony) :
    ((univ.filter fun e => g.ends src ix e = p).image (g.ends dst ix)).card ≤ coreBins Δ := by
  apply le_trans _ (g.bins p.1 p.2.val p.2.property)
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun q : g.Colony => ⟨q.1, q.2.val⟩)
  · intro q hq
    obtain ⟨e, he, rfl⟩ := mem_image.mp hq
    rw [← (mem_filter.mp he).2]
    exact mem_sigma.mpr ⟨hd e, mem_image.mpr ⟨ix e, mem_filter.mpr ⟨mem_univ _, rfl⟩, rfl⟩⟩
  · rintro ⟨v, a⟩ _ ⟨w, b⟩ _ eq
    obtain ⟨rfl, hab⟩ := Sigma.mk.inj eq
    have he : a = b := Subtype.ext (eq_of_heq hab)
    cases he
    rfl

theorem card_bound :
    (Fintype.card g.Colony : ℝ) ≤
      Fintype.card V + 16 * (∑ v, ∑ x, l v x) / ((2 : ℝ) ^ k * B) := by
  simpa only [Colony, Fintype.card_sigma, Fintype.card_coe, Nat.cast_sum] using g.total

end Grouping

/-- Pay for all core bins out of the total load and one allowance per host. -/
theorem bin_charge {B S K P H L X Z σ : ℝ}
    (hb : 0 < B) (hs : 0 < S) (hp : 0 ≤ P) (hz : 0 ≤ Z) (hσ : 0 ≤ σ)
    (hk : 256 * (K + 1) ≤ S) (hh : S * B * H ≤ σ)
    (hl : L ≤ 2 * (X + Z)) (hc : P ≤ H + 16 * L / (S * B)) :
    B * (K + 1) * P ≤ X / 8 + (Z + σ) := by
  have h₁ := mul_le_mul_of_nonneg_right hk (mul_nonneg hb.le hp)
  have h₂ := (le_div_iff₀ (mul_pos hs hb)).mp (sub_le_iff_le_add'.mpr hc)
  linarith

/-- A packing together with a compatible matching that internalizes at least
a quarter of the core width, less the tether and host allowances. -/
theorem pack_subround {E : Type} [Fintype E] {k : ℕ}
    (N C : V → Finset V) (Δ D : ℕ) (hΔ : 0 < Δ) (hD : 0 < D)
    (eSym : ∀ v u, u ∈ N v → v ∈ N u) (cSym : ∀ v u, u ∈ C v → v ∈ C u)
    (sub : ∀ v, C v ⊆ N v) (eDeg : ∀ v, (N v).card ≤ D) (cDeg : ∀ v, (C v).card ≤ Δ)
    (hk : 1 ≤ k) (hkh : k ≤ h) (B : ℝ) (hB : 0 < B)
    (l : V → Cell h → ℝ) (hl : ∀ v x, 0 ≤ l v x ∧ l v x ≤ B)
    (src dst : E → V) (ix : E → Cell h) (u Z σ : ℝ) (hu : 0 < u) (hZ : 0 ≤ Z)
    (hs : ∀ v x, u * (univ.filter fun e => src e = v ∧ ix e = x).card ≤ l v x)
    (hd : ∀ e, dst e ∈ C (src e))
    (hbins : 256 * (coreBins Δ + 1) ≤ 2 ^ k)
    (hhosts : (2 : ℝ) ^ k * B * Fintype.card V ≤ σ)
    (hload : (∑ v, ∑ x, l v x) ≤ 2 * (u * Fintype.card E + Z)) :
    ∃ (g : Grouping N C Δ D k B l) (m : Matching (g.ends src ix) (g.ends dst ix) ix),
      u * Fintype.card E / 4 - (Z + σ) ≤ u * m.count := by
  obtain ⟨g⟩ := pack_group N C Δ D hΔ hD eSym cSym sub eDeg cDeg hk hkh B hB l hl
  obtain ⟨m, hm⟩ := subround (g.ends src ix) (g.ends dst ix) ix u B (coreBins Δ) hu hB.le
    (fun p x => (g.outgoing src ix u hu.le hs p x).trans (hl p.1 x).2)
    (g.destinations src dst ix hd)
  have hb : (256 : ℝ) * (coreBins Δ + 1) ≤ 2 ^ k := by exact_mod_cast hbins
  have hσ : 0 ≤ σ := le_trans (by positivity) hhosts
  have hc := bin_charge hB (by positivity) (Nat.cast_nonneg _) hZ hσ hb hhosts hload g.card_bound
  exact ⟨g, m, by linarith only [hc, hm]⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Charging the incidences of replacement wires

Each gadget has fewer than `4*b` wires. Both ends of every wire are
charged to one of its four original endpoints. The matched pairs use
disjoint sets of original wires.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Finset Spectral.Tensor
open scoped Classical

variable {V E : Type} [Fintype E]

private def weight (v x : V) : ℕ := if x = v then 1 else 0

namespace Grouping

variable [Fintype V] {N C : V → Finset V} {Δ D h k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

def oldContact (col : Bool) (e : E) :=
  (g.route m col (src e) (ix e), g.route m col (dst e) (ix e))

theorem contact_degree (b : ℕ) (f : m.items → Fin 8 → ℕ)
    (hf : ∀ e, ∑ j, f e j < 4 * b) (col : Bool) (z : Site V h) :
    degree (g.contact (b := b) (f := f) m col) z ≤ 8 * b * degree (g.oldContact m col) z := by
  let old e := arityCost z (g.oldContact m col e)
  let new (s : m.replaced b f) := arityCost z (g.contact m col s)
  let wt := weight z
  let mass e := old (m.mate e) + old e.val
  have one (e : m.items) (i : Fin 6) : wt (g.party m col e i) ≤ mass e := by
    have a : wt (g.party m col e 0) + wt (g.party m col e 1) +
        (wt (g.party m col e 2) + wt (g.party m col e 3)) = mass e := rfl
    have h₀ : wt (g.party m col e 0) ≤ mass e := by omega
    have h₁ : wt (g.party m col e 1) ≤ mass e := by omega
    have h₂ : wt (g.party m col e 2) ≤ mass e := by omega
    have h₃ : wt (g.party m col e 3) ≤ mass e := by omega
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
    · cases col <;> assumption
    · cases col <;> assumption
  have gadget (e : m.items) :
      (∑ j, ∑ i : Fin (f e j), new (.inl ⟨e, j, i⟩)) ≤ 8 * b * mass e := calc
    _ ≤ ∑ j, ∑ _i : Fin (f e j), (mass e + mass e) :=
      sum_le_sum fun j _ => sum_le_sum fun i _ =>
        Nat.add_le_add (one e (sixPair j).1) (one e (sixPair j).2)
    _ = (∑ j, f e j) * (mass e + mass e) := by simp [sum_mul]
    _ ≤ 4 * b * (mass e + mass e) := Nat.mul_le_mul_right _ (hf e).le
    _ = 8 * b * mass e := by ring
  have unpaired (e : m.unpaired) : (∑ i : Fin b, new (.inr (e, i))) ≤ 8 * b * old e.val := by
    change (∑ _i : Fin b, old e.val) ≤ _
    simpa using Nat.mul_le_mul_right (old e.val) (show b ≤ 8 * b by omega)
  have split : (∑ e, old e) = (∑ e, mass e) + ∑ e : m.unpaired, old e.val := by
    rw [← Equiv.sum_comp m.partition, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    rfl
  rw [degree_sum, degree_sum]
  change (∑ e, new e) ≤ 8 * b * (∑ e, old e)
  rw [split, mul_add, mul_sum, mul_sum, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sigma]
  exact Nat.add_le_add (sum_le_sum fun e _ => gadget e) (sum_le_sum fun e _ => unpaired e)

/-- Each new wire has width `u / b`. Both endpoints count toward the load,
including two incidences at a common site when the wire is a loop. -/
theorem contact_load (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (hl : ∀ v x, 0 ≤ l v x) (hB : 0 ≤ B)
    (b : ℕ) (hb : 0 < b) (f : m.items → Fin 8 → ℕ) (hf : ∀ e, ∑ j, f e j < 4 * b)
    (u : ℝ) (hu : 0 < u)
    (hload : ∀ t : V × Cell h,
      u * degree (fun e => ((src e, ix e), (dst e, ix e))) t ≤ l t.1 t.2)
    (col : Bool) (z : Site V h) :
    u / b * degree (g.contact (b := b) (f := f) m col) z ≤
      8 * (near C Δ z).card * ((2 : ℝ) ^ k * B) := by
  let pair (e : E) := ((src e, ix e), (dst e, ix e))
  let r (t : V × Cell h) := g.route m col t.1 t.2
  have hold : u * degree (g.oldContact m col) z ≤ (near C Δ z).card * ((2 : ℝ) ^ k * B) := by
    refine le_trans ?_ (g.route_load m cs sub hedge hl hB col z)
    change u * degree (fun e => Prod.map r r (pair e)) z ≤ _
    rw [degree_map, Nat.cast_sum, mul_sum]
    apply sum_le_sum
    intro t _
    by_cases htz : g.route m col t.1 t.2 = z
    · simpa only [r, ite_eq_left htz] using hload t
    · simp [r, htz]
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  calc
    _ ≤ u / b * (8 * b * degree (g.oldContact m col) z) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hu.le hb'.le)
      exact_mod_cast g.contact_degree m b f hf col z
    _ = 8 * (u * degree (g.oldContact m col) z) := by
      rw [← mul_assoc, mul_left_comm (u / _), div_mul_cancel₀ _ hb'.ne', mul_assoc]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hold (by norm_num : (0 : ℝ) ≤ 8)

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Choosing the cheaper contraction before identifying any endpoints

The profile alone gives two complementary upper bounds on the number
of crossings. Their comparison does not inspect the actual diagram.
Additional coincidences of endpoints can only reduce the chosen cost.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open Finset
open scoped Classical

def profileScore (c : Bool) (f : Fin 8 → ℕ) :=
  ∑ j, if c = decide (4 ≤ j.val) then 0 else f j

theorem score_sum (f : Fin 8 → ℕ) :
    profileScore true f + profileScore false f = ∑ j, f j := by
  unfold profileScore
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  cases decide (4 ≤ j.val) <;> simp

def side {I : Type} [Fintype I] (f : I → Fin 8 → ℕ) : Bool :=
  decide ((∑ i, profileScore true (f i)) < ∑ i, profileScore false (f i))

private theorem side_bound {I : Type} [Fintype I] (f : I → Fin 8 → ℕ) :
    2 * (∑ i, profileScore (side f) (f i)) ≤ ∑ i, ∑ j, f i j := by
  simp_rw [← score_sum, sum_add_distrib]
  unfold side
  by_cases h : (∑ i, profileScore true (f i)) < ∑ i, profileScore false (f i)
  · rw [decide_eq_true h]; omega
  · rw [decide_eq_false h]; omega

namespace Grouping

variable {V E : Type} [Fintype V] [Fintype E] {N C : V → Finset V} {Δ D h k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

theorem cross_side (b : ℕ) (f : m.items → Fin 8 → ℕ) (hf : ∀ e, ∑ j, f e j < 4 * b) :
    2 * Fintype.card {e : m.replaced b f //
      (g.contact m (side f) e).1 ≠ (g.contact m (side f) e).2} + m.count ≤
      2 * b * Fintype.card E := by
  let col := side f
  let cost (e : m.replaced b f) : ℕ :=
    if (g.contact m col e).1 ≠ (g.contact m col e).2 then 1 else 0
  have unit (e : m.replaced b f) : cost e ≤ 1 := by
    unfold cost
    split_ifs <;> omega
  have first (e : m.items) (j : Fin 8) :
      (∑ t : Fin (f e j), cost (.inl ⟨e, j, t⟩)) ≤
        if col = decide (4 ≤ j.val) then 0 else f e j := by
    split_ifs with hc
    · have he := g.party_closed m e j
      rw [← hc] at he
      have hz (t : Fin (f e j)) : cost (.inl ⟨e, j, t⟩) = 0 := ite_eq_right (not_not.mpr he)
      simp only [hz, sum_const_zero, le_refl]
    · simpa using sum_le_sum (s := univ) (fun t _ => unit (.inl ⟨e, j, t⟩))
  have bound : ∑ e, cost e ≤ (∑ e, profileScore col (f e)) + Fintype.card m.unpaired * b := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp_rw [Fintype.sum_sigma]
    apply Nat.add_le_add
    · exact sum_le_sum fun e _ => sum_le_sum fun j _ => first e j
    · simpa using sum_le_sum (s := univ) (fun e _ => unit (.inr e))
  have total : (∑ e, ∑ j, f e j) + m.count ≤ m.count * (4 * b) := by
    have h := sum_le_sum (s := univ) (fun e _ => Nat.succ_le_of_lt (hf e))
    simpa only [Nat.succ_eq_add_one, sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul,
      mul_one, m.card_items] using h
  rw [Fintype.card_subtype, card_filter]
  change 2 * (∑ e, cost e) + m.count ≤ _
  have hc := side_bound f
  change 2 * (∑ e, profileScore col (f e)) ≤ _ at hc
  calc
    _ ≤ m.count * (4 * b) + 2 * (Fintype.card m.unpaired * b) := by omega
    _ = _ := by rw [← m.card_partition]; ring

theorem cross_bound (b : ℕ) (f : m.items → Fin 8 → ℕ) (hf : ∀ e, ∑ j, f e j < 4 * b) :
    ∃ col, 2 * Fintype.card {e : m.replaced b f // (g.contact m col e).1 ≠ (g.contact m col e).2}
      + m.count ≤ 2 * b * Fintype.card E :=
  ⟨side f, g.cross_side m b f hf⟩

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Simultaneous replacement of matched bundles

Each matched pair uses the same six-site identity, with its own
selector. Unmatched bundles pass through unchanged. The choices of
row or column contractions can be made after expanding this identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Spectral Spectral.Tensor Classical

variable {V E : Type} [Fintype V] [Fintype E] {N C : V → Finset V} {Δ D h k : ℕ}
  {B : ℝ} {l : V → Cell h → ℝ} (g : Grouping N C Δ D k B l)
  {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)

namespace Grouping

abbrev Parties := (Σ _ : m.items, Fin 6) ⊕ (V × Cell h)

def locate (col : Bool) : g.Parties m → Site V h
  | .inl ⟨e, j⟩ => g.party m col e j
  | .inr (v, x) => g.route m col v x

private abbrev Demand (b : ℕ) := (Σ _ : m.items, Fin 2 × Fin b) ⊕ (m.unpaired × Fin b)

private def demandIndex (b : ℕ) : Demand g m b ≃ E × Fin b :=
  (((((Equiv.sigmaEquivProd _ _).trans (Equiv.prodAssoc _ _ _).symm).sumCongr (.refl _)).trans
    (Equiv.sumProdDistrib _ _ _).symm).trans (m.partition.prodCongr (.refl _)))

private def untouched {b : ℕ} (e : m.unpaired × Fin b) : (V × Cell h) × (V × Cell h) :=
  ((src e.1.val, ix e.1.val), (dst e.1.val, ix e.1.val))

private def demand0 {b : ℕ} : Demand g m b → g.Parties m × g.Parties m :=
  Packet.together (Packet.parallelDemand (fun _ e => sixDemandPair e.1)) (untouched g m)

def demand {b : ℕ} : E × Fin b → g.Parties m × g.Parties m :=
  demand0 g m ∘ (demandIndex g m b).symm

theorem locate_demand {b : ℕ} (col : Bool) (e : E × Fin b) :
    Prod.map (g.locate m col) (g.locate m col) (g.demand m e) =
      (g.route m col (src e.1) (ix e.1), g.route m col (dst e.1) (ix e.1)) := by
  obtain ⟨q, rfl⟩ := (demandIndex g m b).surjective e
  rw [demand, Function.comp_apply, Equiv.symm_apply_apply]
  rcases q with ⟨q, j, t⟩|⟨q, t⟩
  · exact congrArg (Prod.map (fun p => g.route m col p.1 p.2)
      (fun p => g.route m col p.1 p.2)) (g.rep_demand m col q j)
  · rfl

abbrev Selector (A : ℕ) (H : Finset (Fin 8 → ℕ)) := m.items → Fin A × ↥H

def profile {A H} (i : g.Selector m A H) (v : m.items) : Fin 8 → ℕ := (i v).2.val

def supplies {b : ℕ} {f : m.items → Fin 8 → ℕ} : m.replaced b f → g.Parties m × g.Parties m
  | .inl ⟨e, j, _⟩ => (.inl ⟨e, (sixPair j).1⟩, .inl ⟨e, (sixPair j).2⟩)
  | .inr t => (.inr (untouched g m t).1, .inr (untouched g m t).2)

omit [Fintype E] in
theorem locate_supply {b : ℕ} {f : m.items → Fin 8 → ℕ} (col : Bool) (e : m.replaced b f) :
    Prod.map (g.locate m col) (g.locate m col) (g.supplies m e) = g.contact m col e := by
  rcases e with ⟨q, j, t⟩|⟨q, t⟩ <;> rfl

private def supplyIndex (b z : ℕ) (f : m.items → Fin 8 → ℕ) :
    (m.replaced b f × Fin z) ≃ m.replaced (b * z) (fun q j => f q j * z) :=
  (Equiv.sumProdDistrib _ _ _).trans <| Equiv.sumCongr
    ((Equiv.sigmaProdDistrib _ _).trans <| Equiv.sigmaCongrRight fun _ =>
      (Equiv.sigmaProdDistrib _ _).trans <| Equiv.sigmaCongrRight fun _ => finProdFinEquiv)
    ((Equiv.prodAssoc _ _ _).trans ((Equiv.refl _).prodCongr finProdFinEquiv))

/-- A profile of each selector counts sub-bundles of width `z`. -/
def wireRule {K : Type} [Field K] {b z A : ℕ} {H : Finset (Fin 8 → ℕ)}
    (P : Packet.Rule K (fun e : Fin 2 × Fin (b * z) => sixDemandPair e.1)
      (fun i : Fin A × ↥H => fun e : Σ j : Fin 8, Fin (i.2.1 j * z) => sixPair e.1)) :
    Packet.Rule K (g.demand (b := b * z) m)
      (fun i : g.Selector m A H => fun e : m.replaced b (g.profile m i) × Fin z =>
        g.supplies m e.1) := by
  let all := (Packet.Rule.parallel (fun _ : m.items => P)).keep (untouched g m (b := b * z))
  let old := all.reindex (demandIndex g m (b * z)).symm
  let new := old.supplies_equiv (fun i => supplyIndex g m b z (g.profile m i))
  refine new.congr rfl ?_
  funext i e
  rcases e with ⟨⟨e, j, s⟩|⟨e, s⟩, t⟩ <;> rfl

theorem wireIdentity {K : Type} [Field K] {b z A : ℕ} {H : Finset (Fin 8 → ℕ)}
    (P : Packet K (fun e : Fin 2 × Fin (b * z) => sixDemandPair e.1)
      (fun i : Fin A × ↥H => fun e : Σ j : Fin 8, Fin (i.2.1 j * z) => sixPair e.1)) :
    Packet K (g.demand (b := b * z) m)
      (fun i : g.Selector m A H => fun e : m.replaced b (g.profile m i) × Fin z =>
        g.supplies m e.1) :=
  (g.wireRule m P.rule).packet

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Contracting a matched subround

On the core diagram, tether ends are named exterior wires. The selector
determines which layout to contract. Every surviving bundle still has
exactly `z` bits and the sum of the diagrams is the unmodified tensor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open Spectral Classical

/-- Fixed independently of the subdivision width. -/
structure Gadget (F : Type) [Field F] where
  b : ℕ
  copies : ℕ
  shapes : Finset (Fin 8 → ℕ)
  pos : 0 < b
  cost : ∀ f ∈ shapes, ∑ j, f j < 4 * b
  packet : ∀ z : ℕ, 0 < z →
    Packet F (fun e : Fin 2 × Fin (b * z) => Tensor.sixDemandPair e.1)
      (fun i : Fin copies × ↥shapes => fun e : Σ j : Fin 8, Fin (i.2.1 j * z) => Tensor.sixPair e.1)

theorem gadget_exists (F : Type) [Field F] : Nonempty (Gadget F) :=
  let ⟨b, c, H, hb, hc, h⟩ := Tensor.six_packets F
  ⟨⟨b, c, H, hb, hc, h⟩⟩

variable {F V E : Type} [Field F] [Fintype V] [Fintype E] {a b : Wire}
  {N C : V → Finset V} {Δ D h k : ℕ} {B : ℝ} {l : V → Cell h → ℝ}
  (g : Grouping N C Δ D k B l) {src dst : E → V} {ix : E → Cell h}
  (m : Matching (g.ends src ix) (g.ends dst ix) ix)
  (P : Gadget F) (G : Diagram F a b) (z : ℕ)

namespace Grouping

abbrev Choice := g.Selector m P.copies P.shapes

abbrev Supply (i : g.Choice m P) := m.replaced P.b (g.profile m i)

abbrev Crossing (i : g.Choice m P) (c : Bool) :=
  {e : g.Supply m P i // (g.contact m c e).1 ≠ (g.contact m c e).2}

def layout (i : g.Choice m P) := side (g.profile m i)

abbrev Survivors (i : g.Choice m P) := g.Crossing m P i (g.layout m P i)

def ends' (i : g.Choice m P) (e : g.Survivors m P i) : Site V h × Site V h :=
  g.contact m (g.layout m P i) e.1

variable {G z}
variable (s : Bundles G src dst ix (P.b * z)) (hz : 0 < z)

def assign (i : g.Choice m P) (v : G.V) :=
  g.route m (g.layout m P i) (s.place v).1 (s.place v).2

private def station (i : g.Choice m P) := g.locate m (g.layout m P i)

private theorem aligned :
    G.Aligned (g.assign m P s) (g.station m P) (g.demand m ∘ s.bits) := by
  intro i e
  have := g.locate_demand m (g.layout m P i) (s.bits e)
  simp only [assign, s.left, s.right, station, Function.comp_apply]
  exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩

abbrev expansion := (g.wireRule m (P.packet z hz).rule).reindex s.bits

abbrev contract (i : g.Choice m P) :=
  G.replaced (g.expansion m P s hz) (g.assign m P s) (g.station m P) i

theorem eval_contract (x : Val a) (y : Val b) :
    ∑ i, (g.contract m P s hz i).eval x y = G.eval x y :=
  G.eval_replaced _ _ _ x y

theorem bound_survivors (i : g.Choice m P) :
    2 * Fintype.card (g.Survivors m P i) + m.count ≤ 2 * P.b * Fintype.card E :=
  g.cross_side m P.b (g.profile m i) (fun t => P.cost _ (i t).2.property)

private abbrev SupplyEnd (i : g.Choice m P) (e : g.Supply m P i × Fin z) :=
  g.supplies m e.1

private theorem across (i : g.Choice m P) (e : g.Supply m P i) :
    (g.contact m (g.layout m P i) e).1 ≠ (g.contact m (g.layout m P i) e).2 ↔
      g.station m P i (g.supplies m e).1 ≠ g.station m P i (g.supplies m e).2 := by
  rw [← g.locate_supply m (g.layout m P i)]
  rfl

private def crossingIndex (i : g.Choice m P) :
    g.Survivors m P i × Fin z ≃ Diagram.Cut (W := g.SupplyEnd m P (z := z)) (g.station m P) i where
  toFun e := ⟨(e.1.val, e.2), (g.across m P i _).mp e.1.property⟩
  invFun e := (⟨e.val.1, (g.across m P i _).mpr e.property⟩, e.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

def remaining (i : g.Choice m P) :
    g.Survivors m P i × Fin z ≃ (g.contract m P s hz i).E :=
  (g.crossingIndex m P i).trans
    (G.cutEdges (g.expansion m P s hz) _ _ (g.aligned m P s) i)

theorem contact_contract (i : g.Choice m P) (t : g.Survivors m P i × Fin z) :
    ((g.contract m P s hz i).source (g.remaining m P s hz i t),
     (g.contract m P s hz i).target (g.remaining m P s hz i t)) = g.ends' m P i t.1 :=
  g.locate_supply m (g.layout m P i) t.1.val

/-- The saving counts individual wire bits, even though matching was
performed on whole bundles. -/
theorem width_contract (i : g.Choice m P) :
    2 * Fintype.card (g.contract m P s hz i).E + m.count * z ≤ 2 * Fintype.card G.E := by
  rw [← Fintype.card_congr (g.remaining m P s hz i), Fintype.card_congr s.bits]
  simp only [Fintype.card_prod, Fintype.card_fin]
  have ht := Nat.mul_le_mul_right z (g.bound_survivors m P i)
  rw [add_mul, mul_assoc 2] at ht
  rw [show 2 * P.b * Fintype.card E * z = 2 * (Fintype.card E * (P.b * z)) by ring] at ht
  exact ht

theorem contraction (i : g.Choice m P) {Z : ℝ} (hZ : 0 ≤ Z)
    (matched : (P.b * z : ℕ) * (Fintype.card E : ℝ) / 4 - Z ≤ (P.b * z : ℕ) * (m.count : ℝ)) :
    (Fintype.card (g.contract m P s hz i).E : ℝ) ≤
      (1 - 1 / (8 * (P.b : ℝ))) * Fintype.card G.E + Z := by
  have hw : 2 * (Fintype.card (g.contract m P s hz i).E : ℝ) + m.count * (z : ℝ) ≤
      2 * (Fintype.card G.E : ℝ) := by exact_mod_cast g.width_contract m P s hz i
  have hb : 1 ≤ (P.b : ℝ) := by exact_mod_cast P.pos
  have hn : Fintype.card G.E = Fintype.card E * (P.b * z) := by
    simpa using Fintype.card_congr s.bits
  have hm : (Fintype.card G.E : ℝ) / (8 * (P.b : ℝ)) ≤ m.count * (z : ℝ) / 2 + Z := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [hn]
    push_cast at matched ⊢
    nlinarith only [matched, mul_le_mul_of_nonneg_right hb hZ, hZ]
  rw [sub_mul, one_mul, one_div_mul_eq_div]
  linarith only [hw, hm]

theorem input_contract (i : g.Choice m P) (t : slots a) :
    ((g.contract m P s hz i).src.symm (.inl t)).1 = g.assign m P s i (G.src.symm (.inl t)).1 := rfl

theorem output_contract (i : g.Choice m P) (t : slots b) :
    ((g.contract m P s hz i).dst.symm (.inl t)).1 = g.assign m P s i (G.dst.symm (.inl t)).1 := rfl

theorem arity_contract (i : g.Choice m P) (v : Site V h) :
    (g.contract m P s hz i).arity v ≤ exterior G (g.assign m P s i) v +
      degree (g.contact (b := P.b) (f := g.profile m i) m (g.layout m P i)) v * z := by
  let col := g.layout m P i
  let edge := g.contact (b := P.b) (f := g.profile m i) m col
  let f (e : g.Supply m P i × Fin z) :=
    Prod.map (g.station m P i) (g.station m P i) (g.supplies m e.1)
  have eqn : f = fun e => edge e.1 := funext fun e => g.locate_supply m col e.1
  have ht := G.arity_replaced (g.expansion m P s hz) (g.assign m P s) (g.station m P)
    (g.aligned m P s) i v
  change (g.contract m P s hz i).arity v ≤ exterior G (g.assign m P s i) v + degree f v at ht
  rwa [eqn, degree_bundle] at ht

theorem load_contract (cs : ∀ v w, w ∈ C v → v ∈ C w) (sub : ∀ v, C v ⊆ N v)
    (hedge : ∀ e, dst e ∈ C (src e)) (hl : ∀ v x, 0 ≤ l v x) (hB : 0 ≤ B)
    (hi : ∀ t : V × Cell h,
      (P.b * z : ℕ) * (degree (fun e => ((src e, ix e), (dst e, ix e))) t : ℝ) ≤ l t.1 t.2)
    (he : ∀ t, (exterior G s.place t : ℝ) ≤ l t.1 t.2)
    (i : g.Choice m P) (v : Site V h) :
    ((g.contract m P s hz i).arity v : ℝ) ≤ 9 * (near C Δ v).card * ((2 : ℝ) ^ k * B) := by
  let col := g.layout m P i
  let f (t : V × Cell h) := g.route m col t.1 t.2
  have h₁ : (exterior G (g.assign m P s i) v : ℝ) ≤ (near C Δ v).card * ((2 : ℝ) ^ k * B) := by
    change (exterior G (f ∘ s.place) v : ℝ) ≤ _
    rw [exterior_comp]
    refine le_trans ?_ (g.route_load m cs sub hedge hl hB col v)
    exact Finset.sum_le_sum fun t _ => by split_ifs <;> first | exact he t | exact le_rfl
  have hb : 0 < (P.b : ℝ) := Nat.cast_pos.mpr P.pos
  have h₂ := g.contact_load m cs sub hedge hl hB P.b P.pos (g.profile m i)
    (fun t => P.cost _ (i t).2.property) (P.b * z : ℕ) (Nat.cast_pos.mpr (Nat.mul_pos P.pos hz))
    hi col v
  rw [Nat.cast_mul, mul_div_cancel_left₀ _ hb.ne'] at h₂
  have ht := (Nat.cast_le (α := ℝ)).mpr (g.arity_contract m P s hz i v)
  rw [Nat.cast_add, Nat.cast_mul] at ht
  dsimp only [col] at h₂
  linarith only [ht, h₁, h₂]

end Grouping
end OAI.LinearAlgebra.MatrixExponent.Packing
end

/-!
# Contracting on a projected host

Surviving core bundles have both ends in one group. Reassign tether
ends and frozen charges by the same layout, keeping their names intact.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

open Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {h a z Δ D k : ℕ} {B : ℝ} {P : Gadget F} {G : HostNet F L h (P.b * z)}
  (s : G.Projection Δ D a) (g : Grouping G.N G.C Δ D k B G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix)
  (hz : 0 < z) (hle : Δ ≤ D) (i : g.Choice m P)

private theorem keep (col : Bool) (v : G.V) (t : Cell h) :
    s.frozen (s.place (g.route m col v t)).1 ↔ G.frozen v := by
  rw [s.keep]
  rcases g.route_cases m col v t with he | ⟨e, he, _, _, ht⟩
  · rw [he]; rfl
  · rw [ht, ← he]
    exact iff_of_false (G.core (m.mate e)).2 (G.core e.val).1

private theorem active (col : Bool) (e : m.items) (j : Fin 6) :
    ¬s.frozen (s.place (g.party m col e j)).1 := by
  unfold Grouping.party
  rw [keep]
  obtain ⟨h₁, h₂⟩ := G.core (m.mate e)
  obtain ⟨h₃, h₄⟩ := G.core e.val
  fin_cases j
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · cases col <;> assumption
  · cases col <;> assumption

private theorem surviving (e : g.Survivors m P i) :
    let t := g.ends' m P i e
    (s.place t.1).2 = (s.place t.2).2 ∧ (s.place t.2).1 ∈ s.C (s.place t.1).1 :=
  s.core _ _ (g.contact_mem m G.cs G.sub G.edge _ e.val)

def assignment (p : G.V × Cell h) : s.W × Cell a :=
  s.place (g.route m (g.layout m P i) p.1 p.2)

theorem port_contract (q : slots x ⊕ slots y) :
    s.place (portEnd (g.contract m P G.units hz i) q) =
      assignment s g m i (G.units.place (portEnd G.diagram q)) := by
  cases q <;> rfl

def contracted : HostNet F L a z where
  diagram := g.contract m P G.units hz i
  V := s.W
  E := g.Survivors m P i
  src e := (s.place (g.ends' m P i e).1).1
  dst e := (s.place (g.ends' m P i e).2).1
  ix e := (s.place (g.ends' m P i e).1).2
  units := {
    place := s.place
    bits := (g.remaining m P G.units hz i).symm
    left e := by
      obtain ⟨p, rfl⟩ := (g.remaining m P G.units hz i).surjective e
      rw [Equiv.symm_apply_apply]
      exact congrArg (fun q => s.place q.1) (g.contact_contract m P G.units hz i p)
    right e := by
      obtain ⟨p, rfl⟩ := (g.remaining m P G.units hz i).surjective e
      rw [Equiv.symm_apply_apply, (surviving s g m i p.1).1]
      exact congrArg (fun q => s.place q.2) (g.contact_contract m P G.units hz i p) }
  past := G.carried (assignment s g m i)
  park := assignment s g m i ∘ G.park
  frozen := s.frozen
  N := s.N
  C := s.C
  ns := s.ns
  cs := s.cs
  sub := s.sub
  kept t := (keep s g m _ _ _).mpr (G.kept t)
  core e := by
    change ¬s.frozen (s.place (g.contact m _ e.val).1).1 ∧
      ¬s.frozen (s.place (g.contact m _ e.val).2).1
    rcases e with ⟨⟨e, j, t⟩ | ⟨e, t⟩, _⟩
    · exact ⟨active s g m _ e _, active s g m _ e _⟩
    · exact ⟨mt (keep s g m _ _ _).mp (G.core e.val).1,
        mt (keep s g m _ _ _).mp (G.core e.val).2⟩
  edge e := (surviving s g m i e).2
  tether q := by
    obtain ⟨hc, hi, he⟩ := G.tether q
    dsimp only
    rw [port_contract]
    refine ⟨mt (keep s g m _ _ _).mp hc, ?_⟩
    unfold assignment
    simp only [Function.comp_apply, ← hi]
    exact s.full _ _ (g.contact_full m G.cs G.sub G.edge G.ns hle _ he _)

theorem contracted_X : (contracted s g m hz hle i).X =
    Fintype.card (g.contract m P G.units hz i).E := by
  rw [← Fintype.card_congr (g.remaining m P G.units hz i), Fintype.card_prod, Fintype.card_fin]
  rfl

theorem choice_card :
    Fintype.card (g.Choice m P) ≤ (P.copies * P.shapes.card + 1) ^ (Fintype.card G.E) := by
  have hm : Fintype.card m.items ≤ Fintype.card G.E := Fintype.card_subtype_le _
  change Fintype.card (m.items → Fin P.copies × ↥P.shapes) ≤ _
  rw [Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe]
  exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans (Nat.pow_le_pow_right (by omega) hm)

theorem contracted_load (hB : 0 ≤ B) (p : Site G.V h) :
    (contracted s g m hz hle i).load (s.place p).1 (s.place p).2 ≤
      9 * (near G.C Δ p).card * ((2 : ℝ) ^ k * B) := by
  let Q := contracted s g m hz hle i
  let c := g.layout m P i
  let r := assignment s g m i
  have outside := G.reassign Q r rfl (port_contract s g m hz i) rfl (s.place p)
  have hr : push r (Function.uncurry G.load) (s.place p) ≤
      (near G.C Δ p).card * ((2 : ℝ) ^ k * B) := by
    have he := g.route_load m G.cs G.sub G.edge G.load_nonneg hB c p
    simpa only [push, r, assignment, s.place.injective.eq_iff, c, Function.uncurry_def] using he
  let edge := g.contact (b := P.b) (f := g.profile m i) m c
  let emb : g.Survivors m P i ↪ g.Supply m P i := ⟨Subtype.val, Subtype.val_injective⟩
  have eqn : (Q.pair : g.Survivors m P i → _) =
      fun e => Prod.map s.place s.place ((edge ∘ emb) e) := by
    funext e
    apply Prod.ext
    · rfl
    · exact Prod.ext rfl (surviving s g m i e).1
  have hd : degree Q.pair (s.place p) ≤ degree edge p := by
    rw [eqn]
    change degree (fun e => Prod.map s.place s.place ((edge ∘ emb) e)) (s.place p) ≤ degree edge p
    rw [degree_map (edge ∘ emb) s.place]
    simpa only [s.place.injective.eq_iff, sum_ite_eq', mem_univ, ite_true] using degree_select edge emb p
  have hi (t : G.V × Cell h) : ((P.b * z : ℕ) : ℝ) * degree G.pair t ≤ G.load t.1 t.2 := by
    rw [mul_comm]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load t.1 t.2)
  have ht := g.contact_load m G.cs G.sub G.edge G.load_nonneg hB P.b P.pos (g.profile m i)
    (fun t => P.cost _ (i t).2.property) (P.b * z : ℕ) (Nat.cast_pos.mpr (Nat.mul_pos P.pos hz))
    hi c p
  rw [Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr P.pos.ne')] at ht
  have cost := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hd) (Nat.cast_nonneg z)
  change Q.load _ _ ≤ _
  change z * (degree edge p : ℝ) ≤ _ at ht
  rw [mul_comm (z : ℝ)] at ht
  exact (outside.trans (add_le_add hr (cost.trans ht))).trans_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-!
# Simultaneous contraction of dyadic groups

Treat the group prefix as an extra host coordinate while packing.
Projection then returns that prefix to the block index. The resulting
host bounds are independent of the number of groups.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet

open Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {h u z : ℕ}

omit [Field F] in
theorem outgoing (G : HostNet F L h u) (v : G.V) (i : Cell h) :
    (u : ℝ) * (univ.filter fun e => G.src e = v ∧ G.ix e = i).card ≤ G.load v i := by
  have count : (univ.filter fun e => G.src e = v ∧ G.ix e = i).card ≤ degree G.pair (v, i) := by
    unfold degree
    apply le_trans _ (Nat.le_add_right _ _)
    simp [Fintype.card_subtype, pair]
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr count) (Nat.cast_nonneg _)).trans
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load v i))

omit [Field F] [Fintype T] in
theorem diagram_width (G : HostNet F L h u) : Fintype.card G.diagram.E = G.X := by
  simpa [X] using Fintype.card_congr G.units.bits

theorem projected_bounds (P : Gadget F) (G : HostNet F L h (P.b * z)) (hz : 0 < z)
    (a k Δ D : ℕ) (hΔ : 0 < Δ) (hle : Δ ≤ D) (ah : a ≤ h)
    (B σ : ℝ) (hB : 0 ≤ B) (hσ : 0 ≤ σ) (bounds : G.Bounded Δ D B)
    (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B (G.regroup a ah).load)
    (m : Matching (g.ends (G.regroup a ah).src (G.regroup a ah).ix)
      (g.ends (G.regroup a ah).dst (G.regroup a ah).ix) (G.regroup a ah).ix)
    (matched : (G.X : ℝ) / 4 - (L.Z + σ) ≤ (P.b * z : ℕ) * (m.count : ℝ)) (i : g.Choice m P) :
    let q := contracted (G.project a ah Δ D hle) g m hz hle
    Fintype.card (q i).V ≤ 2 * 2 ^ (h - a) * Fintype.card G.V ∧
        (q i).Bounded ((4 * Δ) ^ 900) ((4 * D) ^ 900) (9 * ((4 * Δ) ^ 300 : ℕ) * ((2 : ℝ) ^ k * B)) ∧
        ((q i).X : ℝ) ≤ (1 - 1 / (8 * (P.b : ℝ))) * G.X + (L.Z + σ) ∧
        G.Preserves (q i) ∧ (q i).mass = G.mass + 2 * G.X ∧ G.Tracks (q i) ((Δ + 1) * 2) := by
  let H := G.regroup a ah
  have hb := G.regroup_bounded a ah bounds
  let s : H.Projection Δ D a := G.project a ah Δ D hle
  let q := contracted s g m hz hle
  refine ⟨Site.card _ _, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨cube_near_card G.C Δ hΔ bounds.1, cube_near_card G.N D (hΔ.trans_le hle) bounds.2.1,
      fun v x => ?_⟩
    obtain ⟨p, he⟩ := s.place.surjective (v, x)
    have ht := contracted_load s g m hz hle i hB p
    rw [he] at ht
    refine ht.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (near_card H.C Δ hΔ hb.1 p)) (by norm_num)
  · have ht := g.contraction m P H.units hz i (add_nonneg L.total_nonneg hσ) (by
      have he : Fintype.card (G.regroup a ah).E = Fintype.card G.E := rfl
      simpa only [X, Nat.cast_mul, he, mul_comm (Fintype.card G.E : ℝ)] using matched)
    erw [H.diagram_width, ← contracted_X s g m hz hle i] at ht
    exact ht
  · refine ⟨assignment s g m i ∘ splitAddr G.V a ah, rfl, port_contract s g m hz i,
      ⟨prefixMap ah, prefixMap_onto ah, ?_⟩,
      Σ d : Fin (h - a + 1), Cell d.val, inferInstance, Equiv.refl _, ?_⟩
    · intro q
      let t := splitAddr G.V a ah q
      have near := g.route_near m H.cs H.sub H.edge (g.layout m P i) t.1 t.2
      exact (split_near G.C Δ near).1.symm
    · intro j
      let t := H.park j
      change (g.route m (g.layout m P i) t.1 t.2).1.1 = _
      rcases g.route_cases m (g.layout m P i) t.1 t.2 with he | ⟨e, he, _⟩
      · rw [he]; rfl
      · exact ((H.core e.val).1 (he.symm ▸ H.kept j)).elim

  · have hc := H.carry_sum (assignment s g m i)
    rw [regroup_mass, regroup_X] at hc
    exact hc
  · let f : (q i).V ≃ G.V × (Σ j : Fin (h - a + 1), Cell j.val) := Equiv.refl _
    refine tracks_of_slots f (fun v => insert v (G.C v)) ?_ ?_ (by norm_num)
      (Site.card _ _) ?_
    · intro u v he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (G.cs _ _ he)
    · exact fun v => (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (bounds.1 v) _)
    · intro j
      let t := H.units.place (portEnd H.diagram j)
      have he := (mem_near _ _ _ _).mp (g.route_near m H.cs H.sub H.edge (g.layout m P i) t.1 t.2)
      unfold tip
      rw [show (q i).units.place (portEnd (q i).diagram j) = _ from port_contract s g m hz i j]
      change (g.route m (g.layout m P i) t.1 t.2).1.1 ∈ insert t.1.1 (G.C t.1.1)
      rcases he with he | he
      · rw [he]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((mem_inGroup _ _ _ _).mp he.1).1

theorem subround (P : Gadget F) (G : HostNet F L h (P.b * z)) (hz : 0 < z)
    (a k Δ D : ℕ) (hΔ : 0 < Δ) (hle : Δ ≤ D) (hk : 1 ≤ k) (ha : a + k ≤ h)
    (B σ : ℝ) (hB : 0 < B) (bounds : G.Bounded Δ D B)
    (hbins : 256 * (coreBins Δ + 1) ≤ 2 ^ k)
    (slack : (2 : ℝ) ^ k * B * (Fintype.card G.V * 2 ^ a : ℕ) ≤ σ) :
    ∃ (I : Type) (_ : Fintype I) (q : I → HostNet F L a z),
      Fintype.card I ≤ (P.copies * P.shapes.card + 1) ^ (Fintype.card G.E) ∧
      (∀ x y, ∑ i, (q i).diagram.eval x y = G.diagram.eval x y) ∧
      ∀ i, Fintype.card (q i).V ≤ 2 * 2 ^ (h - a) * Fintype.card G.V ∧
        (q i).Bounded ((4 * Δ) ^ 900) ((4 * D) ^ 900) (9 * ((4 * Δ) ^ 300 : ℕ) * ((2 : ℝ) ^ k * B)) ∧
        ((q i).X : ℝ) ≤ (1 - 1 / (8 * (P.b : ℝ))) * G.X + (L.Z + σ) ∧
        G.Preserves (q i) ∧ (q i).mass = G.mass + 2 * G.X ∧ G.Tracks (q i) ((Δ + 1) * 2) := by
  have ah : a ≤ h := by omega
  let H := G.regroup a ah
  have hb : H.Bounded Δ D B := G.regroup_bounded a ah bounds
  have hs : (2 : ℝ) ^ k * B * Fintype.card H.V ≤ σ := by
    change (2 : ℝ) ^ k * B * Fintype.card (G.V × Cell a) ≤ σ
    rwa [Fintype.card_prod, card_cell]
  have hm : (∑ v, ∑ i, H.load v i) ≤ 2 * ((P.b * z : ℕ) * (Fintype.card H.E : ℝ) + L.Z) := by
    simpa only [X, Nat.cast_mul, mul_add, mul_comm (Fintype.card H.E : ℝ)] using H.sum_load
  obtain ⟨g, m, matched⟩ := pack_subround H.N H.C Δ D hΔ (hΔ.trans_le hle)
    H.ns H.cs H.sub hb.2.1 hb.1 hk (by omega) B hB H.load
    (fun v i => ⟨H.load_nonneg v i, hb.2.2 v i⟩) H.src H.dst H.ix (P.b * z : ℕ)
    L.Z σ (Nat.cast_pos.mpr (Nat.mul_pos P.pos hz)) L.total_nonneg H.outgoing H.edge
    hbins hs hm
  let s : H.Projection Δ D a := G.project a ah Δ D hle
  let q := contracted s g m hz hle
  refine ⟨g.Choice m P, inferInstance, q, choice_card g m,
    g.eval_contract m P H.units hz, ?_⟩
  apply G.projected_bounds P hz a k Δ D hΔ hle ah B σ hB.le (le_trans (by positivity) hs) bounds g m
  have he : Fintype.card H.E = Fintype.card G.E := rfl
  simp only [he, X, Nat.cast_mul, mul_comm (Fintype.card G.E : ℝ)] at matched ⊢
  exact matched

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-! # Transporting a contraction and a reset to a larger field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing
open HostNet

variable {F : Type} [Field F]

/-- Extend the local factors of a packet along a field homomorphism.
The supply graph and selector set are unchanged. -/
private theorem map_packet {S E I K : Type} {J : I → Type}
    [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)] [Field K]
    {D : E → S × S} {W : (i : I) → J i → S × S}
    (f : F →+* K) (h : Spectral.Packet F D W) : Spectral.Packet K D W := by
  classical
  obtain ⟨a, hl, he⟩ := h
  refine ⟨fun i v x y z => f (a i v x y z),
    fun i v x y z x' y' z' hx hy hz => congrArg f (hl i v x y z x' y' z' hx hy hz), ?_⟩
  intro x y
  simpa only [apply_ite, map_one, map_zero, map_sum, map_prod] using congrArg f (he x y)

abbrev Gadget.extend (P : Gadget F) (K : Type) [Field K] [Algebra F K] : Gadget K :=
  ⟨P.b, P.copies, P.shapes, P.pos, P.cost, fun z h => map_packet (algebraMap F K) (P.packet z h)⟩

abbrev Rotor.extend {Y w : ℕ} (R : Rotor F Y w) (K : Type) [Field K] [Algebra F K] :
    Rotor K Y w :=
  ⟨R.V, R.E, R.pos, R.degree, fun σ => map_packet (algebraMap F K) (R.packet σ)⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end
