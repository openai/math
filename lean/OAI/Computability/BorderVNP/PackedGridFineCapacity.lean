import OAI.Computability.BorderVNP.PackedGridBoxBudget
import OAI.Computability.BorderVNP.PackedGridSlotBounds

/-! # Public per-copy capacity for the initial site's private bank

Each guessed internal or supplied crossing wire has at least one real endpoint at
the cell. A supplied external bit has its own attached vertex. Their combined compact
length is at most three times the number of retained trivalent vertices. Public block
capacities and the fixed route congestion bound therefore suffice for every copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing CellAddresses Finset
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _ => 1))
variable {C : Type} (cell : N.Site → C) (c : C)

private abbrev Endpoint := P ⊕ N.Edge × Bool

private def endpoint : Endpoint N → N.Site :=
  Sum.elim N.attach (fun eb => if eb.2 then N.dst eb.1 else N.src eb.1)

private noncomputable def endpointAt :
    N.InsideEdge cell c ⊕ Supplied N cell c → {e : Endpoint N // cell (endpoint N e) = c}
  | .inl e => ⟨.inr (e.val,false),e.property.1⟩
  | .inr (.inl e) =>
    if hs : cell (N.src e.val.val) = c then ⟨.inr (e.val.val,false),hs⟩
    else ⟨.inr (e.val.val,true),e.property.resolve_left hs⟩
  | .inr (.inr p) => ⟨.inl p.val,p.property⟩

omit [Fintype P] in
private theorem endpointAt_inj : Function.Injective (endpointAt N cell c) := by
  let key : Endpoint N → P ⊕ N.Edge := Sum.elim Sum.inl (fun e => Sum.inr e.1)
  have hk (z : N.InsideEdge cell c ⊕ Supplied N cell c) :
      key (endpointAt N cell c z).val = (match z with
        | .inl e => .inr e.val
        | .inr (.inl e) => .inr e.val.val
        | .inr (.inr p) => .inl p.val) := by
    rcases z with z | (z | z)
    · rfl
    · by_cases hs : cell (N.src z.val.val) = c <;> simp [endpointAt,hs,key]
    · rfl
  rintro (a | (a | a)) (b | (b | b)) h <;> have he := congrArg (key ∘ Subtype.val) h <;>
    simp only [Function.comp_apply,hk,Sum.inr.injEq,Sum.inl.injEq,reduceCtorEq] at he ⊢
  · exact Subtype.ext he
  · exact False.elim (b.val.property (he ▸ a.property.1.trans a.property.2.symm))
  · exact False.elim (a.val.property (he.symm ▸ b.property.1.trans b.property.2.symm))
  · exact Subtype.ext (Subtype.ext he)
  · exact Subtype.ext he

/-- The fine cell bank stores each guessed and supplied bit at most once per actual
incident endpoint. Thus every trivalent routed cell fits into three words per fine site. -/
theorem stride_le_sites (tri : N.Trivalent) :
    GridBoxes.stride N cell c ≤ 3 * Fintype.card {v : N.Site // cell v = c} := by
  let S := univ.filter fun v => cell v = c
  have hu (p : Supplied N cell c) : suppliedWidth N cell c p = 1 := by
    rcases p with e | p
    · exact tri.1 _
    · rfl
  have hsize : GridBoxes.stride N cell c = Fintype.card (N.InsideEdge cell c ⊕ Supplied N cell c) := by
    simp only [GridBoxes.stride,guessedSize,suppliedSize,tri.1,hu,sum_const,card_univ,nsmul_eq_mul,
      mul_one,Fintype.card_sum,Nat.cast_id]
  rw [hsize]
  apply (Fintype.card_le_of_injective _ (endpointAt_inj N cell c)).trans
  have hf := sum_card_fiberwise_eq_card_filter (univ : Finset (Endpoint N)) S (endpoint N)
  simp only [S,mem_filter,mem_univ,true_and] at hf
  rw [Fintype.card_subtype,← hf]
  have hdeg (v : N.Site) : (univ.filter fun e => endpoint N e = v).card ≤ 3 := tri.2 v
  calc
    _ ≤ ∑ _v ∈ S, 3 := sum_le_sum fun v _ => hdeg v
    _ = _ := by simp [S,Fintype.card_subtype,Nat.mul_comm]

variable {G J : Type} [Group G] [Fintype G] {step : J → G} {invStep : ∀ j, ∃ i, step i = (step j)⁻¹}
    {n : ℕ} (input : P ≃ Fin n) (inject : Function.Injective N.attach)
    (order : Fin (Fintype.card G) ≃ G) (slots : ℕ) (fit : n ≤ slots) {s h : ℕ}
    (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (r : Routed N (N.slotPlace input inject order slots fit) step invStep
      (endpointBudget slots s (Fintype.card G)) h)

/-- Uniform public upper bound on the number of actual retained vertices, also an
upper bound on the number of named unary positions in this one-copy cell. -/
def siteCapacity (V slots s h : ℕ) := blockWidth slots V + blockWidth s V +
  (8*(endpointBudget slots s V)*(h+1) + Nat.clog 2 V)

omit [Fintype P] in
/-- Ordered initial placement and all private route choices meet the same integral cap. -/
theorem routed_capacity (hv : Fintype.card N.Site ≤ s) (g : G) :
    Fintype.card {v : (N.subdivide (wireRoutes position r)).Site // GridPlacement.cell position r v = g} ≤
      siteCapacity (Fintype.card G) slots s h := by
  rw [routed_site_count]
  apply Nat.add_le_add (occupancy_slots N input inject order slots fit hv g) (r.visits g)

/-- The complete live per-copy bank fits in this public capacity before private staging
or reported-use suffixes are attached. -/
theorem routed_stride (tri : N.Trivalent) (hv : Fintype.card N.Site ≤ s) (g : G) :
    GridBoxes.stride (N.subdivide (wireRoutes position r)) (GridPlacement.cell position r) g ≤
      3*siteCapacity (Fintype.card G) slots s h :=
  (stride_le_sites _ _ g (N.trivalent_subdivide tri _)).trans (Nat.mul_le_mul_left 3
    (routed_capacity N input inject order slots fit position r hv g))

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
