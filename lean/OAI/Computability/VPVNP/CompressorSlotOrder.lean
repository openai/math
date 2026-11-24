import OAI.Computability.VPVNP.CompressorSlotAddresses

/-!
# Ordering actual compressor arc records at each endpoint

In a single endpoint fiber the high-order relative key already distinguishes
all genuine arcs. Hence adding the absolute lane as a low-order address digit
preserves their order. The padding records come afterwards, in dummy-number
order at the unique dummy source for this fiber.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Slots

open Compression Compression.PackingData Compression.SurvivingSlots

variable {V H Tag L : Type*} {d c N J nL pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- The orientation bit selects the outgoing (false) or incoming (true) role. -/
def endRole (layout side : Bool) : Fin 4 → PackedRole :=
  if side then targetRole layout else sourceRole layout

/-- From the source site of a dummy, recover its site at the selected end. -/
def dummyEnd (side : Bool) : Equiv.Perm (Site V Tag L) :=
  if side then
    (Equiv.prodAssoc V Tag L).symm.trans
      (((cycleTags tags).prodCongr (Equiv.refl L)).trans (Equiv.prodAssoc V Tag L))
  else Equiv.refl _

/-- The actual endpoint used as the owner of an arc record's field. -/
def actualEnd (layout side : Bool) : ActualId P subdiv pad → Site V Tag L :=
  Sum.elim (endpoint (P.survivingRole layout) (endRole layout side))
    (fun x ↦ dummyEnd tags side x.1)

/-- Base identifier used by the regularized slot permutation. -/
def paddedBaseId : ActualId P subdiv pad → PaddedId (V × Tag) (Id P.BaseMotif subdiv) pad :=
  Sum.map (baseId P subdiv) (fun x ↦ (packedBase x.1, x.2))

private theorem genuine_lt_dummy (i : Id P.Motif subdiv) (x : Site V Tag L × Fin pad) :
    arcAddress P subdiv vertices tags lanes pad (.inl i) < arcAddress P subdiv vertices tags lanes pad (.inr x) := by
  let a := finProdFinEquiv (relativeKey P subdiv vertices tags i, lanes (P.sourceLane i.2.1))
  let s := finProdFinEquiv (vertices x.1.1, finProdFinEquiv (tags x.1.2.1, lanes x.1.2.2))
  change a.val < keyCount N J d c subdiv * nL + (finProdFinEquiv (s, x.2)).val
  exact a.isLt.trans_le (Nat.le_add_right _ _)

private theorem dummy_lt_dummy (s : Site V Tag L) (a b : Fin pad) :
    arcAddress P subdiv vertices tags lanes pad (.inr (s,a)) <
      arcAddress P subdiv vertices tags lanes pad (.inr (s,b)) ↔ a < b := by
  let site := finProdFinEquiv (vertices s.1, finProdFinEquiv (tags s.2.1, lanes s.2.2))
  change keyCount N J d c subdiv * nL + (a.val + pad * site.val) <
    keyCount N J d c subdiv * nL + (b.val + pad * site.val) ↔ a.val < b.val
  omega

/-- The absolute-address comparison in one genuine endpoint fiber is exactly
the comparison of the two relative keys used by the base slot numbering. -/
theorem address_lt_iff_relative (layout : Bool) (pick : Fin 4 → PackedRole)
    {i j : Id P.Motif subdiv} (h : endpoint (P.survivingRole layout) pick i =
      endpoint (P.survivingRole layout) pick j) :
    arcAddress P subdiv vertices tags lanes pad (.inl i) < arcAddress P subdiv vertices tags lanes pad (.inl j) ↔
      relativeKey P subdiv vertices tags i < relativeKey P subdiv vertices tags j := by
  let addr (x : Id P.Motif subdiv) := (arcAddress P subdiv vertices tags lanes pad (.inl x)).val
  let key (x : Id P.Motif subdiv) := (relativeKey P subdiv vertices tags x).val
  have quotient (x : Id P.Motif subdiv) : addr x / nL = key x :=
    address_div_lane P subdiv vertices tags lanes pad x
  have monotone (x y : Id P.Motif subdiv) (ha : addr x ≤ addr y) : key x ≤ key y := by
    rw [← quotient, ← quotient]
    exact Nat.div_le_div_right ha
  constructor
  · intro ha
    refine lt_of_le_of_ne (monotone _ _ ha.le) ?_
    intro hk
    have hb : baseId P subdiv i = baseId P subdiv j := P.slotIdentifier_injective vertices tags subdiv hk
    let f := incidentBaseEquiv P subdiv layout pick (endpoint (P.survivingRole layout) pick j)
    have he : i = j := congrArg Subtype.val (f.injective
      (show f ⟨i, h⟩ = f ⟨j, rfl⟩ from Subtype.ext hb))
    exact (ne_of_lt ha) (congrArg (fun x ↦ arcAddress P subdiv vertices tags lanes pad (.inl x)) he)
  · intro hk
    exact lt_of_not_ge (fun ha ↦ (not_le_of_gt hk) (monotone _ _ ha))

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

private theorem genuineEnd_card (hc : 2 ≤ c) (layout side : Bool) (s : Site V Tag L) :
    Fintype.card {i : Id P.Motif subdiv // endpoint (P.survivingRole layout) (endRole layout side) i = s} =
      survivingDegree d c subdiv := by
  cases side
  · exact (P.survivingSlot_degree hc layout subdiv s).1
  · exact (P.survivingSlot_degree hc layout subdiv s).2

private def dummyFiberEquiv (side : Bool) (s : Site V Tag L) :
    {x : Site V Tag L × Fin pad // dummyEnd tags side x.1 = s} ≃ Fin pad where
  toFun x := x.1.2
  invFun j := ⟨((dummyEnd tags side).symm s, j), (dummyEnd tags side).apply_symm_apply _⟩
  left_inv x := Subtype.ext (Prod.ext ((dummyEnd tags side).symm_apply_eq.mpr x.2.symm) rfl)
  right_inv _ := rfl

/-- Every actual endpoint has all the surviving slots and every padding slot. -/
theorem actualEnd_card (hc : 2 ≤ c) (layout side : Bool) (s : Site V Tag L) :
    Fintype.card {i : ActualId P subdiv pad // actualEnd P subdiv tags layout side i = s} =
      survivingDegree d c subdiv + pad := by
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  exact congrArg₂ (· + ·) (genuineEnd_card P subdiv hc layout side s)
    ((Fintype.card_congr (dummyFiberEquiv tags side (pad := pad) s)).trans (Fintype.card_fin pad))

/-- A zero-based position within the endpoint row obtained by scanning the
entire numeric address space. -/
abbrev addressRank (layout side : Bool) (i : ActualId P subdiv pad) :=
  Fintype.card {j : ActualId P subdiv pad //
    actualEnd P subdiv tags layout side j = actualEnd P subdiv tags layout side i ∧
    arcAddress P subdiv vertices tags lanes pad j < arcAddress P subdiv vertices tags lanes pad i}

private theorem addressRank_genuine (layout side : Bool) (i : Id P.Motif subdiv)
    (r : IncidentRow (endpoint (P.survivingRole layout) (endRole layout side))
      (endpoint (P.survivingRole layout) (endRole layout side) i)) :
    addressRank P subdiv vertices tags lanes layout side (pad := pad) (.inl i) =
      rowRank P subdiv vertices tags i r.ids := by
  classical
  let A := arcAddress P subdiv vertices tags lanes pad
  let ep := actualEnd P subdiv tags layout side (pad := pad)
  have empty : IsEmpty {x : Site V Tag L × Fin pad //
      ep (.inr x) = ep (.inl i) ∧ A (.inr x) < A (.inl i)} :=
    ⟨fun x ↦ (asymm x.2.2) (genuine_lt_dummy P subdiv vertices tags lanes i x.1)⟩
  change Fintype.card {j // ep j = ep (.inl i) ∧ A j < A (.inl i)} = _
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum,
    Fintype.card_eq_zero (α := {x : Site V Tag L × Fin pad //
      ep (.inr x) = ep (.inl i) ∧ A (.inr x) < A (.inl i)}), Nat.add_zero]
  rw [Fintype.card_subtype]
  change _ = r.ids.countP (fun j ↦ decide (relativeKey P subdiv vertices tags j < relativeKey P subdiv vertices tags i))
  rw [← r.nodup.card_eq_countP (P := fun j ↦ relativeKey P subdiv vertices tags j < relativeKey P subdiv vertices tags i)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, r.complete]
  exact and_congr_right fun h ↦ address_lt_iff_relative P subdiv vertices tags lanes layout (endRole layout side) h

private theorem addressRank_dummy (hc : 2 ≤ c) (layout side : Bool) (s : Site V Tag L) (a : Fin pad) :
    addressRank P subdiv vertices tags lanes layout side (.inr (s,a)) = survivingDegree d c subdiv + a.val := by
  classical
  let A := arcAddress P subdiv vertices tags lanes pad
  let ep := actualEnd P subdiv tags layout side (pad := pad)
  let real := Equiv.subtypeEquivRight (fun j : Id P.Motif subdiv ↦
    show ep (.inl j) = ep (.inr (s,a)) ∧ A (.inl j) < A (.inr (s,a)) ↔ ep (.inl j) = ep (.inr (s,a)) from
      and_iff_left (genuine_lt_dummy P subdiv vertices tags lanes j (s,a)))
  let dummy : {x : Site V Tag L × Fin pad //
      ep (.inr x) = ep (.inr (s,a)) ∧ A (.inr x) < A (.inr (s,a))} ≃ {b : Fin pad // b.val < a.val} := {
    toFun x := ⟨x.1.2, by
      have hs := (dummyEnd tags side).injective x.2.1
      have h := x.2.2
      rcases x with ⟨⟨s', b⟩, _⟩
      change s' = s at hs
      subst s'
      exact (dummy_lt_dummy P subdiv vertices tags lanes s b a).mp h⟩
    invFun b := ⟨(s,b), rfl, (dummy_lt_dummy P subdiv vertices tags lanes s b a).mpr b.2⟩
    left_inv x := Subtype.ext (Prod.ext ((dummyEnd tags side).injective x.2.1).symm rfl)
    right_inv _ := rfl }
  change Fintype.card {j // ep j = ep (.inr (s,a)) ∧ A j < A (.inr (s,a))} = _
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum, Fintype.card_congr real, Fintype.card_congr dummy,
    Fintype.card_fin_lt_of_le a.isLt.le]
  exact congrArg (· + a.val) (genuineEnd_card P subdiv hc layout side (dummyEnd tags side s))

private noncomputable def allIncident {E S : Type*} [Fintype E] [DecidableEq S] (endSite : E → S) (s : S) :
    IncidentRow endSite s := by
  let fiber := Finset.univ.filter (fun e ↦ endSite e = s)
  exact ⟨fiber.toList, fiber.nodup_toList, fun _ ↦ by simp [fiber]⟩

variable [Module (ZMod 2) Tag]

/-- Address order in either endpoint fiber agrees with the full regularized
slot indexing, both on genuine arcs and on the dummy tail. -/
theorem addressRank_eq_slot (hc : 2 ≤ c) (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout side : Bool) {d' : ℕ} (hd : survivingDegree d c subdiv ≤ d') (hJ : 1 < J)
    (i : ActualId P subdiv (d' - survivingDegree d c subdiv)) :
    let := P.slotIdentifierOrder vertices tags subdiv
    let I := P.regularizedSlotIndexing hc hφ layout subdiv hd tags hJ
    addressRank P subdiv vertices tags lanes layout side i =
      ((if side then I.incoming else I.outgoing) (paddedBaseId P subdiv i)).2.val := by
  intro order I
  rcases i with i | ⟨s,a⟩
  · let r (b : Bool) := allIncident (endpoint (P.survivingRole layout) (endRole layout b) (subdiv := subdiv))
      (endpoint (P.survivingRole layout) (endRole layout b) i)
    rw [addressRank_genuine P subdiv vertices tags lanes layout side i (r side)]
    have h := actualSlot_numbers P subdiv vertices tags hc hφ layout hd hJ i (r false) (r true)
    cases side
    · exact h.1
    · exact h.2
  · rw [addressRank_dummy P subdiv vertices tags lanes hc layout side s a]
    cases side <;> rfl

end CompressorRecords.Slots

end VPVNP
end Computability
end OAI
