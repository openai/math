import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecord

/-! # Reading the canonical old record from an induced patch

The vertex slots are the patch in increasing order of its certified names.
The actual wire determines its two numbered ports, and both are paired in
the record precisely when both endpoint vertices are in the patch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {V E A : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  {n K : ℕ} (M : RootedMap V E) (old : Fin n ↪ V)

/-- The original oriented dart, read from the vertex slot and port number. -/
def actual (p : PatchDart (fun i => M.typeAt (old i))) : E × Bool :=
  ((M.num _).symm p.2).val

theorem actual_owner (p : PatchDart (fun i => M.typeAt (old i))) :
    M.graph.vertex (actual M old p).1 (actual M old p).2 = old p.1 :=
  ((M.num _).symm p.2).property

theorem actual_injective : Function.Injective (actual M old) := by
  rintro ⟨i,u⟩ ⟨j,v⟩ h
  have hij := old.injective (((actual_owner M old ⟨i,u⟩).symm.trans
    (congrArg (fun p : E × Bool => M.graph.vertex p.1 p.2) h)).trans (actual_owner M old ⟨j,v⟩))
  change i = j at hij
  subst j
  exact congrArg (Sigma.mk i) ((M.num _).symm.injective (Subtype.ext h))

/-- The dart at an endpoint in the patch has one and only one valid slot. -/
theorem actual_range (p : E × Bool) :
    (∃ q, actual M old q = p) ↔ ∃ i, old i = M.graph.vertex p.1 p.2 := by
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨q.1, (actual_owner M old q).symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨⟨i, M.num _ ⟨p,hi.symm⟩⟩, congrArg Subtype.val ((M.num _).symm_apply_apply _)⟩

/-- Retain the actual other port if it belongs to the patch. Otherwise this
port is a boundary stub, represented by a fixed point. -/
def partner (p : PatchDart (fun i => M.typeAt (old i))) : PatchDart (fun i => M.typeAt (old i)) :=
  if h : ∃ q, actual M old q = cross (actual M old p) then h.choose else p

theorem partner_of_internal {p q : PatchDart (fun i => M.typeAt (old i))}
    (h : actual M old q = cross (actual M old p)) : partner M old p = q := by
  have he : ∃ q, actual M old q = cross (actual M old p) := ⟨q,h⟩
  exact (dite_eq_left he).trans (actual_injective M old (he.choose_spec.trans h.symm))

omit [Fintype E] in
private theorem cross_twice (p : E × Bool) : cross (cross p) = p := by
  rcases p with ⟨e,(_|_)⟩ <;> rfl

omit [Fintype E] in
private theorem cross_ne (p : E × Bool) : cross p ≠ p := by
  rcases p with ⟨e,(_|_)⟩ <;> exact fun h => Bool.noConfusion (congrArg Prod.snd h)

theorem partner_fixed_iff (p : PatchDart (fun i => M.typeAt (old i))) :
    partner M old p = p ↔ ¬ ∃ q, actual M old q = cross (actual M old p) := by
  constructor
  · rintro hf ⟨q,hq⟩
    have he := hf.symm.trans (partner_of_internal M old hq)
    exact cross_ne _ (hq.symm.trans (congrArg _ he.symm))
  · exact fun h => dite_eq_right h

theorem actual_partner {p : PatchDart (fun i => M.typeAt (old i))} (hp : partner M old p ≠ p) :
    actual M old (partner M old p) = cross (actual M old p) := by
  obtain ⟨q,hq⟩ := not_not.mp (mt (partner_fixed_iff M old p).mpr hp)
  rw [partner_of_internal M old hq, hq]

theorem partner_involutive : Function.Involutive (partner M old) := by
  intro p
  by_cases hf : partner M old p = p
  · rw [hf,hf]
  · exact partner_of_internal M old (by rw [actual_partner M old hf, cross_twice])

/-- Restriction to the indicated injection of vertex slots. -/
def ofSlots (label : V → A) (hn : 0 < n) (hk : n ≤ K) : PatchRecord K A where
  shape := {
    size := ⟨n,Nat.lt_succ_of_le hk⟩
    positive := hn
    typeAt i := M.typeAt (old i)
    opposite := (partner_involutive M old).toPerm _
    involutive := partner_involutive M old
    direction := by
      intro p hp
      exact congrArg Prod.snd (actual_partner M old hp) }
  label i := label (old i)

/-- List a patch in increasing order of its distinct old vertex names. -/
def slotOrder (P : Finset V) (name : V ↪ ℕ) : Fin P.card ≃ ↥P :=
  let : LinearOrder ↥P := LinearOrder.lift' (fun v : P => name v) (name.injective.comp Subtype.val_injective)
  (Fintype.orderIsoFinOfCardEq ↥P (Fintype.card_coe _)).toEquiv

omit [Fintype V] [DecidableEq V] in
theorem slotOrder_strict (P : Finset V) (name : V ↪ ℕ) :
    StrictMono (fun i => name ((slotOrder P name i).val)) := by
  let : LinearOrder ↥P := LinearOrder.lift' (fun v : P => name v) (name.injective.comp Subtype.val_injective)
  exact (Fintype.orderIsoFinOfCardEq ↥P (Fintype.card_coe _)).strictMono

/-- The canonical injection of old vertices indexed by their record slots. -/
def slots (P : Finset V) (name : V ↪ ℕ) : Fin P.card ↪ V :=
  (slotOrder P name).toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype V] [DecidableEq V] in
theorem mem_slots_iff (P : Finset V) (name : V ↪ ℕ) (x : V) :
    (∃ i, slots P name i = x) ↔ x ∈ P := by
  constructor
  · rintro ⟨i,rfl⟩
    exact (slotOrder P name i).property
  · intro h
    exact ⟨(slotOrder P name).symm ⟨x,h⟩, congrArg Subtype.val ((slotOrder P name).apply_symm_apply _)⟩

/-- Extracting a record retains the complete labels on the sorted slots. -/
def extract (label : V → A) (P : Finset V) (name : V ↪ ℕ) (hn : P.Nonempty) (hk : P.card ≤ K) :
    PatchRecord K A :=
  ofSlots M (slots P name) label (Finset.card_pos.mpr hn) hk

/-- Opposite ports are paired inside the record exactly on internal wires. -/
theorem extract_stub_iff (label : V → A) (P : Finset V) (name : V ↪ ℕ) (hn : P.Nonempty)
    (hk : P.card ≤ K) (p : (extract M label P name hn hk).shape.Dart) :
    (extract M label P name hn hk).shape.opposite p = p ↔
      M.graph.vertex (actual M (slots P name) p).1 (!(actual M (slots P name) p).2) ∉ P := by
  exact (partner_fixed_iff M (slots P name) p).trans (not_congr
    ((actual_range M (slots P name) _).trans (mem_slots_iff P name _)))

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
