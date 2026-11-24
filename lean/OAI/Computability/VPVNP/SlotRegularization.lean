import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Regularizing labeled wire slots

In Section 7.2 and Appendix C of *VP and VNP differ over every field*,
surviving role edges carry an identifier for their motif, role pair and
subdivision number. Once their two base-endpoint fibers have a common size,
the fibers can be numbered separately. Parallel dummy edges fill any
deficit. All numbering is at the base, so it transports along the remaining
lane without depending on widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {B E L : Type*} {k d : ℕ}

/-- Both endpoint numberings of a set of identified arcs, with their lane
displacements. The incoming slot of an ID is the target of its outgoing slot. -/
structure SlotIndexing (B E L : Type*) (d : ℕ) (src dst : E → B) (shift : E → L) where
  /-- The lifted slot graph implementing the given source, target, and lane displacement for
  every arc identifier. -/
  graph : LiftedSlots B d L
  /-- The bijection assigning each arc identifier its source base vertex and local outgoing
  slot number. -/
  outgoing : E ≃ B × Fin d
  /-- The bijection assigning each arc identifier its target base vertex and local incoming
  slot number. -/
  incoming : E ≃ B × Fin d
  src_eq : ∀ e, (outgoing e).1 = src e
  dst_eq : ∀ e, (incoming e).1 = dst e
  match_eq : ∀ e, graph.base.target (outgoing e) = incoming e
  displacement_eq : ∀ e, graph.displacement (outgoing e) = shift e

/-- At any absolute source lane the ID gives both slot addresses and the
destination lane, with the same endpoint numberings at every translate. -/
theorem SlotIndexing.actualTarget [AddCommGroup L] {src dst : E → B} {shift : E → L}
    (I : SlotIndexing B E L d src dst shift) (e : E) (g : L) :
    I.graph.actualTarget (I.outgoing e, g) = (I.incoming e, g + shift e) := by
  simp [I.match_eq, I.displacement_eq]

/-- Number each endpoint fiber by its ID order. -/
private def numberFiber [Fintype E] [LinearOrder E] [DecidableEq B]
    (endpoint : E → B) (h : ∀ b, Fintype.card {e // endpoint e = b} = k) : E ≃ B × Fin k :=
  (Equiv.sigmaFiberEquiv endpoint).symm.trans (Equiv.sigmaEquivProdOfEquiv
    fun b ↦ (Fintype.orderIsoFinOfCardEq {e // endpoint e = b} (h b)).symm.toEquiv)

/-- Padding attaches one new ID per missing outgoing slot at each base. -/
abbrev PaddedId (B E : Type*) (deficit : ℕ) := E ⊕ B × Fin deficit

/-- All padded arcs leave the vertex in their ID. -/
def paddedSource (src : E → B) : PaddedId B E k → B := Sum.elim src Prod.fst

/-- The added slots advance the base through a common permutation. -/
def paddedTarget (dst : E → B) (next : Equiv.Perm B) : PaddedId B E k → B :=
  Sum.elim dst fun p ↦ next p.1

/-- Dummy arcs preserve the remaining lane. -/
def paddedShift [Zero L] (shift : E → L) : PaddedId B E k → L := Sum.elim shift (fun _ ↦ 0)

/-- For arbitrary widths, including lane-dependent ones, assign zero to
each dummy arc. -/
def paddedWidth (width : E → L → ℕ) : PaddedId B E k → L → ℕ := Sum.elim width (fun _ _ ↦ 0)

/-- A common deficit in the two endpoint counts can be padded to degree
`d`. Real slots keep their ID order inside each fiber and dummy slots follow
them. The next-base permutation may be the cyclic shift on the tag. -/
def paddedSlotIndexing [Fintype E] [LinearOrder E] [DecidableEq B] [Zero L]
    (src dst : E → B) (shift : E → L) (hends : ∀ e, dst e ≠ src e)
    (hsrc : ∀ b, Fintype.card {e // src e = b} = k)
    (hdst : ∀ b, Fintype.card {e // dst e = b} = k)
    (hkd : k ≤ d) (next : Equiv.Perm B) (hnext : ∀ b, next b ≠ b) :
    SlotIndexing B (PaddedId B E (d - k)) L d (paddedSource src) (paddedTarget dst next)
      (paddedShift shift) := by
  let combine : (B × Fin k ⊕ B × Fin (d - k)) ≃ B × Fin d :=
    (Equiv.prodSumDistrib B (Fin k) (Fin (d - k))).symm.trans
      ((Equiv.refl B).prodCongr (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkd))))
  let out := (Equiv.sumCongr (numberFiber src hsrc) (Equiv.refl (B × Fin (d - k)))).trans combine
  let inc := (Equiv.sumCongr (numberFiber dst hdst)
    (next.prodCongr (Equiv.refl (Fin (d - k))))).trans combine
  have source (e : PaddedId B E (d - k)) : (out e).1 = paddedSource src e := by
    cases e <;> rfl
  have target (e : PaddedId B E (d - k)) : (inc e).1 = paddedTarget dst next e := by
    cases e <;> rfl
  let G : SlotGraph B d := {
    target := out.symm.trans inc
    ends_ne := by
      intro p
      obtain ⟨e, rfl⟩ := out.surjective p
      change (inc (out.symm (out e))).1 ≠ (out e).1
      rw [out.symm_apply_apply, source, target]
      cases e with
      | inl e => exact hends e
      | inr p => exact hnext p.1 }
  exact {
    graph := ⟨G, fun p ↦ paddedShift shift (out.symm p)⟩
    outgoing := out
    incoming := inc
    src_eq := source
    dst_eq := target
    match_eq e := congrArg inc (out.symm_apply_apply e)
    displacement_eq e := congrArg (paddedShift shift) (out.symm_apply_apply e) }

private theorem numberFiber_rank [Fintype E] [LinearOrder E] [DecidableEq B]
    (endpoint : E → B) (h : ∀ b, Fintype.card {e // endpoint e = b} = k)
    (e : E) (ids : Finset E) (hids : ∀ a, a ∈ ids ↔ endpoint a = endpoint e) :
    ((numberFiber endpoint h e).2 : ℕ) = (ids.filter (· < e)).card := by
  let F := {a // endpoint a = endpoint e}
  let label := (Fintype.orderIsoFinOfCardEq F (h (endpoint e))).symm
  let a₀ : F := ⟨e, rfl⟩
  let smaller := label.toEquiv.subtypeEquiv (p := fun a : F ↦ a < a₀)
    (q := fun i : Fin k ↦ (i : ℕ) < (label a₀).val) (fun a ↦ by
      change a < a₀ ↔ label a < label a₀
      simp)
  let members : {a : F // a < a₀} ≃ (ids.filter (· < e)) := {
    toFun := fun a ↦ ⟨a.1.1, Finset.mem_filter.mpr ⟨(hids _).mpr a.1.2, a.2⟩⟩
    invFun := fun a ↦ ⟨⟨a.1, (hids _).mp (Finset.mem_filter.mp a.2).1⟩,
      (Finset.mem_filter.mp a.2).2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  change (label a₀).val = _
  rw [← Fintype.card_fin_lt_of_le (label a₀).isLt.le, ← Fintype.card_congr smaller,
    Fintype.card_congr members, Fintype.card_coe]

/-- The two slot numbers of a real ID can be recovered from the two local
incidence lists alone. Each is the number of smaller IDs in its list. -/
theorem paddedSlot_numbers [Fintype E] [LinearOrder E] [DecidableEq B] [Zero L]
    (src dst : E → B) (shift : E → L) (hends : ∀ e, dst e ≠ src e)
    (hsrc : ∀ b, Fintype.card {e // src e = b} = k)
    (hdst : ∀ b, Fintype.card {e // dst e = b} = k)
    (hkd : k ≤ d) (next : Equiv.Perm B) (hnext : ∀ b, next b ≠ b)
    (e : E) (outIds inIds : Finset E) (hout : ∀ a, a ∈ outIds ↔ src a = src e)
    (hin : ∀ a, a ∈ inIds ↔ dst a = dst e) :
    let I := paddedSlotIndexing src dst shift hends hsrc hdst hkd next hnext
    ((I.outgoing (.inl e)).2 : ℕ) = (outIds.filter (· < e)).card ∧
    ((I.incoming (.inl e)).2 : ℕ) = (inIds.filter (· < e)).card :=
  ⟨numberFiber_rank src hsrc e outIds hout, numberFiber_rank dst hdst e inIds hin⟩

/-- Dummy slots follow the genuine incidence list in both numberings. -/
theorem paddedSlot_dummy_numbers [Fintype E] [LinearOrder E] [DecidableEq B] [Zero L]
    (src dst : E → B) (shift : E → L) (hends : ∀ e, dst e ≠ src e)
    (hsrc : ∀ b, Fintype.card {e // src e = b} = k)
    (hdst : ∀ b, Fintype.card {e // dst e = b} = k)
    (hkd : k ≤ d) (next : Equiv.Perm B) (hnext : ∀ b, next b ≠ b) (b : B) (i : Fin (d - k)) :
    let I := paddedSlotIndexing src dst shift hends hsrc hdst hkd next hnext
    ((I.outgoing (.inr (b, i))).2 : ℕ) = k + i ∧ ((I.incoming (.inr (b, i))).2 : ℕ) = k + i :=
  ⟨rfl, rfl⟩

/-- Cyclic dummy slots change only the tag of the new base. -/
def cycleTags {V Tag : Type*} {J : ℕ} (index : Tag ≃ Fin J) : Equiv.Perm (V × Tag) :=
  (Equiv.refl V).prodCongr (index.trans ((finRotate J).trans index.symm))

theorem cycleTags_ne {V Tag : Type*} {J : ℕ} (index : Tag ≃ Fin J) (hJ : 1 < J)
    (b : V × Tag) : cycleTags index b ≠ b := by
  intro h
  have hrot := congrArg (fun p : V × Tag ↦ index p.2) h
  change index (index.symm (finRotate J (index b.2))) = index b.2 at hrot
  rw [index.apply_symm_apply] at hrot
  cases J with
  | zero => omega
  | succ n =>
    have he := congrArg Fin.val hrot
    rw [coe_finRotate] at he
    split at he
    · rename_i hlast
      rw [hlast] at he
      simp at he
      omega
    · omega

end Compression

end VPVNP
end Computability
end OAI
