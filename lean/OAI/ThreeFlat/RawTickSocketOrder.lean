import OAI.ThreeFlat.RawTickNumbering

namespace OAI
/-! # Chronological order of uses of each raw template address -/

namespace ThreeFlat.RawTick

open scoped Classical
noncomputable section
variable {F : Type*} {p : ℕ} (N : BitNetwork F p)

def source (a : ℕ) : ℕ :=
  if ha : a<sockets N.cells then
    (sourceIndex (N.address (finProdFinEquiv.symm ⟨a,ha⟩))).val else 0

theorem source_at (u : N.Socket) : source N (ordinal N u) = (sourceIndex (N.address u)).val := by
  rw [source,dite_eq_left (show ordinal N u<sockets N.cells from (finProdFinEquiv u).isLt)]
  change (sourceIndex (N.address (finProdFinEquiv.symm (finProdFinEquiv u)))).val = _
  rw [Equiv.symm_apply_apply]

theorem source_lt (i : ℕ) (hi : i<sockets N.cells) : source N i<sources N.internal p := by
  simp only [source,hi,↓reduceDIte]
  exact Fin.isLt _

def occurrence (s : N.Source) (j : Fin (N.arity s)) := ordinal N (N.socketAt s j)

theorem occurrence_lt (s : N.Source) (j : Fin (N.arity s)) : occurrence N s j < sockets N.cells :=
  (finProdFinEquiv (N.socketAt s j)).isLt

set_option maxHeartbeats 800000 in
theorem occurrence_strictMono (s : N.Source) : StrictMono (occurrence N s) := by
  let index : N.Socket ≃ Fin (sockets N.cells) := finProdFinEquiv
  let chainOrder : LinearOrder (N.Fiber s) :=
    LinearOrder.lift' (fun u : N.Fiber s => index u.val) (index.injective.comp Subtype.val_injective)
  let := chainOrder
  let order := Fintype.orderIsoFinOfCardEq (N.Fiber s) rfl
  intro i j h
  change (index (order i).val).val < (index (order j).val).val
  exact @OrderIso.strictMono _ _ _ chainOrder.toPartialOrder.toPreorder order i j h

theorem occurrence_iff (s : N.Source) {i : ℕ} (hi : i<sockets N.cells) :
    source N i = (sourceIndex s).val ↔ ∃ j, occurrence N s j=i := by
  let u : N.Socket := finProdFinEquiv.symm (⟨i,hi⟩ : Fin (sockets N.cells))
  have hu : ordinal N u=i := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨i,hi⟩)
  rw [← hu,source_at]
  constructor
  · intro eq
    have es := sourceIndex.injective (Fin.ext eq)
    have found (t : N.Source) (ht : N.address u=t) : ∃ j, occurrence N t j=ordinal N u := by
      subst t
      exact ⟨N.socketOffset u,by simp [occurrence]⟩
    exact found s es
  · rintro ⟨j,eq⟩
    have same : N.socketAt s j=u := finProdFinEquiv.injective (Fin.ext eq)
    rw [← same,N.address_socketAt]

end
end ThreeFlat.RawTick

end OAI
