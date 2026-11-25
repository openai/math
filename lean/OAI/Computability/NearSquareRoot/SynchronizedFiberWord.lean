import OAI.Computability.NearSquareRoot.SynchronizedPlacedWord

/-! A bounded primitive word for an axis fiber pass in a full padded block.
The placement acts only in primary coordinates of the physical axis, even
when the short restored circuit temporarily needs more coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedBorrowing SynchronizedPadding

noncomputable section

variable {a b c r : ℕ}

private abbrev Cell (a b c : ℕ) := Fin b × (Fin a ⊕ Fin c)
private abbrev Local (a r : ℕ) := Fin a ⊕ Fin (2*r-a)

private def primary (a b c : ℕ) : Fin b × Fin a ↪ Cell a b c :=
  (Function.Embedding.refl _).prodMap (Function.Embedding.inl)

/-- Source and spectator coordinates embedded in the primary cells of a padded axis. -/
def batchCells (hr : 2*r ≤ 8*a) (j : Fin 15) :
    Local a r × Fin (size b j) ↪ Cell a b c :=
  (Equiv.prodComm ..).toEmbedding.trans ((batchPlacement b j hr).trans (primary a b c))

/-- The batched copies of one local matrix on a full padded physical block. -/
def batchMatrix (hr : 2*r ≤ 8*a) (j : Fin 15) (M : Matrix (Local a r) (Local a r) ℂ) :
    Matrix (Cell a b c) (Cell a b c) ℂ :=
  placeHom (batchCells hr j) M

/-- Apply a whole local circuit to the same disjoint batch of fibers. -/
theorem batchMatrix_list_prod (hr : 2*r ≤ 8*a) (j : Fin 15)
    (w : List (Matrix (Local a r) (Local a r) ℂ)) :
    batchMatrix (b := b) (c := c) hr j w.prod = (w.map (batchMatrix hr j)).prod :=
  map_list_prod (placeHom (batchCells (c := c) (b := b) hr j)) w

private def restrict (x : Cell a b c → ℂ) : Fin b × Fin a → ℂ := x ∘ primary a b c

private theorem batchMatrix_restrict (hr : 2*r ≤ 8*a) (j : Fin 15) (M : Matrix (Local a r) (Local a r) ℂ)
    (x : Cell a b c → ℂ) :
    restrict (batchMatrix hr j M *ᵥ x) = placedMatrix hr j M (restrict x) := by
  funext p
  set e₁ := batchPlacement b j hr
  set e₂ := batchCells (c := c) (b := b) hr j
  have hx (s : Fin (size b j)) (t : Local a r) : e₂ (t,s) = primary a b c (e₁ (s,t)) := rfl
  change (placeHom e₂ M *ᵥ x) (primary a b c p) = _
  rw [placeHom_mulVec]
  unfold placedMatrix
  rw [show batchPlacement b j hr = e₁ from rfl]
  by_cases h : p ∈ Set.range e₁
  · obtain ⟨⟨s,t⟩,rfl⟩ := h
    rw [← hx, e₂.injective.extend_apply, e₁.injective.extend_apply]
    simp only [hx, restrict, Function.comp_def]
  · have h' : primary a b c p ∉ Set.range e₂ := by
      rintro ⟨⟨t,s⟩, hp⟩
      exact h ⟨(s,t), (primary a b c).injective (hx s t ▸ hp)⟩
    rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h']
    rfl

private theorem batchMatrix_spare (hr : 2*r ≤ 8*a) (j : Fin 15) (M : Matrix (Local a r) (Local a r) ℂ)
    (x : Cell a b c → ℂ) (i : Fin b) (t : Fin c) :
    (batchMatrix hr j M *ᵥ x) (i, .inr t) = x (i, .inr t) := by
  rw [batchMatrix, placeHom_mulVec, Function.extend_apply']
  rintro ⟨⟨u,s⟩,h⟩
  have hh : Sum.inl ((batchPlacement b j hr (s,u)).2) = (Sum.inr t : Fin a ⊕ Fin c) := congrArg Prod.snd h
  exact Sum.inl_ne_inr hh

def fiberMatrix (b : ℕ) (U : Matrix (Fin a) (Fin a) ℂ) :
    Matrix (Cell a b c) (Cell a b c) ℂ :=
  (blockDiagonal fun _ : Fin b ↦ axisPadding (b := Fin c) U).submatrix Prod.swap Prod.swap

theorem fiberMatrix_mulVec (U : Matrix (Fin a) (Fin a) ℂ) (x : Cell a b c → ℂ) (p : Cell a b c) :
    (fiberMatrix b U *ᵥ x) p = (axisPadding U *ᵥ fun t ↦ x (p.1,t)) p.2 := by
  change ((blockDiagonal fun _ : Fin b ↦ axisPadding U).submatrix (Equiv.prodComm ..) (Equiv.prodComm ..) *ᵥ x) p = _
  rw [submatrix_mulVec_equiv]
  exact copies_apply _ _ _

private theorem batch_prod_apply (hr : 2*r ≤ 8*a) (M : Matrix (Local a r) (Local a r) ℂ)
    (js : List (Fin 15)) (x : Cell a b c → ℂ) :
    let y := (js.map fun j ↦ batchMatrix hr j M).prod *ᵥ x
    restrict y = js.foldr (placedMatrix hr · M) (restrict x) ∧
      ∀ i (t : Fin c), y (i, .inr t) = x (i, .inr t) := by
  induction js with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, List.foldr_cons]
    exact ⟨(batchMatrix_restrict ..).trans (congrArg _ ih.1), fun i t ↦
      (batchMatrix_spare ..).trans (ih.2 i t)⟩

/-- All fifteen batches implement one fiber pass on the padded block. -/
theorem fiberMatrix_eq_batches (hb : 8 ≤ b) (hr : 2*r ≤ 8*a)
    (U : Matrix (Fin a) (Fin a) ℂ) :
    fiberMatrix (c := c) b U = ((List.finRange 15).map fun j ↦
      batchMatrix hr j (extend (rowInclusion a (2*r-a)) U)).prod := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  obtain ⟨hocc,hsp⟩ := batch_prod_apply hr (extend (rowInclusion a (2*r-a)) U) (List.finRange 15) x
  rw [full_placedMatrix hb hr U rfl] at hocc
  funext ⟨i, t⟩
  rw [fiberMatrix_mulVec, axisPadding, fromBlocks_mulVec]
  cases t with
  | inl t => simpa [restrict, primary, Function.comp_def] using (congrFun hocc (i,t)).symm
  | inr t => simpa using (hsp i t).symm

/-- Running fifteen batches preserves the short-word gate choices of each factor.
The bound is on ordinary primitive layers over the full physical block. -/
theorem fiberMatrix_word (hb : 8 ≤ b) (hr : 2*r ≤ 8*a) (even : Even (b*(a+c)))
    {d : ℕ} (U : Matrix (Fin a) (Fin a) ℂ)
    (h : HasShortWord (extend (rowInclusion a (2*r-a)) U) d) :
    HasShortWord (fiberMatrix (c := c) b U) (15*d) := by
  have hE : Even (Fintype.card (Cell a b c)) := by simpa [Cell] using even
  rw [fiberMatrix_eq_batches hb hr]
  have H (l : List (Fin 15)) :
      HasShortWord ((l.map fun j ↦ batchMatrix (b := b) (c := c) hr j (extend (rowInclusion a (2*r-a)) U)).prod) (l.length*d) := by
    induction l with
    | nil => simpa using (HasShortWord.empty (A := Cell a b c))
    | cons j l ih =>
      have hj := h.place (batchCells (c := c) (b := b) hr j) hE
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_comm]
      exact hj.append ih
  simpa using H (List.finRange 15)

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
