import OAI.Hierarchy.ProbeStageRendered

namespace OAI
/-! # The matching retained after each complete allocation pass -/

namespace Hierarchy.ProbeStage

/-- The retained matching includes the concrete mixed-radix numbering
of groups used on the native tape. -/
structure Matching (n : ℕ) where
  shape : Shape
  count : ℕ
  encode : shape.Group ↪ Fin count
  tiles : Tiles (Fin n) shape.Group shape.span

namespace Matching
variable {n B ℓ : ℕ}

noncomputable def root (π : Equiv.Perm (Fin n)) : Matching n where
  shape := ⟨Unit,n⟩
  count := 1
  encode := ⟨fun _ => 0,fun _ _ _ => Subsingleton.elim ..⟩
  tiles := permutationTiles π

noncomputable def descend (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (p : Matching n) : Matching n :=
  let a := allocateMasked p.tiles pos s
  {shape := ⟨p.shape.Group×Fin B,innerSize p.shape.span B⟩
   count := p.count*B
   encode := (p.encode.prodMap (Function.Embedding.refl (Fin B))).trans finProdFinEquiv.toEmbedding
   tiles := inner p.tiles pos a}

noncomputable def walk (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (p : Matching n) :
    ℕ → Matching n
  | 0 => p
  | j+1 => descend pos s (walk pos s p j)

theorem walk_succ (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (p : Matching n) (j : ℕ) :
    walk pos s p (j+1)=walk pos s (descend pos s p) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (descend pos s) ih

noncomputable def entering (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (p : Matching n) :=
  layer (enter p.tiles pos (allocateMasked p.tiles pos s))
noncomputable def leaving (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (p : Matching n) :=
  layer (exitStage p.tiles pos (allocateMasked p.tiles pos s))

/-- Output order is entering depths 0 through q−1, the current center,
then the outgoing moves of depths q−1 through 0. -/
theorem rendered_walk (pos : 0<B) (s : MaskIndex B → Fin ℓ → Fin B) (q : ℕ) (p : Matching n) :
    render (Fin n) B pos (fun t => allocateMasked t pos s) q p.tiles =
      ((List.range q).map (fun j => entering pos s (walk pos s p j))) ++
      [layer (walk pos s p q).tiles] ++
      (((List.range q).map (fun j => leaving pos s (walk pos s p j))).reverse) := by
  induction q generalizing p with
  | zero => rfl
  | succ q ih =>
    change ([entering pos s p] ++ render _ _ pos _ q (descend pos s p).tiles ++ [leaving pos s p]) = _
    rw [ih,List.range_succ_eq_map]
    have enter_succ : (fun j => entering pos s (walk pos s p j)) ∘ Nat.succ =
        fun j => entering pos s (walk pos s (descend pos s p) j) :=
      funext fun j => congrArg (entering pos s) (walk_succ pos s p j)
    have exit_succ : (fun j => leaving pos s (walk pos s p j)) ∘ Nat.succ =
        fun j => leaving pos s (walk pos s (descend pos s p) j) :=
      funext fun j => congrArg (leaving pos s) (walk_succ pos s p j)
    simp only [List.map_cons,List.map_map,List.reverse_cons,enter_succ,exit_succ,
      List.cons_append,List.nil_append,List.append_assoc,show walk pos s p 0=p from rfl]
    rw [walk_succ pos s p q]

end Matching

noncomputable def history (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) (j : ℕ) :=
  Matching.walk (radix_pos h d) (formatAdvice h d).row (Matching.root π) j

theorem history_sizes {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) {j : ℕ} (depth : j≤rounds d) :
    (history h d π j).count = (radix h d)^j ∧ (history h d π j).shape.span=2^widthLog h d j := by
  induction j with
  | zero => simp [history,Matching.walk,Matching.root,widthLog_start hd]
  | succ j ih =>
    obtain ⟨card,span⟩ := ih (by omega)
    exact ⟨by change (history h d π j).count*radix h d=_;rw [card,pow_succ],
      by change innerSize (history h d π j).shape.span (radix h d)=_;rw [span,inner_exact (by omega)]⟩

theorem history_card {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : ℕ) :
    Fintype.card (history h d π j).shape.Group=(history h d π j).count := by
  induction j with
  | zero => exact Fintype.card_unit
  | succ j ih =>
    change Fintype.card ((history h d π j).shape.Group × Fin (radix h d)) =
      (history h d π j).count*radix h d
    rw [Fintype.card_prod,Fintype.card_fin,ih]

theorem advised_history (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) :
    let a := (formatAdvice h d).row
    let pos := radix_pos h d
    let q := rounds d
    (advisedRoute h d π).layers =
      (List.range q).map (fun j => Matching.entering pos a (history h d π j)) ++
      [layer (history h d π q).tiles] ++
      ((List.range q).map (fun j => Matching.leaving pos a (history h d π j))).reverse := by
  exact (advised_render h d π).trans (Matching.rendered_walk _ _ _ (Matching.root π))

end Hierarchy.ProbeStage

end OAI
