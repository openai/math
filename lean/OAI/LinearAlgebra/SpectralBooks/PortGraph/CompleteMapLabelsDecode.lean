import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsFace

/-! # Decoding the minimum on each face from the one-edge equations -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarCertSize Equiv.Perm

variable {N : ℕ}

variable {D : Type*} (φ : Equiv.Perm D) (own claim : D → FaceKey) (dist : D → ℕ)

/-- Decode by actually walking forward the reported number of steps. -/
def decodeFace (d : D) : D × ℕ := ((φ ^ dist d) d, dist d)

theorem CodedFaceEquations.hit (h : CodedFaceEquations φ own claim dist) (d : D) :
    own ((φ ^ dist d) d) = claim d := by
  induction d using (measure dist).wf.induction with
  | h d ih =>
    by_cases he : claim d = own d
    · rw [(h d).2.2.1 he, pow_zero, one_apply, he]
    · have hs := (h d).2.2.2 he
      have hh := ih (φ d) (by change dist (φ d) < dist d; omega)
      rw [hs, pow_succ, mul_apply, hh, (h d).1]

theorem decodeFace_valid [LinearOrder D] (ho : StrictMono own)
    (h : CodedFaceEquations φ own claim dist) : PlanarFace.Valid φ (decodeFace φ dist) where
  constant d := ho.injective (by
    change own ((φ ^ dist (φ d)) (φ d)) = own ((φ ^ dist d) d)
    rw [h.hit, h.hit, (h d).1])
  lower d := ho.le_iff_le.mp (by
    change own ((φ ^ dist d) d) ≤ own d
    rw [h.hit]
    exact (h d).2.1)
  zero d hd := (h d).2.2.1 ((h.hit φ own claim dist d).symm.trans (congrArg own hd))
  step d hd := (h d).2.2.2 (fun he => hd (ho.injective ((h.hit φ own claim dist d).trans he)))

theorem codedFaceEquations_of_valid [LinearOrder D] (ho : StrictMono own)
    {f : D → D × ℕ} (hf : PlanarFace.Valid φ f) :
    CodedFaceEquations φ own (fun d => own (f d).1) (fun d => (f d).2) :=
  fun d => ⟨congrArg own (hf.constant d), ho.monotone (hf.lower d),
    fun he => hf.zero d (ho.injective he), fun he => hf.step d (fun hh => he (congrArg own hh))⟩

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable (b : V → BaseAlphabet N)

/-- The dart order is the lexicographic order on the two encoded coordinates. -/
theorem selfKey_strictMono (hinj : Function.Injective (fun v => vertexVal (b v) .preorderName)) :
    letI := M.graph.namedPortOrder ⟨_,hinj⟩ M.slots
    StrictMono (atDart M b selfKey) := by
  let key : V ↪ ℕ := ⟨_,hinj⟩
  let := M.graph.namedPortOrder key M.slots
  intro a d h
  apply Prod.Lex.toLex_lt_toLex.mpr
  rcases (M.graph.namedPortOrder_lt key M.slots a d).mp h with hl | ⟨he,hl⟩
  · exact Or.inl hl
  · exact Or.inr ⟨he, Nat.succ_lt_succ hl⟩

/-- The marked-port weight, computed solely from the four labels. -/
def markedCount (x : BaseAlphabet N) : ℕ :=
  (Finset.univ.filter (fun i : Fin 4 => (x.2.1 i).isSome ∧ faceKey x i = selfKey x i)).card

/-- The edge weight is the number of outgoing slots, including the outgoing
end of a loop. -/
def tailCount (x : BaseAlphabet N) : ℕ :=
  (Finset.univ.filter (fun i : Fin 4 => x.2.1 i = some false)).card

theorem card_slots_filter (v : V) (P : Fin 4 → Prop) [DecidablePred P]
    (hP : ∀ i, P i → ∃ p, M.slots v p = i) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun p : M.graph.Port v => P (M.slots v p))).card := by
  symm
  apply Finset.card_bij (fun p _ => M.slots v p)
  · exact fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩
  · exact fun _ _ _ _ he => (M.slots v).injective he
  · intro i hi
    obtain ⟨p,rfl⟩ := hP i (Finset.mem_filter.mp hi).2
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩,rfl⟩

theorem padded_at_port {v : V} (p : M.graph.Port v) :
    RootedMap.paddedDirection (M.typeAt v) (M.slots v p) = some p.val.2 := by
  unfold RootedMap.paddedDirection
  have hi : (M.slots v p).val < (M.typeAt v).degree.val := (M.num v p).isLt
  rw [dite_eq_left hi]
  change some (((M.num v).symm (M.num v p)).val.2) = _
  simp

theorem exists_port_of_padded {v : V} (i : Fin 4)
    (hi : (RootedMap.paddedDirection (M.typeAt v) i).isSome) : ∃ p, M.slots v p = i := by
  unfold RootedMap.paddedDirection at hi
  split at hi
  · rename_i h
    exact ⟨(M.num v).symm ⟨i.val,h⟩, Fin.ext (by simp [RootedMap.slots])⟩
  · cases hi

theorem tailCount_eq (ht : ∀ v, (b v).2.1 = RootedMap.paddedDirection (M.typeAt v)) (v : V) :
    tailCount (b v) = PlanarPatch.edgeWeight M.graph v := by
  classical
  unfold tailCount
  rw [card_slots_filter M v _ (fun i hi => exists_port_of_padded M i (by rw [← ht v, hi]; rfl))]
  simp [PlanarPatch.edgeWeight, ht, padded_at_port]

theorem markedCount_eq (ht : ∀ v, (b v).2.1 = RootedMap.paddedDirection (M.typeAt v))
    {f : E × Bool → (E × Bool) × ℕ} [LinearOrder (E × Bool)]
    (hinj : Function.Injective (atDart M b selfKey))
    (hf : ∀ p, atDart M b faceKey p = atDart M b selfKey (f p).1) (v : V) :
    markedCount (b v) = PlanarPatch.faceWeight M.graph f v := by
  classical
  unfold markedCount
  rw [card_slots_filter M v _ (fun i hi => exists_port_of_padded M i (by rw [← ht v]; exact hi.1))]
  unfold PlanarPatch.faceWeight
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ht, padded_at_port,
    Option.isSome_some, eq_self, true_and]
  rw [← atDart_val M b p faceKey, ← atDart_val M b p selfKey, hf, hinj.eq_iff]

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
