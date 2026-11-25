import OAI.ThreeFlat.Diagonal.HistogramPortKernel

namespace OAI
/-! # Copy-local admission of the selector fields of a motif party -/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators

variable {H J S E F : Type*} [Fintype H] [DecidableEq H] [Nonempty H] [Fintype J] [Nonempty J]
    [Fintype E] [Fintype S] [CommRing F] {r k : ℕ}

variable (G : Supply J S) (j : J) (code : H ↪ Fin (2^k))
    (raw : (ports G).Port j → Fin r → Fin (2^k))

noncomputable def readLetter (i : Fin r) := Function.invFun code (raw (anchorPort G j) i)

/-- This is a bounded-arity predicate on the selector fields at one copy. -/
def copyGood (i : Fin r) : Prop :=
  (∀ a, raw a i = raw (anchorPort G j) i) ∧ ∃ h, code h = raw (anchorPort G j) i

omit [Fintype J] [Nonempty J] [Fintype S] in
theorem copyGood_all (v : Histogram H r) :
    ((∀ i, copyGood G j code raw i) ∧ histogram (readLetter G j code raw) = v) ↔
      (∀ a, raw a = raw (anchorPort G j)) ∧
      ∃ t : {s // histogram s = v}, sequenceCode code r t.val = raw (anchorPort G j) := by
  constructor
  · rintro ⟨ok,eq⟩
    refine ⟨fun a => funext fun i => (ok i).1 a,⟨⟨readLetter G j code raw,eq⟩,?_⟩⟩
    funext i
    exact Function.invFun_eq (ok i).2
  · rintro ⟨same,t,encoded⟩
    have read (i : Fin r) : readLetter G j code raw i = t.val i := by
      have h := congrFun encoded i
      change code (t.val i) = raw (anchorPort G j) i at h
      rw [readLetter,←h]
      exact Function.leftInverse_invFun code.injective _
    refine ⟨fun i => ⟨fun a => congrFun (same a) i, ⟨t.val i,congrFun encoded i⟩⟩,?_⟩
    rw [funext read,t.property]

omit [Fintype J] [Nonempty J] [Fintype E] in
/-- Agreement and alphabet membership come from the bounded local LUT, while
histogram equality comes from one counted mask per alphabet symbol. Their
conjunction is exactly the branch selected by the histogram wire kernel. -/
theorem histogramKernel_admit (D : PortGraph J E) (w base : E → ℕ) (hpad : ∀ a, w a ≤ base a*r)
    (sw : H → S → ℕ) (M : ∀ h a, D.State (fun e => Fin (2^base e)) a →
      (ports G).State (fun e => Fin (2^sw h e)) a → F) (v : Histogram H r)
    (x : D.State (fun e => Fin (2^w e)) j)
    (y : (ports G).State (fun e => (Fin r → Fin (2^k)) × Fin (2^histWidth sw v e)) j)
    (val : F) (goodVal : ∀ t : {s // histogram s = v}, sequenceCode code r t.val = (y (anchorPort G j)).1 →
      val = histogramTileProduct D G w base hpad sw M v j x t (fun a => (y a).2)) :
    histogramKernel D G w base hpad sw code M v j x y =
      (if (∀ i, copyGood G j code (fun a => (y a).1) i) ∧ histogram (readLetter G j code (fun a => (y a).1)) = v
        then 1 else 0) * val := by
  rw [histogramKernel_eq]
  have criterion := copyGood_all G j code (fun a => (y a).1) v
  by_cases same : ∀ a, (y a).1 = (y (anchorPort G j)).1
  · by_cases row : ∃ t : {s // histogram s = v}, sequenceCode code r t.val = (y (anchorPort G j)).1
    · have accept := criterion.mpr ⟨same,row⟩
      simp only [ite_eq_left same,dite_eq_left row,ite_eq_left accept,one_mul]
      exact (goodVal row.choose row.choose_spec).symm
    · have reject := fun ok => row (criterion.mp ok).2
      simp only [ite_eq_left same,dite_eq_right row,ite_eq_right reject,zero_mul]
  · have reject := fun ok => same (criterion.mp ok).1
    simp only [ite_eq_right same,ite_eq_right reject,zero_mul]

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
