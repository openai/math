import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinUniformCover
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-! # Pinning a finite map inside the universal spherical-map polynomial

A vertex guesses its name in a prescribed rooted map and checks its own type.
Each wire compares both endpoint names and both port numbers with a target wire.
The only surviving map class is the prescribed isomorphism class, with a unique
decoration. Its weight is exactly the contraction of the given named tables.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace GridPin

open UniformDecorations PortGraph

variable {V E W D K : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W]
  {s : ℕ}

/-- A target vertex name fits in the ceiling logarithm of the number of vertices. -/
private def name (W : Type*) [Fintype W] : W ↪ Bits (Nat.clog 2 (Fintype.card W)) :=
  (Fintype.equivFin W).toEmbedding.trans (Fin.castLEEmb (Nat.le_pow_clog (by decide) _))

private def readName (H : RootedMap W D) (d : Bits (Nat.clog 2 (Fintype.card W))) : W :=
  letI : Nonempty W := ⟨H.root⟩
  Function.invFun (name W) d

@[simp] private theorem readName_name (H : RootedMap W D) (v : W) :
    readName H (name W v) = v := by
  let : Nonempty W := ⟨H.root⟩
  exact Function.leftInverse_invFun (name W).injective v

variable (H : RootedMap W D)
  (T : (v : W) → (H.graph.Port v → Bits s) → K)

/-- The local name tests and the table indexed by the decoded vertex. -/
def pinSpec [Zero K] : Spec K s (Nat.clog 2 (Fintype.card W)) where
  vertexOK θ d := name W (readName H d) = d ∧ θ = H.typeAt (readName H d)
  edgeOK a b := ∃ e : D,
    readName H a.1 = H.graph.vertex e false ∧ a.2.2.val = H.portNumber e false ∧
    readName H b.1 = H.graph.vertex e true ∧ b.2.2.val = H.portNumber e true
  tensor θ d x :=
    let v := readName H d
    if h : (H.typeAt v).degree.val = θ.degree.val then
      T v (fun p => x ((H.num v p).cast h))
    else 0

/-- Looking up the named entry preserves any formula weight bound. -/
theorem pinSpec_tensor_hasFormula {I F : Type*} [Field F]
    (T : (v : W) → (H.graph.Port v → Bits s) → MvPolynomial I F)
    {B : ℕ} (hB : 1 ≤ B) (hT : ∀ v x, PlanarPatch.HasFormula B (T v x))
    (θ : MapType) (d : Bits (Nat.clog 2 (Fintype.card W))) (x : Fin θ.degree.val → Bits s) :
    PlanarPatch.HasFormula B ((pinSpec H T).tensor θ d x) := by
  dsimp only [pinSpec]
  split
  · exact hT ..
  · simpa using (PlanarPatch.HasFormula.const (I := I) (0 : F)).mono hB

variable [CommSemiring K]

private theorem valid_iff_iso (M : RootedMap V E) (d : V → Bits (Nat.clog 2 (Fintype.card W))) :
    (pinSpec H T).Valid (view M) d ↔ ∃ f : M.Iso H, ∀ v, d v = name W (f.vertex v) := by
  constructor
  · rintro ⟨hv,he⟩
    let f v := readName H (d v)
    have types (v : V) : M.typeAt v = H.typeAt (f v) := (hv v).2
    have edge (e : E) : ∃ e' : D, ∀ b, f (M.graph.vertex e b) = H.graph.vertex e' b ∧
        M.portNumber e b = H.portNumber e' b := by
      obtain ⟨e', ht, hnt, hh, hnh⟩ := he e
      exact ⟨e', fun b => by cases b <;> first | exact ⟨ht,hnt⟩ | exact ⟨hh,hnh⟩⟩
    choose g hg using edge
    exact ⟨isoOfLocal f g types (fun e b => (hg e b).1) (fun e b => (hg e b).2),
      fun v => (hv v).1.symm⟩
  · rintro ⟨f, hd⟩
    constructor
    · intro v
      change name W (readName H (d v)) = d v ∧ M.typeAt v = H.typeAt (readName H (d v))
      rw [hd, readName_name]
      exact ⟨rfl,typeAt_iso f v⟩
    · intro e
      refine ⟨f.edge e, ?_, f.number e false, ?_, f.number e true⟩
      · change readName H (d (M.graph.vertex e false)) = _
        rw [hd, readName_name, f.incidence]
      · change readName H (d (M.graph.vertex e true)) = _
        rw [hd, readName_name, f.incidence]

private theorem pinSpec_tensor_name (v : W) (x : H.graph.Port v → Bits s) :
    (pinSpec H T).tensor (H.typeAt v) (name W v) (fun i => x ((H.num v).symm i)) = T v x := by
  exact atName _ v (readName_name H v) x
where
  atName (d : Bits (Nat.clog 2 (Fintype.card W))) (v : W) (h : readName H d = v)
      (x : H.graph.Port v → Bits s) :
      (pinSpec H T).tensor (H.typeAt v) d (fun i => x ((H.num v).symm i)) = T v x := by
    subst v
    simp [pinSpec]
    apply congrArg (T _)
    funext p
    exact congrArg x ((H.num _).symm_apply_apply p)

private theorem eval_pinSpec_self : eval H (pinSpec H T).compiled =
    H.graph.contraction (A := fun _ => Bits s) T := by
  have valid (d : W → Bits (Nat.clog 2 (Fintype.card W))) :
      (pinSpec H T).Valid (view H) d ↔ d = name W := by
    rw [valid_iff_iso]
    constructor
    · rintro ⟨f,hf⟩
      obtain rfl : f = .refl H := Subsingleton.elim _ _
      exact funext hf
    · rintro rfl
      exact ⟨.refl H, fun _ => rfl⟩
  unfold eval
  rw [Spec.contraction_compiled]
  simp only [valid, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold Spec.decoratedContraction
  congr 1
  exact funext fun v => funext fun x => pinSpec_tensor_name H T v x

/-- In the sum over spherical map classes, only the prescribed map contributes.
Its unique valid decoration evaluates the original named contraction. -/
theorem Z_pinSpec [DecidableEq D] {N : ℕ} (hN : Fintype.card W ≤ N) (hs : H.Spherical) :
    Z N _ (pinSpec H T).compiled = H.graph.contraction (A := fun _ => Bits s) T := by
  classical
  let c := H.toClass hN hs
  unfold Z
  rw [Finset.sum_eq_single c]
  · change classEval (Quotient.mk _ (H.toRep hN hs)) _ = _
    rw [classEval_mk, ← eval_iso (H.toRepIso hN hs)]
    exact eval_pinSpec_self H T
  · intro a _ hne
    rw [classEval_out]
    unfold eval
    rw [Spec.contraction_compiled]
    apply Finset.sum_eq_zero
    intro d _
    apply ite_eq_right_iff.mpr
    intro hv
    exfalso
    obtain ⟨f,_⟩ := (valid_iff_iso H T _ _).mp hv
    apply hne
    rw [← Quotient.out_eq a]
    exact (MapClass.eq_iff_iso a.out _).mpr ⟨f.trans (H.toRepIso hN hs)⟩
  · simp

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
