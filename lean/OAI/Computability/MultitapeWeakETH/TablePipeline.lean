import OAI.Computability.MultitapeWeakETH.Contraction

/-! # Composing field tables with auxiliary processor wires

The old graph and its additional wires share sites. Summing the intermediate
output indices at each site gives a single table on the union of the wires.
This allows the known singleton slices to be substituted before summing
the borrow and folded-output labels.
-/

namespace OAI.Computability.MultitapeWeakETH.TablePipeline

open VPVNP.WireTensor Finset
open scoped Classical
noncomputable section

variable {K J E H : Type} [Field K] [Fintype J] [Fintype E] [Fintype H]
    (a b : E → J) (c d : H → J) (U : E → Type) (W : H → Type)
    [∀ e, Fintype (U e)] [∀ h, Fintype (W h)]

def Alphabet : E ⊕ H → Type := Sum.elim U W
instance (e : E ⊕ H) : Fintype (Alphabet U W e) :=
  match e with | .inl i => inferInstanceAs (Fintype (U i)) | .inr i => inferInstanceAs (Fintype (W i))

abbrev combined := wireNetwork (k:=K) (Sum.elim a c) (Sum.elim b d) (Alphabet U W)

def left (j : J) (wire : (combined a b c d U W (K:=K)).Basis j) :
    (wireNetwork (k:=K) a b U).Basis j :=
  ⟨fun e h => wire.1 (.inl e) h,fun e h => wire.2 (.inl e) h⟩

def right (j : J) (wire : (combined a b c d U W (K:=K)).Basis j) :
    (wireNetwork (k:=K) c d W).Basis j :=
  ⟨fun e h => wire.1 (.inr e) h,fun e h => wire.2 (.inr e) h⟩

private def splitLabels :
    ((e : E ⊕ H) → Alphabet U W e) ≃ ((h : H) → W h) × ((e : E) → U e) where
  toFun s := (fun h => s (.inr h),fun e => s (.inl e))
  invFun s e := match e with | .inl i => s.2 i | .inr i => s.1 i
  left_inv s := by funext e; cases e <;> rfl
  right_inv _ := rfl

variable {X Z : J → Type} [∀ j, Fintype (X j)]
    (first : ∀ j, X j → (wireNetwork (k:=K) a b U).Basis j → K)
    (next : ∀ j, Z j → X j → (wireNetwork (k:=K) c d W).Basis j → K)

def localMap (j : J) (z : Z j) (wire : (combined a b c d U W (K:=K)).Basis j) : K :=
  ∑ x, next j z x (right a b c d U W j wire) * first j x (left a b c d U W j wire)

theorem contract (z : ∀ j, Z j) :
    applyLocal (localMap a b c d U W first next) (combined a b c d U W).coeff z =
      ∑ h : (i : H) → W i, applyLocal
        (fun j y x => next j y x (edgeAssignment c d h j))
        (applyLocal first (wireNetwork a b U).coeff) z := by
  simp_rw [applyLocal_comp]
  rw [applyLocal_wireNetwork]
  simp_rw [applyLocal_wireNetwork]
  rw [← Fintype.sum_prod_type']
  let _ : DecidableEq (E ⊕ H) := Classical.decEq _
  apply Fintype.sum_equiv (splitLabels U W)
  intro s
  rfl

/-- On a singleton slice, the field scalar factors out, leaving exactly
the sum over the auxiliary processor labels evaluated on that slice. -/
theorem contract_singleton (out : ∀ j, X j) (scalar : K)
    (support : applyLocal first (wireNetwork a b U).coeff =
      fun x => if x = out then scalar else 0) (z : ∀ j, Z j) :
    applyLocal (localMap a b c d U W first next) (combined a b c d U W).coeff z =
      (∑ h : (i : H) → W i, ∏ j, next j (z j) (out j) (edgeAssignment c d h j)) * scalar := by
  rw [contract,support]
  simp only [applyLocal,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true,sum_mul]

/-- A deterministic set of local processor tests on a singleton input
slice contributes its scalar once. This also permits many zero coefficients
inside the original field-valued network. -/
theorem unique_processor (out : ∀ j, X j) (scalar : K)
    (support : applyLocal first (wireNetwork a b U).coeff =
      fun x => if x = out then scalar else 0)
    (legal : ∀ j, X j → (wireNetwork (k:=K) c d W).Basis j → Prop)
    (read : ∀ j, X j → (wireNetwork (k:=K) c d W).Basis j → Z j)
    (chosen : (h : H) → W h)
    (unique : ∀ labels, (∀ j, legal j (out j) (edgeAssignment c d labels j)) ↔ labels = chosen) :
    applyLocal (localMap a b c d U W first (fun j z x wire =>
      if legal j x wire ∧ z = read j x wire then 1 else 0)) (combined a b c d U W).coeff =
      fun z => if z = (fun j => read j (out j) (edgeAssignment c d chosen j)) then scalar else 0 := by
  funext z
  rw [contract_singleton _ _ _ _ _ _ _ _ _ _ support]
  simp only [Fintype.prod_boole,forall_and,unique,← funext_iff]
  rw [sum_eq_single chosen]
  · simp
  · intro labels _ ne
    simp [ne]
  · simp

/-- Typed labels can be sent through a binary wire with any larger alphabet.
Selecting the encoded endpoint indices preserves the exact equality checks
at loops as well as at distinct sites. -/
theorem restrict_alphabets (small big : E → Type) [∀ e, Fintype (small e)] [∀ e, Fintype (big e)]
    (encode : (e : E) → small e ↪ big e) :
    Restricts (wireNetwork (k:=K) a b big) (wireNetwork a b small) := by
  let lift (j : J) (x : (wireNetwork (k:=K) a b small).Basis j) :
      (wireNetwork (k:=K) a b big).Basis j :=
    ⟨fun e h => encode e (x.1 e h),fun e h => encode e (x.2 e h)⟩
  refine ⟨fun j x y => if lift j x = y then 1 else 0,?_⟩
  rw [applyLocal_pullback]
  funext x
  simp only [wireNetwork,lift,Function.Embedding.apply_eq_iff_eq]

end
end OAI.Computability.MultitapeWeakETH.TablePipeline
