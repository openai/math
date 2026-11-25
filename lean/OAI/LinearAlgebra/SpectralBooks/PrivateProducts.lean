import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.BookRaw
import OAI.LinearAlgebra.SpectralBooks.StretchProducts
import OAI.LinearAlgebra.SpectralBooks.TrivialSlots

/-! # Private products in the proof of doubling

We keep a coefficient tensor in its actual private format. Multiplication
pairs the local indices on its occupied side and leaves one-dimensional
slots everywhere else. This identifies the private classes with additive
submonoids of the nonzero tensor products on all sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor.BookFactors

open PermutationStretch Foundation
open scoped Classical BigOperators

variable (K : Type*) [Field K] (B C O : Type) [Fintype B] [Fintype C] [Fintype O]

/-- A nonzero coefficient tensor occupying the center and one list of sites. -/
structure PrivateData where
  Center : Type
  Leg : B → Type
  finiteCenter : Fintype Center
  finiteLeg : ∀ b, Fintype (Leg b)
  coeff : Center → (∀ b, Leg b) → K
  coeff_ne : coeff ≠ 0

attribute [instance] PrivateData.finiteCenter PrivateData.finiteLeg

variable {K B C O}

/-- Insert scalar slots at all auxiliary sites, preserving nonvanishing. -/
def bookProduct {U : Type} {X : B → Type} {Y : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (O : Type) [Fintype O] (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (hT : T ≠ 0) :
    NonzeroProduct (BookSite B C ⊕ O) K :=
  Additive.ofMul ⟨ofRaw (Raw.withTrivial O (bookRaw T)), by
    change ofRaw (Raw.withTrivial O (bookRaw T)) ≠ 0
    rw [ne_eq, ofRaw_eq_zero_iff]
    intro he
    apply (bookRaw_coeff_ne_zero_iff T).mpr hT
    funext a
    exact congrFun he ((Raw.withTrivialIndex O (bookRaw T)).symm a)⟩

/-- The class of the binary diagonal occupied by both private sides. -/
def jointDiagonal (K : Type*) [Field K] (B C O : Type) [Fintype B] [Fintype C] [Fintype O] :
    NonzeroProduct (BookSite B C ⊕ O) K :=
  bookProduct O (diagAll (K := K) B C (Fin 2)) fun h => by
    simpa [diagAll, diagonalCoeff] using congrFun (congrFun (congrFun h 0) (fun _ => 0)) (fun _ => 0)

namespace PrivateData

/-- The private unit, with a one-dimensional slot at each occupied site. -/
def unit (K : Type*) [Field K] (B : Type) : PrivateData K B where
  Center := Unit
  Leg := fun _ => Unit
  finiteCenter := inferInstance
  finiteLeg _ := inferInstance
  coeff := fun _ _ => 1
  coeff_ne h := one_ne_zero (congrFun (congrFun h ()) (fun _ => ()))

/-- A product of two private tensors is still a private tensor. -/
def mul (P Q : PrivateData K B) : PrivateData K B where
  Center := P.Center × Q.Center
  Leg b := P.Leg b × Q.Leg b
  finiteCenter := inferInstance
  finiteLeg _ := inferInstance
  coeff u x := P.coeff u.1 (fun b => (x b).1) * Q.coeff u.2 (fun b => (x b).2)
  coeff_ne := by
    obtain ⟨p, x, hx⟩ : ∃ p x, P.coeff p x ≠ 0 := by
      by_contra! h
      exact P.coeff_ne (funext fun u => funext (h u))
    obtain ⟨q, y, hy⟩ : ∃ q y, Q.coeff q y ≠ 0 := by
      by_contra! h
      exact Q.coeff_ne (funext fun u => funext (h u))
    intro hz
    exact (mul_ne_zero hx hy) (congrFun (congrFun hz (p,q)) (fun b => (x b, y b)))

/-- Embed a tensor on the first private side on all sites. -/
def left (O C : Type) [Fintype O] [Fintype C] (P : PrivateData K B) :
    NonzeroProduct (BookSite B C ⊕ O) K :=
  bookProduct O (placeB C P.coeff) fun h => P.coeff_ne
    (funext fun u => funext fun x => congrFun (congrFun (congrFun h u) x) (fun _ => ()))

/-- Embed a tensor on the second private side on all sites. -/
def right (O B : Type) [Fintype O] [Fintype B] (Q : PrivateData K C) :
    NonzeroProduct (BookSite B C ⊕ O) K :=
  bookProduct O (placeC B Q.coeff) fun h => Q.coeff_ne
    (funext fun u => funext fun y => congrFun (congrFun (congrFun h u) (fun _ => ())) y)

@[simp] theorem left_unit :
    left O C (unit K B) = 0 := by
  apply Additive.ext <| Subtype.ext ?_
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (X := Raw.withTrivial O (bookRaw (placeB C (unit K B).coeff)))
    (Y := Raw.one (BookSite B C ⊕ O) K)
    (fun i => ?_)
  · intro a; rfl
  · rcases i with ((_ | (_ | _)) | _) <;> exact Equiv.refl _

@[simp] theorem right_unit :
    right O B (unit K C) = 0 := by
  apply Additive.ext <| Subtype.ext ?_
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (X := Raw.withTrivial O (bookRaw (placeC B (unit K C).coeff)))
    (Y := Raw.one (BookSite B C ⊕ O) K)
    (fun i => ?_)
  · intro a; rfl
  · rcases i with ((_ | (_ | _)) | _) <;> exact Equiv.refl _

@[simp] theorem left_mul (P Q : PrivateData K B) :
    left O C (P.mul Q) = left O C P + left O C Q := by
  apply Additive.ext <| Subtype.ext ?_
  let X := Raw.withTrivial O (bookRaw (placeB C (mul P Q).coeff))
  let Y := (Raw.withTrivial O (bookRaw (placeB C P.coeff))).mul
    (Raw.withTrivial O (bookRaw (placeB C Q.coeff)))
  change ofRaw X = ofRaw Y
  let e (i : BookSite B C ⊕ O) : X.Leg i ≃ Y.Leg i := by
    rcases i with ((_ | (_ | _)) | _)
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Equiv.prodUnique Unit Unit).symm
    · exact (Equiv.prodUnique PUnit PUnit).symm
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent e fun _ => rfl)

@[simp] theorem right_mul (P Q : PrivateData K C) :
    right O B (P.mul Q) = right O B P + right O B Q := by
  apply Additive.ext <| Subtype.ext ?_
  let X := Raw.withTrivial O (bookRaw (placeC B (mul P Q).coeff))
  let Y := (Raw.withTrivial O (bookRaw (placeC B P.coeff))).mul
    (Raw.withTrivial O (bookRaw (placeC B Q.coeff)))
  change ofRaw X = ofRaw Y
  let e (i : BookSite B C ⊕ O) : X.Leg i ≃ Y.Leg i := by
    rcases i with ((_ | (_ | _)) | _)
    · exact Equiv.refl _
    · exact (Equiv.prodUnique Unit Unit).symm
    · exact Equiv.refl _
    · exact (Equiv.prodUnique PUnit PUnit).symm
  exact ofRaw_eq_iff.mpr (Raw.reindex_equivalent e fun _ => rfl)

end PrivateData

/-- The submonoid of products of any number of binary joint diagonals and
private tensors. It is used only after adjoining one more binary diagonal. -/
def targetProducts (K : Type*) [Field K] (B C O : Type) [Fintype B] [Fintype C] [Fintype O] :
    AddSubmonoid (NonzeroProduct (BookSite B C ⊕ O) K) where
  carrier := {t | ∃ n : ℕ, ∃ (p : PrivateData K B) (q : PrivateData K C),
    t = n • jointDiagonal K B C O + p.left O C + q.right O B}
  zero_mem' := ⟨0, PrivateData.unit K B, PrivateData.unit K C, by simp⟩
  add_mem' := by
    rintro _ _ ⟨n, p, q, rfl⟩ ⟨m, p', q', rfl⟩
    refine ⟨n+m, p.mul p', q.mul q', ?_⟩
    simp only [add_nsmul, PrivateData.left_mul, PrivateData.right_mul]
    abel

theorem left_mem (p : PrivateData K B) : p.left O C ∈ targetProducts K B C O :=
  ⟨0, p, PrivateData.unit K C, by simp⟩

theorem right_mem (q : PrivateData K C) : q.right O B ∈ targetProducts K B C O :=
  ⟨0, PrivateData.unit K B, q, by simp⟩

theorem diagonal_mem : jointDiagonal K B C O ∈ targetProducts K B C O :=
  ⟨1, PrivateData.unit K B, PrivateData.unit K C, by simp⟩

/-- Every positive power of a target has a positive diagonal exponent and
one private tensor on each side. -/
theorem power_target {x : NonzeroProduct (BookSite B C ⊕ O) K}
    (hx : x ∈ targetProducts K B C O) {m : ℕ} (hm : 0 < m) :
    ∃ k : ℕ, 0 < k ∧ ∃ (p : PrivateData K B) (q : PrivateData K C),
      m • (jointDiagonal K B C O + x) = k • jointDiagonal K B C O + p.left O C + q.right O B := by
  have hmx := (targetProducts K B C O).nsmul_mem hx m
  obtain ⟨n, p, q, h⟩ := hmx
  refine ⟨m + n, Nat.add_pos_left hm _, p, q, ?_⟩
  rw [nsmul_add, h, add_nsmul]
  abel

end SiteTensor.BookFactors

end

end SpectralBooks
end LinearAlgebra
end OAI
