import OAI.Computability.NearSquareRoot.InterchangeSpectralPacked
import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# Spectral sweeps on ground-alphabet rows

The inverse of two in the repair extension is the image of the inverse of two
in the ground ring. Consequently every coordinate of an extension check row
has its own ordinary ground-ring sweep, including both ends of fixed orbits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralComponents

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeSpectralRequest SwapRepair

variable {K J : Type} [CommRing K] [Nontrivial K] [DecidableEq J] {m : ℕ}

omit [Nontrivial K] in
theorem invRadix_eq (e : Environment K m) (half : K) (hh : 2 * half = 1) :
    e.invRadix = algebraMap K (Coeff K m) half := by
  have h₁ : (2 : Coeff K m) * algebraMap K (Coeff K m) half = 1 := by
    rw [two_mul] at hh ⊢
    simpa only [map_add, map_one] using congrArg (algebraMap K (Coeff K m)) hh
  have h₂ : e.invRadix * (2 : Coeff K m) = 1 := by simpa using e.invRadix_mul
  calc
    e.invRadix = e.invRadix * (2 * algebraMap K (Coeff K m) half) := by rw [h₁, mul_one]
    _ = _ := by rw [← mul_assoc, h₂, one_mul]

/-- The ordinary inverse in a ground field satisfies the normalization needed
for every pass whenever a repair environment exists over that field. -/
theorem ground_half {F : Type} [Field F] (e : Environment F m) : (2 : F) * 2⁻¹ = 1 := by
  apply mul_inv_cancel₀
  intro h
  have zero_ext : (2 : Coeff F m) = 0 := by
    rw [show (2 : Coeff F m) = 1 + 1 by norm_num]
    rw [show (2 : F) = 1 + 1 by norm_num] at h
    simpa only [map_add, map_one, map_zero] using congrArg (algebraMap F (Coeff F m)) h
  have hh : e.invRadix * (2 : Coeff F m) = 1 := by simpa using e.invRadix_mul
  rw [zero_ext, mul_zero] at hh
  let : Nontrivial (Coeff F m) :=
    OAI.LinearAlgebra.FiniteFourier.primeCyclotomicExtension_nontrivial (p:=2) (-1 : F) _
  exact zero_ne_one hh

theorem value_component (e : Environment K m) (half : K) (hh : 2 * half = 1)
    (inv : Bool) (tag : Ordering) (x y : Coeff K m) (d : BasisIndex m) :
    components K m (InterchangeSpectralStep.value inv e.invRadix tag x y) d =
      InterchangeSpectralStep.value inv half tag (components K m x d) (components K m y d) := by
  have hc (v : Coeff K m) : components K m (e.invRadix * v) d = half * components K m v d := by
    rw [invRadix_eq e half hh, ← Algebra.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
  cases inv <;> cases tag <;> simp [InterchangeSpectralStep.value, neg_mul, hc]

theorem advance_component {b f : ℕ} {P G B : Dims.Tape} (e : Environment K m)
    (half : K) (hh : 2 * half = 1) (inv : Bool) (j : J) (d : BasisIndex m)
    (x : Keys P G B J (Block b f) → Coeff K m) (a : Keys P G B J (Block b f)) :
    components K m (advance inv e.invRadix j x a) d =
      advance inv half j (fun z => components K m (x z) d) a :=
  value_component e half hh inv _ _ _ d

/-- Project a complete list of physical conversion steps onto one basis row.
The same identity applies when the inverse pass receives the reversed field list. -/
theorem fold_component {b f : ℕ} {P G B : Dims.Tape} (e : Environment K m)
    (half : K) (hh : 2 * half = 1) (inv : Bool) (fields : List J) (d : BasisIndex m)
    (x : Keys P G B J (Block b f) → Coeff K m) :
    (fun a => components K m ((fields.foldl (fun y j => advance inv e.invRadix j y) x) a) d) =
      fields.foldl (fun y j => advance inv half j y) (fun a => components K m (x a) d) := by
  induction fields generalizing x with
  | nil => rfl
  | cons j fields ih =>
    simp only [List.foldl_cons]
    rw [ih]
    rw [funext (advance_component e half hh inv j d x)]

variable {I A : Type} {D : I → Type} {r : Regime I} {b n : ℕ}

/-- Store each ground coordinate of each extension check in a separate stream.
Each record retains its full contiguous payload. -/
noncomputable def componentBank {X : I → Type} (records : (i : I) → Series (X i)) (payload : (i : I) → Series (D i))
    (rows : Series (A × BasisIndex m)) (digit : K → Tree)
    (x : (i : I) → A → X i × D i → Coeff K m) : I → Tree :=
  InterchangePayloadBank.render records payload rows digit
    (fun i s z => components K m (x i s.1 z) s.2)

/-- The actual P192 conversion of a bank of extension checks through the
ground alphabet. Each field bills one recursive request per check and basis
coordinate. All positions of the contiguous payload travel in that request. -/
theorem charged [NeZero b] [Finite K] [Fintype A] (ord : J ≃ Fin n) (P G B : I → Dims.Tape)
    (f l : I → ℕ) (payload : (i : I) → Series (D i)) (rows : Series (A × BasisIndex m))
    (digit : K → Tree) (hd : Function.Injective digit)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (hw : ∀ i, (payload i).count ≤ l i) (e : Environment K m)
    (half : K) (hh : 2 * half = 1) (inv : Bool) (fields : List J)
    (x : (i : I) → A → domain (J:=J) (b:=b) P G B f i × D i → Coeff K m) :
    let sweep := fun i a (z : domain (J:=J) (b:=b) P G B f i × D i) =>
      fields.foldl (fun y j => advance inv e.invRadix j y) (fun k => x i a (k,z.2)) z.1
    let render := componentBank (layoutRows ord P G B f) payload rows digit
    ChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
      (Fintype.card A * Fintype.card (BasisIndex m) * fields.length) (render x) (render sweep) := by
  intro sweep render
  let records := layoutRows (b:=b) ord P G B f
  let row (u : (i : I) → A → domain (J:=J) (b:=b) P G B f i × D i → Coeff K m) i
      (s : A × BasisIndex m) :=
    stripe (records i) (fun k => stripe (payload i) (fun d => digit (components K m (u i s.1 (k,d)) s.2)))
  have st := layoutRows_station (b:=b) ord P G B f hb hf hp hg hs
  have live (u : (i : I) → A → domain (J:=J) (b:=b) P G B f i × D i → Coeff K m)
      (s : A × BasisIndex m) : Alive r (countRows (b:=b) ord P G B f) l (fun i => row u i s) :=
    (InterchangePayloadBank.manifest payload digit (fun i z => components K m (u i s.1 z) s.2) hw).lives st
  have run (s : A × BasisIndex m) :
      ChargedTyped (r:=r) (l:=l) (b:=b) ord P G B f (InterchangePayloadBank.Good payload digit)
        fields.length (fun i => row x i s) (fun i => row sweep i s) := by
    let v i d a := components K m (x i s.1 (a,d)) s.2
    let base := fun i d => fields.foldl (fun y j => advance inv half j y) (v i d)
    have hv (i d) : (fun a => components K m (sweep i s.1 (a,d)) s.2) = base i d :=
      fold_component e half hh inv fields s.2 (fun a => x i s.1 (a,d))
    have hx := InterchangeSpectralPacked.charged ord P G B f payload digit hb hf hp hg hs
      l hw hd inv half fields v
    have hout : (fun i => row sweep i s) =
        stackRun records (InterchangeSpectralPacked.pack P G B f payload digit base) := by
      funext i
      apply congrArg (stripe (records i))
      funext a
      apply congrArg (stripe (payload i))
      funext d
      exact congrArg digit (congrFun (hv i d) a)
    rw [hout]
    exact hx
  have all := InterchangeBank.collect st.1 rows rows (row x) (row sweep) id (fun _ => fields.length)
    (live x) (live sweep) run
  have eqn (v) : render v = stackRun (fun _ => rows) (row v) := rfl
  rw [eqn, eqn]
  unfold ChargedTyped
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul] using all

end InterchangeSpectralComponents

end NearSquareRoot
end Computability
end OAI
