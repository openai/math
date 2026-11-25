import OAI.Computability.NearSquareRoot.InterchangeRationalVerifier

/-! # A complete finite equality test for two P192 address programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.AddressROM

open IntegerMultiplication.Port

variable {J : Type} [DecidableEq J] {b : ℕ} {R : Type} [CommRing R]

private noncomputable def linearStep (f : ℕ) (op : Lag J b) :
    (Spot J → Tower b f) →ₗ[Tower b f] (Spot J → Tower b f) :=
  let get (i : Spot J) := LinearMap.proj (R:=Tower b f) (φ:=fun _ : Spot J => Tower b f) i
  LinearMap.pi fun t => match op with
    | .width a s => if t = a then s.land f • get a else get t
    | .gather a k s => if t = a then get a + s.stamp f • get k else get t
    | .pivot h d => get ((Equiv.swap (false,h) (true,d)) t)

private theorem linearStep_apply (f : ℕ) (op : Lag J b) (x : Duplex J (Tower b f)) :
    linearStep f op (hear x) = hear (op.fire f x) := by
  funext t
  cases op with
  | width a s =>
    by_cases e : t = a <;> simp [linearStep,Lag.fire,e]
  | gather a k s =>
    by_cases e : t = a <;> simp [linearStep,Lag.fire,e]
  | pivot h d =>
    by_cases e : t = (false,h)
    · subst t; simp [linearStep,Lag.fire]
    by_cases g : t = (true,d)
    · subst t; simp [linearStep,Lag.fire]
    · simp [linearStep,Lag.fire,e,g,Equiv.swap_apply_of_ne_of_ne e g]

private noncomputable def linearWord (f : ℕ) : List (Lag J b) →
    (Spot J → Tower b f) →ₗ[Tower b f] (Spot J → Tower b f)
  | [] => LinearMap.id
  | op :: ops => (linearWord f ops).comp (linearStep f op)

private theorem linearWord_apply (f : ℕ) (ops : List (Lag J b)) (x : Duplex J (Tower b f)) :
    linearWord f ops (hear x) = hear (ops.foldl (Lag.fire f) x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [linearWord,LinearMap.comp_apply,linearStep_apply,ih,List.foldl_cons]

/-- The matrix read by the finite verifier. Only rational arithmetic is used. -/
def columns (ops : List (Lag J b)) : Matrix (Spot J) (Spot J) ℚ :=
  fun i j => applyWord ops (Pi.single j 1) i

private theorem columns_token [Fintype J] (ops : List (Lag J b)) (f : ℕ) (i j : Spot J) :
    Token (columns ops i j) (LinearMap.toMatrix' (linearWord f ops) i j) := by
  rw [LinearMap.toMatrix'_apply]
  let x := duplexCoords J (Tower b f) (Pi.single j 1)
  have hx : hear x = Pi.single j 1 := funext fun _ => hear_duplexCoords _ _
  rw [← hx,linearWord_apply]
  apply applyWord_token
  intro t
  rw [hx]
  by_cases ht : t = j
  · subst t
    simpa using (Token.unit : Token 1 (1 : Tower b f))
  · simpa [Pi.single_apply,ht] using (Token.zero : Token 0 (0 : Tower b f))

/-- Equality of the two finite rational matrices is equivalent to equality of
the native action at every width, including exponent zero. -/
theorem columns_eq_iff [Fintype J] (hb : 1 < b) (ops qs : List (Lag J b)) :
    columns ops = columns qs ↔ ∀ (f : ℕ) (x : Duplex J (Tower b f)),
      ops.foldl (Lag.fire f) x = qs.foldl (Lag.fire f) x := by
  constructor
  · intro h f x
    have heq : linearWord f ops = linearWord f qs := by
      apply LinearMap.toMatrix'.injective
      ext i j
      exact ((h ▸ columns_token ops f i j) : Token (columns qs i j) _).unique
        (columns_token qs f i j)
    exact hear_all fun t => congrFun ((linearWord_apply f ops x).symm.trans <|
      (congrArg (fun h => (h : (Spot J → Tower b f) →ₗ[Tower b f] _) (hear x)) heq).trans
        (linearWord_apply f qs x)) t
  · intro h
    ext i j
    apply separated hb (v:=fun f => LinearMap.toMatrix' (linearWord f ops) i j)
      (fun f => columns_token ops f i j)
    intro f
    have eqL : linearWord f ops = linearWord f qs := by
      apply LinearMap.ext
      intro x
      have hd : hear (duplexCoords J (Tower b f) x) = x := funext fun _ => hear_duplexCoords _ _
      rw [← hd,linearWord_apply,linearWord_apply,h]
    rw [eqL]
    exact columns_token qs f i j

def equal [Fintype J] (ops qs : List (Lag J b)) : Bool :=
  decide (columns ops = columns qs)

theorem equal_iff [Fintype J] (hb : 1 < b) (ops qs : List (Lag J b)) :
    equal ops qs = true ↔ ∀ (f : ℕ) (x : Duplex J (Tower b f)),
      ops.foldl (Lag.fire f) x = qs.foldl (Lag.fire f) x :=
  decide_eq_true_iff.trans (columns_eq_iff hb ops qs)

end Interchange.AddressROM

end NearSquareRoot
end Computability
end OAI
