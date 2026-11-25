import OAI.Hierarchy.CatalystSubstitutionFamily
import OAI.Hierarchy.TaggedWidthInduction

namespace OAI
/-! # Installing the physical calls of one shorter-address format -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst CatalystSubstitution
open scoped BigOperators

/-- A finite list of replacements is shared by all coefficients of the parent.
Socket multiplicity in this list counts substituted gates. Per-format work
multiplicity counts the number of physical copies inside the amplified gates. -/
def fromCallList {F : Type*} [Field F] {k h w types : ℕ} {A C G fixed : ℝ}
    (height payload multiplicity : Fin types → ℕ)
    (smaller : ∀ i,height i<h) (within : ∀ i,inRange A (height i) (payload i))
    (calls : (∀ i,Catalyst.Approximation F k (pins (height i) (payload i))) →
      List (Occurrence F k))
    (host : ∀ X, Host F k (pins h w) (Sockets (calls X)))
    (work : ∀ X,
      (hostSize (host X):ℝ) + (((calls X).map (·.replacement.size)).sum:ℝ) ≤
        fixed + ∑ i,(multiplicity i:ℝ)*((X i).size:ℝ))
    (old : ∀ X, (tableApprox (host X).width (exactValue (calls X) (host X))).Gap (coeff F h w) G)
    (children : ∀ X, (∀ i,(X i).Gap (coeff F (height i) (payload i)) (gap C (height i))) →
      ∀ o ∈ calls X,o.replacement.Gap o.target G)
    (fits : ∀ X, gap C h ≤ G-2*(k:ℝ)*((calls X).length:ℝ)) :
    ShorterCalls F k h w A C where
  types := types
  height := height
  payload := payload
  multiplicity := multiplicity
  smaller := smaller
  within := within
  fixedWork := fixed
  assemble X := install (calls X) (host X)
  size_le X := by
    have z := install_size (calls X) (host X)
    have q : (install (calls X) (host X)).size ≤
       hostSize (host X)+((calls X).map (·.replacement.size)).sum := by omega
    have sum_cast (xs : List (Occurrence F k)) :
        (((xs.map (fun o=>o.replacement.size)).sum : ℕ) : ℝ)=
          (xs.map (fun o=>(o.replacement.size:ℝ))).sum := by
      induction xs with
      | nil=>simp
      | cons o xs ih=>simp [ih]
    have scalar := (Nat.cast_le (α:=ℝ)).mpr q
    rw [Nat.cast_add,sum_cast] at scalar
    exact scalar.trans (work X)
  gap_le X good := Approximation.Gap.mono _
    (install_gap (calls X) (host X) (coeff F h w) G (old X) (children X good)) (fits X)

end Hierarchy.Tagged

end
end OAI
