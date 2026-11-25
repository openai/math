import OAI.Computability.BorderVNP.ShortenPackMotionMeanMeasure
import OAI.Computability.BorderVNP.CoverPackBins

/-!
# Marginal counts of the actual quaternion and deck motions

One sample chooses a speed permutation, a Hecke word in each factor, and a
uniform deck post-translation. The same sample moves every cable in its pack.
The bin tag of a particular charged cable uses its own source frame and carry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PackMotions

open Cover Cover.Frame Hecke Epoch Crossing MeasureTheory Set
open scoped Classical BigOperators

variable {D copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} {B I : Type} [Fintype I]
variable (input : Fin copies → Pack D P bits K) (charged : ∀ i, (input i).layout.Edge → Bool)
variable {depth n : ℕ}

/-- Real probability used for each whole-pack sample, identical for all input copies. -/
noncomputable def sampleProb (depth n : ℕ) (_i : Fin copies) (s : PackSample (lattice 1) elliptic I depth n) : ℝ :=
  (packWeight (lattice 1) elliptic s : ℝ)

/-- The finite weights used on each pack are positive and normalized. -/
theorem sampleProb_probability (depth n : ℕ) (i : Fin copies) :
    (∀ s, 0 < sampleProb (I := I) depth n i s) ∧ ∑ s, sampleProb (I := I) depth n i s = 1 := by
  unfold sampleProb
  constructor
  · intro s
    exact_mod_cast packWeight_pos (lattice 1) elliptic s
  · exact_mod_cast sum_packWeight (lattice 1) elliptic (I := I) depth n

variable (speed : Active input charged → I → ℝ)
variable (code : Active input charged → HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) → B)
variable (frame : Active input charged → Equiv.Perm I → I → SL)
variable (carry : Active input charged → Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck depth)

/-- The moved cable's actual destination deck address and relative configuration bin. -/
noncomputable def sampleAddress (w : Active input charged) (s : PackSample (lattice 1) elliptic I depth n) :
    (I → Deck depth) × B :=
  (shiftedAddress s.2.2 (carry w s.1 s.2.1),
    code w (segmentChart (speed w) s.1 (productPoint (lattice 1) elliptic n (frame w s.1) s.2.1)))

/-- The sample tags precisely the active old cables. -/
noncomputable def sampledBin (i : Fin copies) (s : PackSample (lattice 1) elliptic I depth n)
    (e : (input i).layout.Edge) : Option ((I → Deck depth) × B) :=
  if h : charged i e then some (sampleAddress input charged speed code frame carry ⟨i,e,h⟩ s) else none

omit [Fintype I] in
/-- Sampling preserves the old charge mask, including frozen cables. -/
theorem sampledBin_mask (i : Fin copies) (s : PackSample (lattice 1) elliptic I depth n)
    (e : (input i).layout.Edge) : (sampledBin input charged speed code frame carry i s e).isSome = charged i e := by
  cases hc : charged i e <;> simp [sampledBin, hc]

/-- A charged cable's exact sample law is the geometric address mass from the Hecke estimate. -/
theorem finiteWireLaw_eq_actualBinMass (w : Active input charged) (a : (I → Deck depth) × B) :
    finiteWireLaw input charged (sampledBin input charged speed code frame carry) (sampleProb depth n) w a =
      actualBinMass (speed w) ((code w) ⁻¹' {a.2}) (frame w) (carry w) a.1 := by
  unfold finiteWireLaw actualBinMass
  apply Finset.sum_congr rfl
  intro s _
  let tag := shiftedAddress s.2.2 (carry w s.1 s.2.1)
  let x := segmentChart (speed w) s.1 (productPoint (lattice 1) elliptic n (frame w s.1) s.2.1)
  have htag : sampledBin input charged speed code frame carry w.1 s w.2.val =
      some (tag,code w x) := by simp [sampledBin,w.2.property]; rfl
  rw [htag]
  simp only [Option.some.injEq, Set.indicator_apply, Set.mem_preimage,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  change (if (tag, code w x) = a then _ else 0) =
    if tag = a.1 then if code w x = a.2 then _ else 0 else 0
  rcases a with ⟨t,b⟩
  by_cases ht : tag = t <;> by_cases hx : code w x = b <;> simp [ht,hx,sampleProb]

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
