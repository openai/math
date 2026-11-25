import OAI.Computability.IntegerMultiplication.Brief.News
import OAI.Computability.IntegerMultiplication.Interface

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Interface Strip Code Bits Param Carry
variable {I : Type}

/-- Count length logarithmic bits and put on header in normalized-linear time, regardless of whether n sufficiently large. -/
abbrev measure (n:I→ℕ):I→ℝ := fun i=> (n i:ℝ)+1
theorem here (n:I→ℕ) (i:I) : 1 ≤ measure n i := by unfold measure; simp
variable {n:I→ℕ} (x y : I→Word)
    (p:∀ i,(x i).length=n i) (q:∀ i,(y i).length=n i)
include p q
theorem smallWords :
    Volume (measure n) (send ∘ (fun i=>(x i,y i))) := by
  refine ⟨5,fun i=>?_⟩
  change (size _:ℝ) ≤ _ * ((n i:ℝ)+1)
  rw [size_prod,size_word,size_word,p,q]
  push_cast
  linarith

theorem launch :
    let f := (send ∘ (fun i=>(x i,y i)))
    Carries (measure n) f
      (together ((journals n).header) f) := by
  let z:= smallWords x y p q
  apply Carries.twice ?_ (Carries.idles (here n) z)
  let g (x:Word×Word):Word:= born x.1.length
  have i : Easy g := by
    have v := (Easy.ruler (X:=Bool) (Easy.fst (X:=Word) (Y:=Word))).compose Carry.easy_chart
    simpa only [ruler_length] using v
  have e := Carries.func (y:=fun i=>(x i,y i)) (here n) z g i
  change Carries _ _ (fun i=> send (born (n i)))
  simpa only [g,p,journals,messenger,Function.comp_def] using e

omit q in
/-- MSB loaded are ordinary. Supply standard header orientations for large-spec task calls. -/
theorem lit :
    let f := send ∘ x
    Carries (measure n) f ((journals n).header) := by
  let z : Volume (measure n) (send ∘ x) := .left (q:=send ∘ x) (smallWords x x p p)

  have E := Carries.func (y:=x) (here n) z _ ((Easy.ruler (X:=Bool) Easy.identity).compose Carry.easy_chart)
  change Carries _ _ (fun i=> send (born (n i)))
  simpa only [id_eq,ruler_length,p,journals,messenger,Function.comp_def] using E

end Brief

end IntegerMultiplication
end Computability
end OAI
