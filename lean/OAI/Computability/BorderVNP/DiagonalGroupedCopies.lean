import OAI.Computability.BorderVNP.DiagonalExternalFinePack

/-! # Independent private choices inside each repeated input tile -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Tracked

open Crossing
open scoped Classical BigOperators

variable {D copies exp : ℕ} {Team Param Gadget P A H : Type}
    [Fintype Team] [Fintype Param] [Fintype H]
    {bits : P → ℕ} {N M : Network D P bits}

/-- Install named tables on a public directory proved to be the same network. -/
def castLayout (eqn : N = M) (t : Tracked Team Param Gadget exp N) :
    Tracked Team Param Gadget exp M := eqn ▸ t

/-- Installation through equality of the directory preserves all local reads. -/
theorem castLayout_tensor {E : Type*} [CommSemiring E] (eqn : N = M) (t : Tracked Team Param Gadget exp N)
    (values : Gadget → E) (x : Ports bits) :
    ((t.castLayout eqn).valued values).tensor x = (t.valued values).tensor x := by cases eqn; rfl

variable {N : Network D P (fun _ => 1)} (width : A → ℕ) (lane : P ↪ Σ a, Fin (width a)) (owner : A → N.Site)
    (aligned : ∀ p, owner (lane p).1 = N.attach p)
    (base : H → Tracked Team Param Gadget exp N)

/-- Each bottom copy has its own fine private assignment. The public directory
groups its lanes with all other copies belonging to the same physical tile. -/
noncomputable def groupedCopies (hidden : Fin copies → H) :
    Tracked (Fin copies × Team) Param Gadget exp (N.groupedRepeat width owner copies) :=
  let tags := fun i => (base (hidden i)).tags
  let pack : Tracked (Fin copies × Team) Param Gadget exp (N.repeatGrid copies) :=
    ⟨repeatedTags tags,PowerWords.repeated tags (fun i => (base (hidden i)).words)⟩
  pack.packExternal _ (Network.repeatLane width lane copies) owner (fun p => aligned p.2)

/-- Summation over the independent private bits inside one bundle gives the
product of the original single-copy contractions at the addressed lane words. -/
theorem sum_groupedCopies {E : Type*} [CommSemiring E] (values : Gadget → E)
    (x : Ports (fun a => copies*width a)) :
    (∑ z : Fin copies → H, ((groupedCopies width lane owner aligned base z).valued values).tensor x) =
      ∏ i : Fin copies, ∑ z : H, ((base z).valued values).tensor (fun p _ =>
        let a := Network.repeatLane width lane copies (i,p)
        x a.1 a.2) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro z _
  exact value_repeatedTags (fun i => (base (z i)).tags) values
    (Network.readExternal _ (Network.repeatLane width lane copies) x)

end Diagonal.CellEntries.Tracked

end BorderVNP
end Computability
end OAI
