import OAI.Hierarchy.DescentBoundedBitHistory
import OAI.Hierarchy.DescentRecipeFootprint

namespace OAI
/-! # Bit histories read genuine network inputs -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
def boundaryRead {D : ℕ} {E : Type} {ew : E→ℕ} (A : Network D E ew) (a : A.Assignment) (p : Ports ew)
    (v : A.Site) (r : Boundary A v) : Word (boundaryWidth A v r) :=
  match r with | .inl e=>a e.val | .inr q=>p q.val

abbrev SiteBits {D : ℕ} {E U : Type} {w : E→ℕ} (A : Network D E w) := ∀v : A.Site,BitRecipe U (Boundary A v) (boundaryWidth A v)
def bitInput {D : ℕ} {E : Type} {w : E→ℕ} (A : Network D E w) (a : A.Assignment) (p : Ports w) (v : A.Site)
    (z : BitRef (boundaryWidth A v)) := boundaryRead A a p v z.1 z.2

def ReadsBits {D : ℕ} {E U : Type} {w : E→ℕ} (A : Network D E w) (scalar : U→List (List Bool)→F)
    (hist : SiteBits (U:=U) A) (tbl : A.Tables F) :=
  ∀a p v,(hist v).value scalar (bitInput A a p v)=A.read tbl a p v

theorem expose_reads {D : ℕ} {E U : Type} {w : E→ℕ} (A : Network D E w) (s : U→List (List Bool)→F)
    (tbl : A.Tables F) (r : ∀v,Recipe U (Boundary A v)) (rep : Represents A s tbl r) :
    ReadsBits A s (fun v=>BitRecipe.expose (r v) (boundaryWidth A v)) tbl := by
  intro a p v
  rw [show bitInput A a p v=(fun z=>boundaryRead A a p v z.1 z.2) from rfl,BitRecipe.expose_eval]
  have ports :
      (fun q=>wordList (boundaryRead A a p v q)) =
        input A (fun e=>a e.val) (fun q : Attached A v=>p q.val) := by
    funext q
    cases q <;> rfl
  rw [ports]
  exact rep v (fun e=>a e.val) (fun q=>p q.val)

end
end Hierarchy.DescentKernelHistory

end OAI
