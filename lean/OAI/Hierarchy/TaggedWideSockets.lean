import OAI.Hierarchy.TaggedWideMenu
import OAI.Hierarchy.CatalystSubstitutionHost
import OAI.Hierarchy.CorrectionFrame

namespace OAI
/-! # Fixed numbered bank and control sockets of the wide host -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst CatalystSubstitution CorrectionFrame
open scoped BigOperators

namespace ShorterBank
def target (b : ShorterBank) (F : Type*) [Field F] :=
  dataProduct b.copies (coeff F b.height b.payload)

end ShorterBank

/-- The host presents one product socket per batch. Control occurrences already
carry their width-one approximations at their actual taller heights. -/
def bankCalls {F : Type*} [Field F] {k n : ℕ} (B : Fin n → ShorterBank)
    (Y : ∀ i, (B i).Output F k) (controls : List (Occurrence F k)) : List (Occurrence F k) :=
  List.ofFn (fun i => ⟨_,(B i).target F,Y i⟩) ++ controls

/-- Each stable sort may expose its address-width slices separately as controls. -/
def controlCalls {F : Type*} [Field F] {k c : ℕ} (height : Fin c → ℕ)
    (Z : ∀ i,Approximation F k (pins (height i) (height i))) : List (Occurrence F k) :=
  List.ofFn (fun i => ⟨_,coeff F (height i) (height i),Z i⟩)

end Hierarchy.Tagged

end
end OAI
