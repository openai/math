import Mathlib.Init

/-! # Dependent continuation after a verified prefix

An issued execution takes a boot followed by its dependent time receipt.
Naming the type after these arguments allows an application to retain the
remaining native requests without expanding their dependent telescope.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

universe ua ub uc

/-- Remaining requests after supplying the actual boot and its charged time. -/
def remainingRequest {A : Sort ua} {B : A → Sort ub} {C : (a : A) → B a → Sort uc}
    (_request : (a : A) → (b : B a) → C a b) (a : A) (b : B a) : Sort uc := C a b

/-- Supply a verified input and its receipt, keeping the remaining
dependent requests grouped in the result type. -/
def supplyReceipt {A : Sort ua} {B : A → Sort ub} {C : (a : A) → B a → Sort uc}
    (request : (a : A) → (b : B a) → C a b) (a : A) (b : B a) :
    remainingRequest request a b := request a b

end Diagonal

end BorderVNP
end Computability
end OAI
