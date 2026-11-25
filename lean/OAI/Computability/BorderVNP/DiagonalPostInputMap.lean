import Mathlib.Logic.Function.Basic

/-! # Keeping the inputs of a dependent post-call procedure -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

universe v i e c

variable {Op : Prop} {Values : Type v} {Pin : Type i} {Entries : Values → Type e}
    {Checks : (values : Values) → Pin → Entries values → Type c}
    {Post Charge : (values : Values) → (pin : Pin) → (entries : Entries values) →
      Checks values pin entries → Prop}

/-- The original operational condition and post-call inputs, with the
specified conclusion at the original pin. The operand fixes all the input
types even when they contain previously selected physical return data. -/
def PostInputTarget
    (_ : Op → ∀ values pin entries checks, Post values pin entries checks → Charge values pin entries checks)
    (atPin : Pin → Prop) : Prop :=
  Op → ∀ values pin entries checks, Post values pin entries checks → atPin pin

/-- First read the earned charge and then apply it to the chosen conclusion,
keeping the same operational witness, route data, and pin. -/
theorem PostInputTarget.map {atPin : Pin → Prop}
    (receive : Op → ∀ values pin entries checks, Post values pin entries checks → Charge values pin entries checks)
    (finish : Op → ∀ values pin entries checks, Charge values pin entries checks → atPin pin) :
    PostInputTarget receive atPin :=
  fun op values pin entries checks post => finish op values pin entries checks (receive op values pin entries checks post)

end Diagonal

end BorderVNP
end Computability
end OAI
