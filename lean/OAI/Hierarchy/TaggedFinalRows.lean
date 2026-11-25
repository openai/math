import Mathlib.Data.List.Basic

namespace OAI
namespace Hierarchy.Tagged.FinalScan

def paired {α : Type*} : List (Bool × α) → Prop
  | [] => True
  | a::b::tl => a.1 = false ∧ b.1 = true ∧ a.2 = b.2 ∧ paired tl
  | [_] => False

end Hierarchy.Tagged.FinalScan

end OAI
