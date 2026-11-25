import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.Bounded
open Filter
theorem of_eventually_le {ι : ℕ→Type*} {a b : ∀h,ι h→ℕ} (upper : Bounded b)
    (small : ∀ᶠ h:ℕ in atTop,∀i,a h i≤b h i) : Bounded a :=by
  obtain ⟨C,w⟩:=upper
  exact ⟨C,(small.and w).mono fun h both i=>(both.1 i).trans (both.2 i)⟩
end Hierarchy.DescentDatedAddressBook.Bounded

end OAI
