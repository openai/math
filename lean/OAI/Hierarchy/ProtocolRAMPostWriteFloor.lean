import OAI.Hierarchy.ProtocolRAMPurchaseStage

namespace OAI
/-! # The first possible write of each reported purchase field -/

namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage
variable {q goods : ℕ}

theorem writes_after (L : Dispatch) (B : Repair q goods) (x : ℕ)
    (quote₀ : x<B.quoteOut) (buy₀ : x<B.purchaseOut) (mode : x<B.modeOut)
    (report : ∀ j,x<B.reportOut j) (bought : ∀ j,x<B.boughtFields j)
    (stock : ∀ i,x<B.stockOut i) (reserve : ∀ i,x<B.reserveOut i)
    (price : ∀ i,x<B.priceOut i) : ∀ p∈writes L B,x<p.out := by
  intro p hp
  simp only [writes,List.mem_cons,List.mem_append] at hp
  rcases hp with rfl | rfl | rfl | ((hr|hb)|(hs|hq))
  · exact quote₀
  · exact buy₀
  · exact mode
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact report j
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    exact bought j
  · obtain ⟨ls,hl,hp⟩ := List.mem_flatten.mp hs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    simp only [stockWrites,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl
    · exact stock i
    · exact (stock i).trans_le (Nat.le_add_right ..)
    · exact reserve i
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact price i

end Hierarchy.ProtocolRAM.Calendar

end OAI
