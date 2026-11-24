import OAI.Computability.VPVNP.RAMTapeSortRowCompare

/-!
# Two physical record comparisons for a cross-site row

The first local fetch is compared with the next outgoing field. After that
check consumes the two operands, the routine fetches the local slot again
and compares it with the incoming field to form the layer output.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open RAMBoundary Boundary

theorem crossPass_runs {w B : ℕ} (s : Stacks Port) (block : Fin B → RawSlot w)
    (i j : Fin B) (keepMin : Bool) (sent peer : RawSlot w) (st rt : List Bool)
    (h : Ready s block i j false keepMin) (hs : s .crossSend = recordBytes sent ++ st)
    (hr : s .crossReceive = recordBytes peer ++ rt) :
    let f := 5*i.val+2+SortGather.cost i.val w
    crossPass.Runs (f + (50*w+18 + (f + (65*w+20)))) (Function.update s .localFlag [])
      (Function.update (result s keepMin (block i) peer (some sent) st rt) .partner (s .partner)) := by
  let t := Function.update s Port.localFlag []
  let a := block i
  let f := 5*i.val+2+SortGather.cost i.val w
  let r₁ := Function.update t Port.left (recordBytes a)
  have ht : FetchReady w t := ⟨h.width, h.lookup, h.widthBack, h.saved, h.recordBack⟩
  have h₁ : (fetch .first).Runs f t r₁ := by
    have he := fetch_runs .first t block i ht h.block_eq h.row_eq
    change (fetch .first).Runs f t (Function.update t Port.left (recordBytes a ++ t .left)) at he
    simpa only [show t .left = [] from h.left, List.append_nil] using he
  let r₂ := compareResult r₁ .outgoing [] st [] (verifyOK a sent)
  have hcmp₁ : CompareReady w r₁ := ⟨h.width,h.widthBack,h.savedLeft,h.savedRight,h.selectTmp⟩
  have h₂ : verify.Runs (50*w+18) r₁ r₂ := verify_runs r₁ a sent [] st hcmp₁ (by
    change recordBytes a = recordBytes a ++ []
    rw [List.append_nil]) hs
  let r₃ := Function.update r₂ Port.left (recordBytes a)
  have ht₂ : FetchReady w r₂ := ⟨h.width, h.lookup, h.widthBack, h.saved, h.recordBack⟩
  have h₃ : (fetch .first).Runs f r₂ r₃ := by
    have he := fetch_runs .first r₂ block i ht₂ h.block_eq h.row_eq
    change (fetch .first).Runs f r₂ (Function.update r₂ Port.left (recordBytes a ++ [])) at he
    simpa only [List.append_nil] using he
  have hcmp₃ : CompareReady w r₃ := ⟨h.width,h.widthBack,h.savedLeft,h.savedRight,h.selectTmp⟩
  have h₄ := oriented_runs .incoming r₃ keepMin a peer [] rt hcmp₃ h.orientation (by
    change recordBytes a = recordBytes a ++ []
    rw [List.append_nil]) hr
  have hrun := h₁.followedBy (h₂.followedBy (h₃.followedBy h₄))
  have he :
      compareResult (Function.update r₃ .orientation []) .incoming [] rt
        (recordBytes (chosen keepMin a peer)).reverse (selectOK a peer) =
      Function.update (result s keepMin a peer (some sent) st rt) .partner (s .partner) := by
    funext p
    cases p <;> first | rfl | exact h.left.symm
  rw [he] at hrun
  exact hrun

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
