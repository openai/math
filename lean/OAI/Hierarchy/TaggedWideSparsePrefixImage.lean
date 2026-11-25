import OAI.Hierarchy.TaggedWideDatedROM

namespace OAI
/-! # Rewriting the prepared advice on the actual postsettlement heap -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM
variable {T W : ℕ} (g : Dated T) (rom : ℕ) (sites : Fin g.siteDirectorySize→ℕ)
    (transport : Fin g.rawEdges→Bool) (input out : Memory W)

theorem Dated.words_absorb :
    g.words rom sites transport (g.words rom sites transport input)=g.words rom sites transport input := by
  funext a
  unfold Dated.words
  generalize ((romAt rom g.sites (fun i=>i.val*g.roleCount) a) <|>
    romAt (g.siteROM rom) g.siteDirectorySize sites a <|>
    (List.ofFn fun j : Fin T=>(g.ballot j).word g.sites (g.ballotROM rom j) a).findSome? id <|>
    (List.ofFn fun j : Fin T=>(g.control j).word g.sites (g.controlROM rom j) a).findSome? id <|>
    romAt (g.maskROM rom) g.rawEdges (fun i=>(transport i).toNat) a)=x
  cases x <;> rfl

theorem Dated.mounted_image
    (header : ∀a,rom≤a→a<g.romEnd rom→ out a=g.words rom sites transport input a) :
    g.words rom sites transport out=out := by
  funext a
  by_cases left : a<rom
  · exact g.words_before rom sites transport out a left
  by_cases right : g.romEnd rom≤a
  · exact g.words_end rom sites transport out a right
  have here:=header a (Nat.le_of_not_gt left) (Nat.lt_of_not_ge right)
  exact (g.words_congr rom sites transport out _ a here).trans
    ((congrFun (g.words_absorb rom sites transport input) a).trans here.symm)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
