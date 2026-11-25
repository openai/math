import OAI.Computability.BorderVNP.TeamSiteSupplyChunk
import OAI.Computability.BorderVNP.TeamSiteConsistencyExits
import OAI.Computability.BorderVNP.TeamSiteTraversal

/-! # Unique local instruction history from one processor's exact choices

A canonical predecessor and the complete physical guess spelling determine
the native signed events and the complete outgoing frame. The proof follows
the finite native machine on the spelled branch supply, including valid
zero-weight paths and an already halted predecessor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape RAMTape.PublicExprMachine TeamTapeHandoff TeamSiteChoices TeamSiteEvents SupplyRun
open BurstRAM (Word)
open TeamRAM (Event)

variable {Q Γ : Type} {w p r k a m g : ℕ}

/-- Decode a local physical end mode back to its canonical output frame. -/
private def resultFrame (z : TeamOpcode.State w p r) (fin : Window w) (out : Frame w r) : Verdict → Prop
  | .accepted => out = .accepted fin.elapsed
  | .handoff => out = .live (packed w z.pc.val) z.reg fin.elapsed
  | .reject => False

private theorem live_run (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (H limit cap : Word w)
    (word : Word w) (regs : Fin r → Word w) (elapsed : Word w) (es : List (Event w)) (f : Frame w r)
    (h : EndpointRow P pub (macros lib fuel) H limit cap (.live word regs elapsed) es f) :
    ∃ pc : Fin p, ∃ z fin verdict, word = packed w pc.val ∧
      Run P pub lib fuel ⟨pc,regs⟩ (blockWindow H limit elapsed cap) (extend (chunkBits es)) es z fin verdict ∧
      resultFrame z fin f verdict := by
  obtain ⟨_,pc,z,fin,word,chunk,stopped⟩ := h
  have hp : Prefix (extend (chunkBits es)) (chunkBits es) := prefix_extend _
  rcases stopped with ⟨ha,frame⟩ | ⟨hh,frame⟩
  · exact ⟨pc,z,fin,.accepted,word,of_chunk chunk hp (Run.accept (congrArg Prod.fst ha)),frame⟩
  · exact ⟨pc,z,fin,.handoff,word,of_chunk chunk hp (Run.handoff (congrArg Prod.fst hh)),frame⟩

/-- An accepted or propagated local row has a unique native event list and output
frame once its input frame and exact finite spelling are fixed. -/
theorem EndpointRow.determined (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (H limit cap : Word w) (fits : p ≤ 2^w)
    (f : Frame w r) {x y : List (Event w)} {out₁ out₂ : Frame w r}
    (hx : EndpointRow P pub (macros lib fuel) H limit cap f x out₁)
    (hy : EndpointRow P pub (macros lib fuel) H limit cap f y out₂)
    (bits : chunkBits x = chunkBits y) : x = y ∧ out₁ = out₂ := by
  cases f with
  | accepted elapsed => exact ⟨hx.1.trans hy.1.symm,hx.2.2.trans hy.2.2.symm⟩
  | live word regs elapsed =>
    obtain ⟨pc,z,c,v,hpc,run,out⟩ := live_run P pub lib fuel H limit cap word regs elapsed _ _ hx
    obtain ⟨pc',z',c',v',hpc',run',out'⟩ := live_run P pub lib fuel H limit cap word regs elapsed _ _ hy
    have same : pc = pc' := by
      apply Fin.ext
      have he := congrArg Fin.val (hpc.symm.trans hpc')
      simpa only [packed_val (lt_of_lt_of_le pc.isLt fits), packed_val (lt_of_lt_of_le pc'.isLt fits)] using he
    subst pc'
    obtain ⟨he,rfl,rfl,rfl⟩ := run.of_same_bits run' bits
    cases v with
    | accepted | handoff => exact ⟨he,out.trans out'.symm⟩
    | reject => exact False.elim out

end TeamSite

end BorderVNP
end Computability
end OAI
