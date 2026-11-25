import OAI.Computability.BorderVNP.TeamSiteBudget

/-! # Exact physical replay of every guarded processor chunk -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape TeamPrivateFragment TeamRAM
open BurstRAM (Word)
open RAMSerialization (WordRecord)

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}

/-- The complete chronological native block replays from the actual register, countdown
and record bank. Every subsequent continuation receives the untouched suffix of choice
bits and the unmodified order of the accumulated typed sorter slots. -/
theorem Chunk.run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (fuel : ℕ) (pub : Fin k → Word w) {s last : TeamOpcode.State w p r} {c fin : Window w}
    {es : List (Event w)} (chunk : Chunk (P.fetch pub (fun j => (lib j).eval fuel)) s c es last fin)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (rest : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ n out, n ≤ Work.chunkBudget w m g fuel es ∧
      StackRuns (replay (Loop.code P lib)) n (.clock sg (.enter s.pc),chunkBits es++rest) base
        (.clock (chunkSign sg es) (.enter last.pc),rest) out ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) out ∧
      out ∘ Port.clock = fin.bank pub last ∧
      (rs++chunkSlots (c.elapsed.val+1) es).length + 2*fin.block.val ≤ 4*H := by
  induction chunk generalizing sg rs base with
  | nil =>
    refine ⟨0,base,le_rfl,.nil ..,?_,clock,?_⟩ <;> simpa only [chunkSlots,TeamEventRecords.historySlots,List.append_nil]
  | @cons s c e next es last fin act go fits cap later ih =>
    obtain ⟨n,b,hn,first,hb,cb,room⟩ := event_run P lib fuel pub s next c sg e rs base
      (chunkBits es++rest) safe fits cap act go clock ready space
    obtain ⟨_,_,time,hs⟩ := c.charged_values e.action.extra safe fits
    obtain ⟨t,out,ht,tail,ready',bank',space'⟩ := ih (Loop.times sg (signBit e.sign)) _ b hs cb hb room
    have stamp : (c.charge e.action.extra).elapsed.val + 1 = c.elapsed.val+1+(1+e.action.extra) := by omega
    refine ⟨n+t,out,Nat.add_le_add hn ht,?_,?_,bank',?_⟩
    · simpa only [chunkBits, List.flatMap_cons, List.append_assoc, chunkSign, List.foldl_cons] using first.trans tail
    · simpa only [chunkSlots,TeamEventRecords.historySlots, stamp, List.append_assoc] using ready'
    · simpa only [chunkSlots,TeamEventRecords.historySlots, stamp, List.append_assoc] using space'

end TeamSite

end BorderVNP
end Computability
end OAI
