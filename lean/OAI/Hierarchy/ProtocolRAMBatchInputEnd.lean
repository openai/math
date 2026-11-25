import OAI.Hierarchy.ProbeFixedPrefixBatch

namespace OAI
/-! # Input addresses of the actual batch updates and emitted link columns -/
namespace Hierarchy.ProtocolRAM
variable {q d cut high : ℕ} {b : Batch q d}

namespace Batch.Before
theorem mono (h : b.Before cut) (le : cut≤high) : b.Before high :=
  ⟨h.menu.trans le,h.termCount.trans le,h.enabled.trans le,h.owner.trans le,
    fun i => (h.field i).trans le,fun i => (h.stock i).trans le,
    fun i => (h.perCopy i).trans le,fun e he => (h.quotes e he).trans le⟩

theorem ifAdmitted (h : b.Before cut) (yes no : Expr)
    (yesEnd : yes.inputEnd≤cut) (noEnd : no.inputEnd≤cut) :
    (b.ifAdmitted yes no).inputEnd≤cut :=
  h.ifSelected _ _ (h.ifPacket yes no yesEnd noEnd)
    (InputEnd.ifHistogram _ _ _ _ _ h.field yesEnd noEnd)

theorem nextStock (h : b.Before cut) (i : Fin d) (credit : Expr) (hc : credit.inputEnd≤cut) :
    (b.nextStock i credit).inputEnd≤cut :=
  h.ifSelected _ _ (h.ifPacket _ _ (max_le (max_le (h.stock i) (h.need i)) hc) (h.stock i)) (h.stock i)

theorem fields (h : b.Before cut) (l : Link) (width : Fin q → Expr)
    (grp : l.group.inputEnd≤cut) (src : l.endpoint.inputEnd≤cut)
    (dst : l.opposite.inputEnd≤cut) (len : l.lengthCode.inputEnd≤cut)
    (table : ∀ i, (width i).inputEnd≤cut) (j : Fin 7) :
    ((l.fields b width) j).inputEnd≤cut := by
  fin_cases j
  · exact grp
  · exact src
  · exact dst
  · exact max_le (Nat.zero_le _) (Nat.zero_le _)
  · exact h.wire width table
  · exact len
  · exact h.ifSelected _ _ (h.ifPacket _ _ h.packet (Nat.zero_le _)) (Nat.zero_le _)
end Batch.Before
end Hierarchy.ProtocolRAM

end OAI
