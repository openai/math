import OAI.Computability.VPVNP.RAMProcessorPrelude

/-!
# The initialization record of the linked site

The staged words encode the prescribed initialization, including its site
address in the start-cost position. Every site contributes this record even
when its incoming status has already halted.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM RAMSerialization

variable {w p r k H : ℕ}

/-- Initialization record installing the site's header word at its address, using that same
address as its start cost and zero as its ordinal. -/
def initRecord (addr header : Word w) : WordRecord w := ⟨.init, addr, header, addr, 0⟩

theorem Snapshot.initWords (s : Snapshot w p r k) (hw : 2 ≤ w) (a h : Word w)
    (ha : s.address = BurstRAM.wordBits a) (hh : s.value = BurstRAM.wordBits h) (i : Fin 5) :
    (s.withInitFields a).records (.field i) =
      BurstRAM.wordBits ((recordFormat hw).words (some (initRecord a h)) i) := by
  fin_cases i
  · apply congrArg BurstRAM.wordBits
    apply Fin.ext
    change 1 % (2^w) = 1
    exact Nat.mod_eq_of_lt ((by decide : 1 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hw))
  · exact ha
  · exact hh
  · rfl
  · rfl

theorem Snapshot.emptyHolds (s : Snapshot w p r k) (hw : 2 ≤ w)
    (hs : s.remaining = List.replicate (4*H) true) (hb : s.reverseBuffer = []) (ho : s.output = []) :
    RecordBuffer.Holds hw H [] s.records :=
  ⟨Nat.zero_le _, rfl, rfl, hs, hb, ho⟩

theorem initialRecord_run (T : PrivateRAM.Template p r k) (s : Snapshot w p r k) (hw : 2 ≤ w)
    (a h : Word w) (ha : s.address = BurstRAM.wordBits a) (hh : s.value = BurstRAM.wordBits h)
    (hs : s.remaining = List.replicate (4*H) true) (hb : s.reverseBuffer = []) (ho : s.output = [])
    (hH : 0 < H) :
    let staged := s.withInitFields a
    let after := staged.afterEmit hw (initRecord a h)
    StackRuns (table T) (25*w+12) (atLabel T .initialRecord) staged.bank (atLabel T .checkEntry) after.bank ∧
      RecordBuffer.Holds hw H [initRecord a h] after.records := by
  exact record_emit_run T (s.withInitFields a) hw rfl ((s.withInitFields a).emptyHolds hw hs hb ho)
    (by simp; omega) (initRecord a h) (s.initWords hw a h ha hh)

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
