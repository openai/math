import OAI.Computability.BorderVNP.CellPacketCopyHeaderLoop

/-! # Native opaque-payload header decoder

The two output registers delimit precisely the payload whose length was encoded
in the preceding field. They can be passed directly to the bit-slice copier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketCopy

open VPVNP.BurstRAM CellPacketEncode

private def headerInit : Code := .seq (.copy 21 15) (.copy 22 0)
private def headerFinish : Code := .seq (.copy 14 15) (.binary .add 15 15 22)

/-- Parse a little-endian length field and replace its address pair by the payload address pair. -/
def header : Code := .seq headerInit (.seq (.whileLt 14 21 headerStep) headerFinish)

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Every address in the header is a physical Boolean-valued word. With the exclusive
payload end fitting the bank width, this fragment reads the length and installs both
payload cursors. It leaves the destination, protected frame registers and memory intact. -/
theorem headerRun (s : Bank w) (m : Memory w) (H n : ℕ) (c : Constants (readings s))
    (stop : readings s 15 = readings s 14 + H)
    (source : ∀ i : Fin H, readings m (readings s 14 + i.val) = (n.testBit i.val).toNat)
    (fitsHeader : n < 2^H) (fit : readings s 15 + n < 2^w) :
    BoundedRun pub macros header s m (10*H+6) (fun z =>
      (∀ j, j ≠ 14 → j ≠ 15 → j ≠ 16 → j ≠ 21 → j ≠ 22 → z.reg j = readings s j) ∧
      z.reg 14 = readings s 15 ∧ z.reg 15 = readings s 15 + n ∧ z.mem = readings m) := by
  obtain ⟨es,t,mt,init,cost,he⟩ := headerInit.runFixed pub macros s m ⟨trivial,trivial⟩
  have ht := congrArg NatState.reg he
  have hm := congrArg NatState.mem he
  change readings mt = readings m at hm
  have fixed (j : Reg) (a : j ≠ 21) (b : j ≠ 22) : readings t j = readings s j := by
    simpa [headerInit, Code.fixedEval, Code.evalNat, NatState.ofWords, a,b] using congrFun ht j
  have hsrc := fixed 14 (by decide) (by decide)
  have h21 : readings t 21 = readings s 15 := by
    simpa (config := {decide := true}) [headerInit, Code.fixedEval, Code.evalNat, NatState.ofWords] using congrFun ht 21
  have h22 : readings t 22 = 0 := by
    simpa (config := {decide := true}) [headerInit, Code.fixedEval, Code.evalNat, NatState.ofWords, c.1] using congrFun ht 22
  obtain ⟨fs,u,mu,loop,cost',regs,hu,mem⟩ := headerLoop_run (pub := pub) (macros := macros) t mt n H
    ((fixed 1 (by decide) (by decide)).trans c.2.1) (by rw [hsrc,h21,stop])
    (by rw [Nat.div_eq_of_lt fitsHeader,h22]) (by omega)
    (fun i => by rw [hm,hsrc]; exact source i)
  change readings u 22 = n at hu
  have hu15 : readings u 15 = readings s 15 := (regs 15 (by decide) (by decide) (by decide)).trans
    (fixed 15 (by decide) (by decide))
  have safe : headerFinish.fixedSafe w (readings pub) (.ofWords u mu) := by
    simpa (config := {decide := true}) [headerFinish, Code.fixedSafe, Code.fixedEval, Code.safeReadOnly,
      Code.evalNat, addressOpFits, NatState.ofWords, hu15,hu] using fit
  obtain ⟨gs,z,mz,finish,cost'',hz⟩ := headerFinish.runFixed pub macros u mu safe
  have rz := congrArg NatState.reg hz
  refine ⟨_,z,mz,init.seq (loop.seq finish), ?_, fun j a b d e f => ?_, ?_, ?_, ?_⟩
  · rw [show traceCost (es ++ (fs ++ gs)) = traceCost es + traceCost (fs ++ gs) from VPVNP.RAMBuckets.cost_append ..,
      show traceCost (fs ++ gs) = traceCost fs + traceCost gs from VPVNP.RAMBuckets.cost_append ..]
    change traceCost es ≤ 2 at cost
    change traceCost gs ≤ 2 at cost''
    omega
  · have r : readings z j = readings u j := by
      simpa [headerFinish, Code.fixedEval, Code.evalNat, NatState.ofWords, a,b] using congrFun rz j
    exact (r.trans (regs j d e f)).trans (fixed j e f)
  · simpa (config := {decide := true}) [headerFinish, Code.fixedEval, Code.evalNat,
      NatState.ofWords, hu15] using congrFun rz 14
  · simpa (config := {decide := true}) [headerFinish, Code.fixedEval, Code.evalNat,
      NatState.ofWords, addressOp, hu15,hu] using congrFun rz 15
  · exact (congrArg NatState.mem hz).trans (mem.trans hm)

end RoutingISA.CellPacketCopy

end BorderVNP
end Computability
end OAI
