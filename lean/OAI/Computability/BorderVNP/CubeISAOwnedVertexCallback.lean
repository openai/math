import OAI.Computability.BorderVNP.CubeISAOwnedVertexEmit

/-! # Restoring static selector widths inside the owned packet scan

The persistent loop bank carries the selector width and range in registers
8 and 9. Two copies install them for the checked reader before the callback.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.VertexIndex VPVNP.BurstRAM

/-- Copy the preserved selector dimensions to the selector reader's registers. -/
def selectorShape : Code := .seq (.copy 41 8) (.copy 42 9)

/-- Full owned-row callback with the static width and count restored. -/
def vertexCallback : Code := .seq selectorShape emitPacket

/-- Reading, validating and emitting the selected vertices costs two width
copies in addition to the selector-and-writer cost. The output bank starts at
the old cursor, and all persistent words other than the new cursor survive. -/
theorem vertexCallback_run {w n d blocks : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool) (s : Bank w) (m : Memory w)
    {bank out width count : ℕ}
    (upper : readings s 15 = (p.1.1 i).val.2.val) (ori : readings s 25 = p.1.2.toNat)
    (group : readings s 3 = (groupSymbol p i high).val) (coord : readings s 4 = i.val)
    (dim : readings s 5 = n) (base : readings s 24 = bank) (cursor : readings s 7 = out)
    (bits : readings s 8 = width) (choices : readings s 9 = count)
    (word : width ≤ w) (input : bank+width ≤ 2^w) (fit : out+3*2^n < 2^w)
    (indices : 2^(n+1) ≤ 2^w) (small : 3 < 2^w) :
    TestRun pub macros vertexCallback s m (2+emitPacketCost n width)
      (SelectorRead.Valid (readings m) bank width count) fun z =>
        z.reg 7 = out+3*2^n ∧
        z.mem = image out bank (SelectorRead.decoded (readings m) bank width).val
          (2^i.val) (ownerBit i p.1.2 high).toNat (readings m) (2^n) ∧
        ∀ j : Reg, j.val < 24 → j ≠ 7 → z.reg j = readings s j := by
  have init := (selectorShape.runFixed pub macros s m ⟨trivial,trivial⟩).asTest (by decide)
  have tail u mu (h : NatState.ofWords u mu = selectorShape.fixedEval (readings pub) (.ofWords s m)) :
      TestRun pub macros emitPacket u mu (emitPacketCost n width)
        (SelectorRead.Valid (readings m) bank width count) fun z =>
        z.reg 7 = out+3*2^n ∧
        z.mem = image out bank (SelectorRead.decoded (readings m) bank width).val
          (2^i.val) (ownerBit i p.1.2 high).toNat (readings m) (2^n) ∧
        ∀ j : Reg, j.val < 24 → j ≠ 7 → z.reg j = readings s j := by
    have keep j (hj : j.val < 41) : readings u j = readings s j :=
      (congrArg (fun z : NatState => z.reg j) h).trans (selectorShape.fixedEval_protected _ _ (by decide) j hj)
    have data : (NatState.ofWords u mu).reg 41 = width ∧ (NatState.ofWords u mu).reg 42 = count ∧
        (NatState.ofWords u mu).mem = readings m := by
      rw [h]
      simp (config := {decide := true}) [selectorShape,Code.fixedEval,Code.evalNat,NatState.ofWords,bits,choices]
    have hm : readings mu = readings m := data.2.2
    have run := emitPacket_run (pub := pub) (macros := macros) p i high u mu ((keep 15 (by decide)).trans upper)
      ((keep 25 (by decide)).trans ori) ((keep 3 (by decide)).trans group)
      ((keep 4 (by decide)).trans coord) ((keep 5 (by decide)).trans dim)
      ((keep 24 (by decide)).trans base) ((keep 7 (by decide)).trans cursor)
      data.1 data.2.1 word input fit indices small
    apply run.mono le_rfl (by rw [hm])
    rintro z ⟨hz,img,stable,_,_⟩
    exact ⟨hz,hm ▸ img,fun j hj hne => (stable j hj hne).trans (keep j (by omega))⟩
  exact (init.seq tail).mono le_rfl (by simp) (fun _ h => h)

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
