import OAI.Computability.BorderVNP.CubeScatterPaddingLayout
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Loading the endpoint owner and the directed-bin padding interval

The lookup decodes the source or target digit of the ordered-pair index. The cache
then loads the width and three consecutive metadata words and uses the occupied
width as the first padding ordinal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM HostScatter

/-- Select the label of this end and look up the group owner for the native axis. -/
def ownerStep (side : Bool) : Code := .block [
  .binary (if side then .mod else .div) 33 13 7, .binary .div 33 33 6,
  .binary .mod 33 33 4, .binary .add 33 8 33, .load 33 33]

/-- Fill the native bit-checker registers with the unused suffix of one bin. -/
def cacheStep (side : Bool) : Code := .block [
  .binary .add 34 9 13, .load 17 34, .binary .mul 15 25 26, .binary .sub 15 15 17, .copy 16 13,
  .binary .mul 34 3 13, .binary .add 34 11 34, .load 18 34, .binary .add 34 34 1, .load 19 34,
  .binary .add 34 34 1, .load 20 34, .copy 21 (if side then 1 else 0), .copy 22 0]

/-- Actual owner lookup from the chosen axis digit, preserving the public cache, directory
index and all memory words. -/
theorem run_ownerStep {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) {key : ℕ} (hk : key < l.count) (side : Bool) (s : Bank w) (m : Memory w)
    (fit : l.Fits w (readings m)) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = key) :
    BoundedRun pub mac (ownerStep side) s m (ownerStep side).slots
      (fun z => l.Ready z ∧ z.reg 13 = key ∧ z.reg 33 = l.owner (readings m) key side ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  change l.Ready z at ready
  change z.reg 13 = key at idx
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r11,r12,r24,r25,r26,r27,r28,r29⟩ := ready
  have ha := fit.owner key hk side
  have safe : (ownerStep side).fixedSafe w (readings pub) z := by
    cases side <;> simpa (config := {decide := true})
      [ownerStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
        addressOpFits,addressOp,idx,r4,r6,r7,r8,fit.groups,fit.labels,fit.place,Layout.ownerAt,Layout.label] using ha
  apply ((ownerStep side).runFixed pub mac s m safe).mono le_rfl
  rintro _ rfl
  change l.Ready ((ownerStep side).fixedEval (readings pub) z) ∧ _
  cases side <;> simp (config := {decide := true})
    [ownerStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,Layout.Ready,Layout.owner,Layout.ownerAt,
      Layout.label,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r11,r12,r24,r25,r26,r27,r28,r29,idx,z] <;> simp [NatState.ofWords]

set_option maxHeartbeats 1200000 in
/-- Actual register contents for the entire directed-bin suffix. Its width is the
bin capacity minus the occupied width read from the live width array. -/
theorem run_cacheStep {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) {key : ℕ} (hk : key < l.count) (side : Bool) (s : Bank w) (m : Memory w)
    (fit : l.Fits w (readings m)) (ready : l.Ready (.ofWords s m)) (idx : (s 13).val = key) :
    BoundedRun pub mac (cacheStep side) s m (cacheStep side).slots
      (fun z => l.Ready z ∧ z.reg 13 = key ∧ (l.fields (readings m) key side).Ready z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  change l.Ready z at ready
  change z.reg 13 = key at idx
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r11,r12,r24,r25,r26,r27,r28,r29⟩ := ready
  have triple := fit.tripleAddress key hk
  have used : z.mem (l.widths+key) ≤ l.blocks*l.bc := fit.used key hk
  have stride : l.blocks*l.bc < 2^w := fit.stride
  have safe : (cacheStep side).fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [cacheStep,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,idx,r1,r3,r9,r11,r25,r26,
      fit.widthAddress key hk,stride,used]
    omega
  apply ((cacheStep side).runFixed pub mac s m safe).mono le_rfl
  rintro _ rfl
  change l.Ready ((cacheStep side).fixedEval (readings pub) z) ∧ _
  cases side <;> simp (config := {decide := true})
    [cacheStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,Layout.Ready,Layout.fields,Layout.stride,
      BitFields.Ready,BitFields.read,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r11,r12,r24,r25,r26,r27,r28,r29,
      idx,z] <;> simp [NatState.ofWords]

end Cube.Padding

end BorderVNP
end Computability
end OAI
