import OAI.Computability.BorderVNP.CubePairDirectoryModel
import OAI.Computability.BorderVNP.RoutingISATableSetup

/-! # Loading the native label-pair directory configuration from the real frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PairDirectory

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Physical frame values for the directory pass. Blocks are loaded indirectly
from the eighth word of the declaration header. -/
structure Layout.Fields (l : Layout) (m : ℕ → ℕ) : Prop where
  alphabet : m (l.frame+56) = l.Z
  symbols : m (l.frame+59) = l.d
  axes : m (l.frame+60) = l.axes
  header : m (l.frame+63) = l.header
  blocks : m (l.header+7) = l.blocks
  table : m (l.frame+91) = l.table

/-- Set the three small constants, load the true public field values, and
compute the squared digit radix and the number of ordered label pairs. -/
def setup : Code := .block [.constant 0 0,.constant 1 1,.constant 2 2,
  readFrame 3 62 63 59, readFrame 4 62 63 60, readFrame 5 62 63 56,
  readFrame 11 62 63 63, .constant 63 7,.binary .add 62 11 63,.load 6 62,
  readFrame 7 62 63 91,.binary .mul 8 5 5,.binary .mul 10 3 3]

set_option maxHeartbeats 2000000 in
/-- The fixed setup returns the exact ABI used by the pair loops and leaves
the shared memory unchanged. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (s : Bank w) (m : Memory w) (fit : l.Fits w) (hf : (pub 0).val = l.frame) (fields : l.Fields (readings m)) :
    BoundedRun pub mac setup s m setup.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  have hp : readings pub 0 = l.frame := hf
  have fs (dst : Reg) (f : Word 8) (z : NatState) (hh : f.val ≤ 91) :
      (readFrame dst 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe dst f _ z w (by rw [hp]; have := fit.frame; omega)
  have hc : l.Z*l.Z < 2^w := by change l.count < _; have := fit.directory; omega
  have h7 : 7 < 2^w := by have := fit.header; omega
  have h2 : 2 < 2^w := by omega
  have h1 : 1 < 2^w := by omega
  have h0 : 0 < 2^w := Nat.two_pow_pos _
  apply (setup.runFixed pub mac s m ?_).mono le_rfl
  · rintro z rfl
    constructor
    · intro j hj hn
      rcases j with ⟨j, hj'⟩
      change j ≤ 10 at hj
      change j ≠ 9 at hn
      interval_cases j <;> simp_all (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
        addressOp,readFrame_fixedEval,NatState.ofWords,Layout.param,Layout.count,fields.symbols,fields.axes,
        fields.alphabet,fields.header,fields.table,fields.blocks]
    · simp [setup,Code.block,Code.fixedEval,readFrame_fixedEval,NatState.ofWords]
  · simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,readFrame_fixedEval,NatState.ofWords,hp,fields.header,fields.alphabet,fields.symbols,
      fs _ _ _ (by decide : (59 : Word 8).val ≤ 91), fs _ _ _ (by decide : (60 : Word 8).val ≤ 91),
      fs _ _ _ (by decide : (56 : Word 8).val ≤ 91), fs _ _ _ (by decide : (63 : Word 8).val ≤ 91),
      fs _ _ _ (by decide : (91 : Word 8).val ≤ 91),fit.header,fit.radix,hc,h7,h2,h1,h0]

end Cube.PairDirectory

end BorderVNP
end Computability
end OAI
