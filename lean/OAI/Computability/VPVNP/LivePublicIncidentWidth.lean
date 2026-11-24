import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeParameters

/-!
# Length expressions for the two kinds of incident fields

The sorter exchanges two blocks per triangular layer. The expression forms
the triangular numerator before division, so its fit proof bounds that
numerator independently of the final incident width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.IncidentPublic

open BurstRAM PrimedInputRAM

/-- Bit length of one sorting block, with four times the bucket capacity records of five RAM
words each. -/
def block : PublicExpr := (((.lit 4 : PublicExpr).mul .H).mul (.lit 5)).mul .w

/-- Bit length of one successor field containing eight RAM words. -/
def successor : PublicExpr := (.lit 8 : PublicExpr).mul .w

/-- Combined bit length of the outgoing and incoming successor fields. -/
def bothSuccessors : PublicExpr := (.lit 2 : PublicExpr).mul successor

/-- Number of bitonic layers on the site-address bits, the triangular number for the address
width. -/
def layers : PublicExpr := (((.d : PublicExpr).add (.lit 1)).mul .d).divConst 2

/-- Total incident bit length, comprising both successor fields and two sorting blocks for each
layer. -/
def incident : PublicExpr := bothSuccessors.add (layers.mul ((.lit 2 : PublicExpr).mul block))

@[simp] theorem block_eval (g : Geometry) : block.eval g = RAMLayout.blockBits g.H g.w := rfl

@[simp] theorem layers_eval (g : Geometry) : layers.eval g = RAMLayout.layerCount g.d := by
  simp [layers, PublicExpr.eval, RAMLayout.layerCount, Nat.choose_two_right]

@[simp] theorem incident_eval (g : Geometry) : incident.eval g = RAMLayout.width g.d g.H g.w := by
  change 2 * (8*g.w) + layers.eval g * (2*block.eval g) = _
  rw [layers_eval,block_eval]
  rfl

theorem fits {L : PrimedInputRAM.Lengths} {n r H w : ℕ}
    (Q : Layout L n r H w) (F : Opcodes.ParameterFit Q) (hr : 1 ≤ r)
    (hw : w = (r+10)^4) (g : Geometry) (hd : g.d = r) (hH : g.H = H) (hwidth : g.w = w) :
    block.Fits g (2^w) ∧ successor.Fits g (2^w) ∧ bothSuccessors.Fits g (2^w) ∧ incident.Fits g (2^w) := by
  have h16w : 16*w < 2^w := Opcodes.pubNat_lt Q F 15
  have hwpos : 0 < w := by rw [hw]; positivity
  have hlt : 16 < 2^w := by omega
  let Fit := PublicExpr.Fits g (2 ^ w)
  have lit {i : ℕ} (hi : i ≤ 16) : Fit (.lit i) := ⟨hi.trans_lt hlt,trivial⟩
  have mul {a b : PublicExpr} (fa : Fit a) (fb : Fit b) (hab : a.eval g*b.eval g < 2^w) :
      Fit (.mul a b) := ⟨hab,fa,fb⟩
  have fw : Fit .w := ⟨hwidth ▸ (Opcodes.pubNat_lt Q F 4),trivial⟩
  have fH : Fit .H := ⟨by change g.H < _; rw [hH]; exact Opcodes.pubNat_lt Q F 5,trivial⟩
  have fd : Fit .d := ⟨by change g.d < _; rw [hd]; exact Opcodes.pubNat_lt Q F 3,trivial⟩
  have hb := F.blockFits
  have hwblock : 4*H*5 ≤ 4*H*5*w := Nat.le_mul_of_pos_right _ hwpos
  change 4*H*5*w < 2^w at hb
  have f4H := mul (lit (by decide : 4 ≤ 16)) fH (by change 4*g.H < _; rw [hH]; omega)
  have f5 := mul f4H (lit (by decide : 5 ≤ 16)) (by change 4*g.H*5 < _; rw [hH]; omega)
  have fb : Fit block := mul f5 fw (by change 4*g.H*5*g.w < _; rwa [hH,hwidth])
  have fs : Fit successor := mul (lit (by decide)) fw (by change 8*g.w < _; rw [hwidth]; omega)
  have fss : Fit bothSuccessors := mul (lit (by decide)) fs (by change 2*(8*g.w) < _; rw [hwidth]; omega)
  have hsub : (r+1)*r ≤ w := by
    rw [hw]
    calc
      _ ≤ (r+10)*(r+10) := Nat.mul_le_mul (by omega) (by omega)
      _ = (r+10)^2 := (sq _).symm
      _ ≤ (r+10)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hfit : w < 2^w := Nat.lt_two_pow_self
  have hinc : r+1 ≤ (r+1)*r := Nat.le_mul_of_pos_right _ hr
  have fplus : Fit ((.d : PublicExpr).add (.lit 1)) := ⟨by change g.d + 1 < _; rw [hd]; omega,fd,lit (by decide)⟩
  have fprod := mul fplus fd (by change (g.d+1)*g.d < _; rw [hd]; omega)
  have flayers : Fit layers := ⟨by change (g.d+1)*g.d / 2 < _; rw [hd]; omega, fprod, by omega⟩
  have hincfit : RAMLayout.width r H w < 2^w := Opcodes.pubNat_lt Q F 8
  have hcount : 1 ≤ RAMLayout.layerCount r := PortCode.layerCount_mono (show 1 ≤ r from hr)
  have hdir : 2*RAMLayout.blockBits H w ≤ RAMLayout.layerCount r*(2*RAMLayout.blockBits H w) :=
    Nat.le_mul_of_pos_left _ hcount
  change 2*(8*w)+RAMLayout.layerCount r*(2*RAMLayout.blockBits H w) < _ at hincfit
  have fdirs := mul (lit (by decide : 2 ≤ 16)) fb (by change 2 * block.eval g < _; rw [block_eval,hH,hwidth]; omega)
  have fsort := mul flayers fdirs (by
    change layers.eval g * (2 * block.eval g) < _
    rw [layers_eval,block_eval,hd,hH,hwidth]; omega)
  exact ⟨fb,fs,fss,⟨by rw [incident_eval,hd,hH,hwidth]; exact hincfit, fss,fsort⟩⟩

end LiveProgram.IncidentPublic

end VPVNP
end Computability
end OAI
