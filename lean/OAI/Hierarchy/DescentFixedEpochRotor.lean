import OAI.Hierarchy.DescentFixedMenu
import OAI.Hierarchy.DescentRotorAlphabet
import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentResetPublicDepth

namespace OAI
/-! # Choosing one powered gadget and one physical rotor from the prime's spectral family -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentHostDegree DescentRotor DescentMixedRouter DescentResetInvoice DescentBaseProfile
open LinearAlgebra.SpectralBooks ThreeFlat Expander NonlinearExpanders
noncomputable section

/-- All fields are chosen before the height, number of sites, terminal tuning
and input circuit. In particular the board and bit width are shared by all resets. -/
structure EpochRotor {F : Type} [Field F] (G : PoweredGadget F) where
  degree : ℕ
  multiplicity : ℕ
  rounds : ℕ
  nodesLog : ℕ
  board : Graph nodesLog degree
  bits : ℕ
  f : ℕ
  g : ℕ
  rounds_pos : 0 < rounds
  contracts : reentryRate degree multiplicity*(1-(2-G.rate)/4)^rounds ≤ 1/2
  capacity : 4*quota rounds ≤ 2^nodesLog
  bits_pos : 0 < bits
  configures : ∀π : Equiv.Perm (Fin (2^nodesLog)), Configures F board.arcs multiplicity bits π
  packed : (2^nodesLog)^2*bits ≤ 2^f
  loss : 128*resetTail f+4*(quota rounds:ℝ)^2/(2:ℝ)^f ≤
    1/(nonhubHops (atRound rounds) (2^nodesLog):ℝ)
  fine : f ≤ g
  reserve : g=reserveGain degree multiplicity f

theorem EpochRotor.of_family {F : Type} [Field F] (G : PoweredGadget F)
    (family : NonlinearExpanders.SpectralFamily F) : Nonempty (EpochRotor G) := by
  have paid:=G.rate_lt_two
  have positive:=G.rate_nonneg
  obtain ⟨d,C,t,n,board,bits,f,g,tpos,contracts,capacity,bitsPos,configure,packed,loss,fine,reserve⟩:=
    common_menu family (ρ:=1-(2-G.rate)/4) (by linarith) (by linarith)
  exact ⟨⟨d,C,t,n,board,bits,f,g,tpos,contracts,capacity,bitsPos,configure,packed,loss,fine,reserve⟩⟩

variable {F : Type} [Field F] {G : PoweredGadget F}

def EpochRotor.spec (c : EpochRotor G) : RotorSpec :=
  ⟨c.nodesLog,c.board.arcs,c.multiplicity,c.bits,atRound c.rounds,c.degree,c.f,c.g⟩

def EpochRotor.reset (c : EpochRotor G) :=
  ResetInput.resetHostGain c.degree (2^c.nodesLog) (GroupStage.depthBound (atRound c.rounds) c.nodesLog c.f c.g)

theorem EpochRotor.branch (c : EpochRotor G) : G.b ≤ 2^(capRate G c.rounds c.g) := by
  have small : G.b ≤ capRate G c.rounds c.g := by unfold capRate;omega
  exact small.trans (Nat.lt_two_pow_self.le)

theorem powered_rotor_of_family (F : Type) [Field F] (family : NonlinearExpanders.SpectralFamily F) :
    ∃G : PoweredGadget F, Nonempty (EpochRotor G) := by
  obtain ⟨G⟩:=exists_powered_gadget F
  exact ⟨G,EpochRotor.of_family G family⟩

end
end Hierarchy.DescentSixParty

end OAI
