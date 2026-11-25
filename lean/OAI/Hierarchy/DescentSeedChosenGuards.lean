import OAI.Hierarchy.DescentSeedGuardRoom
import OAI.Hierarchy.DescentSeedPriorWordWidths
import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentOpenSplitStageCount

namespace OAI
/-! # All non-address word checks for genuine whole-program initialization at the chosen terminal socket -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPrimitivePalette DescentSeedRoot Filter
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

theorem selected_word_guards (t f g reset drift quota : ℕ) :
    ∃B₀ : ℕ → ℕ,∀τ B,0 < τ → B₀ τ ≤ B →
      ∀ᶠh : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀M degree w base field wire hist : ℕ,let S:=stageNumbers D t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
        let split:=NativeBranch.binLimit (k:=k) S
        let q:=q₀*(D.b^(t*J)*D.b)
        let p:=split*(h/(16*(q*split)))
        let Z:=S.grainAt D.b p 0
        let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
        let m:=Primitive.paletteLanes D op l.seedWidth Z h k
        h ≤ w → 16*digitsNeeded l.seedWidth ≤ h ∧ 0 < m ∧
          printedBits D l.seedWidth Z op*m ≤ w ∧ DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w ∧
          l.operandBits*l.operandLanes ≤ w ∧ l.seedWidth < 2^Nat.clog 2 (l.seedWidth+1) :=by
  let L:=localSocketRate D t g
  let κ:=1+(hostRate t reset+capRate D t g)*(t+1)+8+cutRate t f g
  refine ⟨fun τ=>1+(κ+3+6)+(2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1)),?_⟩
  intro τ B liveTau budget
  change 1+(κ+3+6)+(2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1)) ≤ B at budget
  have pos : 0 < B:=by omega
  filter_upwards [primitive_word_room D op B κ pos (by omega),
    stage_open_split_counts D t f g reset τ L (τ+κ+4) B pos (by omega),eventually_ge_atTop 32]
    with h shape sockets high
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M degree w base field wire hist
  let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
  let split:=NativeBranch.binLimit (k:=k) S
  let q:=q₀*(D.b^(t*J)*D.b)
  let p:=split*(h/(16*(q*split)))
  let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
  let Z:=S.grainAt D.b p 0
  intro machine
  obtain ⟨_,_,qcap,binPos,binSize,_,_,_⟩:=native_socket_scale D t J f g reset M τ
  have live : 0 < q₀:=Nat.two_pow_pos _
  obtain ⟨_,_,_,lo,_,_⟩:=sockets M q₀ split live binPos qcap binSize
  have src : S.firstWidth D.b p ≤ h :=
    (Nat.le_mul_of_pos_left _ live).trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans lo)
  have group : 2^k ≤ scale J κ:=groupRateAt t J S.hostGain S.capGain (cutRate t f g)
  obtain ⟨packed,lanes,fieldWord⟩:=shape l.seedWidth Z k src (Nat.le_mul_of_pos_right _ D.base_pos) group
  have tailPos : 0 < tail τ J := Nat.mul_pos liveTau (Nat.succ_pos _)
  obtain ⟨signed,retained⟩:=chosen_reader_room D S h k (tail τ J) g p drift degree f quota base field wire hist tailPos high
  exact ⟨packed,lanes,fieldWord.trans ((Nat.div_le_self h 2).trans machine),signed.trans machine,
    retained.trans machine,(Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide : 1<2) _)⟩

end Hierarchy.DescentDatedSeedStartup

end OAI
