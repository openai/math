import OAI.Hierarchy.DescentSeedTokenWidths
import OAI.Hierarchy.DescentSeedTokenCharge
import OAI.Hierarchy.DescentSeedTokenLaneFit
import OAI.Hierarchy.DescentSeedStageCharge
import OAI.Hierarchy.DescentSeedInitialBlockKeys

namespace OAI
/-! # Bit-invoice for the real first ballot-dependent primitive archive -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentDyadicSpan DescentCompiler DescentCompiler.TerminalScale
open DescentPrimitivePalette DescentSixParty DescentSIMDLookup Catalyst Filter
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

set_option maxRecDepth 4096 in
theorem issued_tokens (t f g reset e τ B factor : ℕ)
    (κ : ℕ := 1+(hostRate t reset+capRate D t g)*(t+1)+8+cutRate t f g)
    (κok : 1+(hostRate t reset+capRate D t g)*(t+1)+8+cutRate t f g ≤ κ)
    (τfit : κ+3+3+(e+5) ≤ τ) (positive : 0 < B)
    (budget : κ+3+6 ≤ B) (width : 2*((2+hostRate t reset*(t+1)+(κ+3)+1+1)+5+e) ≤ B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M q p s Z base w : ℕ,let S:=stageNumbers D t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let G:=S.groupCount 0
      let R:=S.copies
      let H:=span M
      let m:=paletteLanes D op s Z h k
      2^h ≤ M → 0 < q → q ≤ scale J e → h ≤ 32*(q*p) → s ≤ h → Z ≤ s → w+1 ≤ factor*h →
      ∀ {cp pins : ℕ} (X : Approximation F cp pins) (host : Vertex X↪Fin H),
      (ticks X D op R s Z h k H G m base host w+
        7*DescentStaticWordColumn.names (program X D op R s Z h k H G m base host w))*(w+1)*2^J ≤
          2*(M*(S.copies*p)) :=by
  let P:=Fintype.card DescentPackedSeed.Primitive.Plan
  let α:=κ+3
  let C:=1000000000*(P+1)*(factor+1)
  filter_upwards [calibration_at D t f g reset α α e C 0 τ (by omega) B positive (by omega),
    primitive_rate D op B positive,shared_token_tables,age_room B positive,eventually_ge_atTop 1]
    with h paying rates tables age hp
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M q p s Z base w ambient qs qfit pack sp zp word cp pins X host
  let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let r:=2^k
  let a:=DescentPackedSeed.Primitive.roleBits s
  let b:=printedBits D s Z op
  let H:=span M
  let m:=paletteLanes D op s Z h k
  let G:=S.groupCount 0
  let A:=DescentPackedSeed.Primitive.pieces h s
  let older:=32*factor*digitsNeeded s
  let fresh:=16*factor*max (a*r) b
  let price:=(ticks X D op S.copies s Z h k H G m base host w+
    7*DescentStaticWordColumn.names (program X D op S.copies s Z h k H G m base host w))*(w+1)
  have κcap : r ≤ scale J κ:=(groupRateAt t J S.hostGain S.capGain (cutRate t f g)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (J+1) κok))
  have cap : r ≤ scale J α:=κcap.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right (J+1) (by omega : κ ≤ κ+3)))
  have monotone (d : ℕ) (le : d ≤ α) : scale J d ≤ scale J α :=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  obtain ⟨pbits,sbits,digits⟩:=rates s Z zp sp
  have short : max (a*r) b ≤ scale J α :=max_le
    ((Nat.mul_le_mul sbits κcap).trans_eq (by rw [scale_mul,add_comm]))
    (pbits.trans (monotone 3 (by omega)))
  have dg:=digits.trans (monotone 2 (by omega))
  have deep:=token_epoch_room h B α hp age.1 budget
  have active : 0 < A :=(occupancy h (8*digitsNeeded s) (by unfold digitsNeeded;positivity)
    (by nlinarith only [deep,dg])).1
  have used:=pitch_fill h (8*digitsNeeded s) (w+1) factor (by unfold digitsNeeded;positivity)
    (by nlinarith only [deep,dg]) word
  have stock : w+1 ≤ A*older :=by simpa only [A,DescentPackedSeed.Primitive.pieces,older,show 4*factor*(8*digitsNeeded s)=32*factor*digitsNeeded s by ring] using used
  obtain ⟨now,small,lookup,_,fill⟩:=token_lane_fit h (w+1) factor a b r (Nat.zero_lt_succ _) (Nat.two_pow_pos _)
    (by nlinarith only [deep,short]) word
  have radixCap : r ≤ h := (Nat.le_mul_of_pos_left r now).trans small
  obtain packs|bad:=tables s H G r m (ambient.trans (span_ge M)) active radixCap small lookup
  · obtain ⟨one,two,three⟩:=packs
    have oldCount : Fintype.card (Old X) ≤ H :=by
      let inclusion : Old X ↪ Fin H := ⟨fun v=>host (.inl v),fun _ _ eq=>Sum.inl.inj (host.injective eq)⟩
      simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding inclusion
    have bill:=version_cost X D op S.copies s Z h k H G m base host w older fresh oldCount (span_pos M)
      (S.seed_population_eq (k:=k) rfl) active now (ambient.trans (span_ge _)) one two three stock fill
    have tops:=span_le M
    have live := (Nat.two_pow_pos h).trans_le ambient
    have hh : H ≤ 3*M:=by dsimp [H];omega
    let hi:=3*factor*hostFee r
    let lo:=3*privateFee older fresh
    have hostZero : S.hostSize 0=M :=by
      change M*_ ^ (0:ℕ)=M
      simp
    have radixEq : S.radix=r :=rfl
    have due : price ≤ S.hostSize 0*h*hi+S.hostSize 0*(S.groupCount 0*S.radix)*lo :=by
      apply bill.trans
      have first:=Nat.mul_le_mul_right (hostFee r) (Nat.mul_le_mul hh word)
      have second:=Nat.mul_le_mul_right (privateFee older fresh) (Nat.mul_le_mul_right (G*r) hh)
      apply (Nat.add_le_add first second).trans_eq
      rw [hostZero,radixEq]
      change _=M*h*hi + M*(G*r)*lo
      dsimp only [hi,lo]
      ring
    let rate:=scale J α
    have oneRate : 1 ≤ rate:=Nat.two_pow_pos _
    have hcost : hi ≤ rate*C :=by
      dsimp only [hi,hostFee,C,P]
      nlinarith only [Nat.mul_le_mul_left factor cap,Nat.mul_le_mul_left factor oneRate,
        Nat.mul_le_mul_left (factor*P) oneRate,Nat.zero_le (rate*factor*P),Nat.zero_le (P*rate)]
    have lcost : lo ≤ rate*C :=by
      dsimp only [lo,privateFee,fresh,older,C]
      nlinarith only [Nat.mul_le_mul_left factor dg,Nat.mul_le_mul_left factor short,
        Nat.zero_le (P*rate),Nat.zero_le (rate*factor*P),Nat.zero_le rate,Nat.zero_le (factor*rate)]
    obtain ⟨receipt,sum⟩:=zero_receipt S h hi lo price due
    have result:=paying M q p hi lo qs qfit pack (by simpa using hcost) (by simpa using lcost) (atZero S price) receipt
    change (∑i : Fin (S.length+1),atZero S price i)*2^J ≤ 2*(M*(S.copies*p)) at result
    rw [sum] at result
    exact result
  · exact False.elim ((Nat.two_pow_pos k).ne' bad)

end
end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
