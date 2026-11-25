import OAI.Hierarchy.DescentTerminalHostInvoice
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Every epoch's common-word and private small-field invoices on the actual scheduled rectangles -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
open scoped BigOperators
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem host_mono (S : AtomSchedule) {i j : ℕ} (ij : i≤j) (radix : 0<S.radix) :
    S.hostSize i≤S.hostSize j :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.mul_pos (Nat.two_pow_pos _) radix) ij)

theorem short_mono (J : ℕ) {a b : ℕ} (ab : a≤b) : scale J a≤scale J b :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ab)

theorem product_rate (h J q p e s : ℕ) (qPos : 0<q) (qFit : q≤scale J e)
    (word : h≤32*(q*p)) (large : scale J (s+5+e)≤h) : scale J s≤p := by
  have cost : 32*q*scale J s≤h := by
    have c : 32≤scale J 5 := by
      change 2^5≤2^(5*(J+1))
      exact Nat.pow_le_pow_right (by decide) (by omega)
    calc
      _ ≤ scale J 5*scale J e*scale J s := Nat.mul_le_mul_right _ (Nat.mul_le_mul c qFit)
      _ = scale J (s+5+e) := by rw [scale_mul,scale_mul];congr 1;omega
      _ ≤ _ := large
  exact (Nat.le_of_mul_le_mul_left (show 32*q*scale J s≤32*q*p by simpa [Nat.mul_assoc] using cost.trans word)
    (by omega))

/-- Each row is charged in its genuine age. The first term is per common host, and the second
is per slot in the host×group×block rectangle. -/
theorem stage_ledger (t J f g reset M τ h p high low : ℕ)
    (S : AtomSchedule) (config : S=stageNumbers G t J f g reset M (tail τ J))
    (hostBought : ((S.length+1)*high)*h≤p*2^(tail τ J))
    (itemBought : (S.length+1)*(2^S.hostGain)^S.length*low*2^J≤p)
    (fee : Fin (S.length+1)→ℕ)
    (charged : ∀i,fee i≤S.hostSize i.val*h*high+
      S.hostSize i.val*(S.groupCount i.val*S.radix)*low) :
    (∑i,fee i)*2^J≤2*(M*(S.copies*p)) := by
  have base : 0<S.radix:=by rw [config];exact Nat.two_pow_pos _
  have hs:=terminal_host_price G t J f g reset M (tail τ J) h p ((S.length+1)*high)
    (hostBought.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))))
  dsimp only at hs
  rw [←config] at hs
  have pay (i : Fin (S.length+1)) : fee i≤ S.hostSize S.length*h*high+
      (M*S.copies)*(2^S.hostGain)^S.length*low := by
    have last:=Nat.le_of_lt_succ i.isLt
    have slot:=S.slot_reserve last
    have init : S.initialSites=M := by rw [config];rfl
    rw [init] at slot
    exact (charged i).trans (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (host_mono S last base)))
      (Nat.mul_le_mul_right _ slot))
  have all:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pay i)
  have result : (∑i,fee i)*2^J ≤ (S.length+1)*(S.hostSize S.length*h*high+
      (M*S.copies)*(2^S.hostGain)^S.length*low)*2^J := by
    apply Nat.mul_le_mul_right
    simpa using all
  apply result.trans
  have priv:=Nat.mul_le_mul_left (M*S.copies) itemBought
  nlinarith only [hs,priv]

/-- Exponent choices are uniform in the history. τ is selected first for common-host rent.
The later choice of B makes each packed private slot's bit cost negligible against p. -/
theorem calibration_at (t f g reset s a e c d τ : ℕ)
    (tailFit : s+d+3+(e+5)≤τ) :
    ∀B : ℕ,0<B→2*((2+hostRate t reset*(t+1)+a+(d+1)+1)+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B);
      ∀M q p high low : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        0<q→q≤scale J e→h≤32*(q*p)→
        high≤scale J s*(c*(tail τ J+1)^d)→low≤scale J a*(c*(tail τ J+1)^d)→
        ∀fee : Fin (S.length+1)→ℕ,(∀i,fee i≤S.hostSize i.val*h*high+
           S.hostSize i.val*(S.groupCount i.val*S.radix)*low)→
        (∑i,fee i)*2^J≤2*(M*(S.copies*p)) := by
  intro B hB chosen
  let n:=2+hostRate t reset*(t+1)+a+(d+1)+1
  filter_upwards [age_room B hB,eventually_late (t+2+c*(τ+1)^d) B hB] with h real late
  let J:=Nat.log 2 h/(2*B)
  have positive : 0<J:=real.1
  have lot : c*(τ+1)^d≤2^(J+1):=(by omega : c*(τ+1)^d≤J).trans
    ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n:=J+1)).le)
  dsimp only
  intro M q p high low qpos qMax pack hh ll fee receipt
  let S:=stageNumbers G t J f g reset M (tail τ J)
  have rounds : S.length+1≤scale J 2 := by
    have tBound : t+2≤2^(J+1) := (by omega : t+2≤J).trans
      ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n:=J+1)).le)
    calc
      _ ≤ (t+2)*(J+1) := by change (t+1)*J+1≤_;nlinarith
      _ ≤ 2^(J+1)*2^(J+1) := Nat.mul_le_mul tBound (Nat.lt_two_pow_self (n:=J+1)).le
      _ = _ := by unfold scale;rw [←pow_add];congr 1;ring
  have hField : h≤p*scale J (5+e) := by
    have cFit : 32≤scale J 5 := by
      change 2^5≤2^(5*(J+1));exact Nat.pow_le_pow_right (by decide) (by omega)
    exact pack.trans (by rw [←scale_mul];nlinarith only [Nat.mul_le_mul_left p (Nat.mul_le_mul cFit qMax)])
  have hostWorks : (S.length+1)*high≤scale J (2+s)*(c*(tail τ J+1)^d) := by
    rw [←scale_mul,Nat.mul_assoc]
    exact Nat.mul_le_mul rounds hh
  have shared:=reserve c d (2+s) (5+e) τ J ((S.length+1)*high) h p lot (by omega) hostWorks hField
  have nativeGain : (2^S.hostGain)^S.length≤scale J (hostRate t reset*(t+1)) := by
    change (2^(hostRate t reset))^((t+1)*J)≤_
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  have lowWork : low≤scale J (a+(d+1)) := by
    rw [←scale_mul]
    exact ll.trans (Nat.mul_le_mul_left _ (logarithmic c d τ J lot))
  have privateWork : (S.length+1)*(2^S.hostGain)^S.length*low*2^J≤scale J n := by
    apply (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul rounds nativeGain) lowWork)
      (show 2^J≤scale J 1 by unfold scale;simp;omega)).trans
    rw [scale_mul,scale_mul,scale_mul]
    apply short_mono
    unfold n
    omega
  have size : scale J (n+5+e)≤h := by
    have left:=Nat.mul_le_mul_left (n+5+e) (show J+1≤2*J by omega)
    have right : J*(2*(n+5+e))≤J*B := Nat.mul_le_mul_left J chosen
    have exp : (n+5+e)*(J+1)≤J*B := by nlinarith only [left,right]
    exact (Nat.pow_le_pow_right (by decide) exp).trans (by
      rw [pow_mul];nlinarith only [real.2])
  exact stage_ledger G t J f g reset M τ h p high low S rfl shared
    (privateWork.trans (product_rate h J q p e n qpos qMax pack size)) fee receipt

theorem calibration (t f g reset s a e c d : ℕ) :
    let τ:=s+d+3+(e+5)
    let n:=2+hostRate t reset*(t+1)+a+(d+1)+1
    ∀B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B);
      ∀M q p high low : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        0<q→q≤scale J e→h≤32*(q*p)→
        high≤scale J s*(c*(tail τ J+1)^d)→low≤scale J a*(c*(tail τ J+1)^d)→
        ∀fee : Fin (S.length+1)→ℕ,(∀i,fee i≤S.hostSize i.val*h*high+
           S.hostSize i.val*(S.groupCount i.val*S.radix)*low)→
        (∑i,fee i)*2^J≤2*(M*(S.copies*p)) := by
  exact calibration_at G t f g reset s a e c d _ le_rfl

end Hierarchy.DescentCompiler.TerminalScale

end OAI
