import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.DescentFixedRotorRates
import OAI.Hierarchy.DescentChosenExteriorHeadWidths

namespace OAI
/-! # The fixed rotor and the actual initial and terminal dimensions of the dyadic host -/
namespace Hierarchy.DescentSixParty.EpochRotor
open DescentCompiler TerminalScale DescentResetInvoice DescentHostDegree Catalyst Filter
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {G : PoweredGadget F} (c : EpochRotor G)
variable (τ β h M : ℕ) {cp n : ℕ} (X : Approximation F cp n)
local notation "J" => Nat.log 2 h/(2*β)
local notation "tb" => tail τ J
local notation "cut" => cutRate c.rounds c.f c.g
local notation "k" => groupBits c.rounds J (hostRate c.rounds c.reset) (capRate G c.rounds c.g) cut
local notation "S" => stageNumbers G c.rounds J c.f c.g c.reset M tb
local notation "j" => headChunk G S
local notation "rest" => headRest G S k tb
local notation "p" => headGrain G S k h
local notation "s" => (S).firstWidth G.b p
local notation "U" => G.b^(c.rounds*J)*G.b
local notation "q" => 2^j*U
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "κ" => 1+(hostRate c.rounds c.reset+capRate G c.rounds c.g)*(c.rounds+1)+8+cut

/-- A single witness fixes the board and its stored word size for all stages of this input. -/
structure HostGeometry where
  ordinary : OrdinaryRates G S k cut
  reset : ResetRates G S k (atRound c.rounds) c.nodesLog c.degree c.multiplicity c.f c.g cut tb
  board : reset.board=c.board
  bits : reset.bitsR=c.bits
  age : 0<(S).height
  width : (S).groupWidth k tb 0+k=j+(j+rest)
  base : (S).baseGroups=2^tb
  branch : G.b≤2^(S).capGain
  positive : 0<p
  room : 10*(X.size+1)≤(S).initialSites
  shorten : reentryRate c.degree c.multiplicity*(1-(2-G.rate)/4)^(S).rounds≤1/2
  wFit : NativeBranch.binLimit («k»:=k) S≤W
  qFit : NativeBranch.localLimit G S≤q
  qh : 0<q
  sitesPositive : 0<(S).hostSize (S).length
  first : 2^J ≤ s
  scaled : 16*(2^j*s)≤h ∧ h≤32*(2^j*s)
  copies : (S).copies=2^(j+(j+rest))
  fits : ∀w,h≤w→s<2^w

theorem host_geometry (large : 20≤β) (reserve : 2*localSocketRate G c.rounds c.g≤τ)
    (budget : 2*(localSocketRate G c.rounds c.g+(τ+κ+4))+Nat.clog 2 G.b*(c.rounds+1)≤β) :
    ∀ᶠ h : ℕ in atTop,∀{cp n M : ℕ} (X : Approximation F cp n),
      10*(X.size+1)≤M → Nonempty (c.HostGeometry τ β h M X) :=by
  filter_upwards [early_native_packing G c.rounds c.f c.g c.reset τ β large reserve budget,
    eventually_ge_atTop (2^(2*β):ℕ)] with h packed late
  intro cp n M X opened
  let J₀:=Nat.log 2 h/(2*β)
  have age : 0<J₀:=Nat.div_pos (Nat.le_log_of_pow_le (by decide) late) (by omega)
  obtain ⟨ord,r,board,bits⟩:=c.issued_rates J₀ M (tail τ J₀) age
  let sched:=stageNumbers G c.rounds J₀ c.f c.g c.reset M (tail τ J₀)
  let kb:=groupBits c.rounds J₀ (hostRate c.rounds c.reset) (capRate G c.rounds c.g) cut
  let chunk:=headChunk G sched
  let grain:=headGrain G sched kb h
  let seats:=sched.firstWidth G.b grain
  obtain ⟨dims,copies,lower,upper,cover⟩:=packed M
  have first : 2^J₀≤ seats:=lower
  have scaled : 16*(2^chunk*seats)≤h:=upper
  have fit : seats≤h := calc
    seats≤2^chunk*seats := Nat.le_mul_of_pos_left seats (Nat.two_pow_pos _)
    _≤16*(2^chunk*seats) := by omega
    _≤h:=scaled
  have widthPos : 0<seats := (Nat.two_pow_pos _).trans_le first
  have grainPos : 0<grain := by
    by_contra! hz
    change 0<(grain*_)*G.b at widthPos
    rw [Nat.eq_zero_of_le_zero hz,Nat.zero_mul,Nat.zero_mul] at widthPos
    exact Nat.lt_irrefl _ widthPos
  have units : 0<G.b^(c.rounds*J₀)*G.b := Nat.mul_pos (pow_pos G.base_pos _) G.base_pos
  have qFits := (Nat.le_pow_clog (by decide : 1<2) (NativeBranch.localLimit G sched)).trans
    (Nat.le_mul_of_pos_right (2^chunk) units)
  have hostPos : 0<sched.hostSize sched.length:=by
    have sites : 0<M:=by omega
    change 0<M*(2^sched.hostGain*2^kb)^sched.length
    exact Nat.mul_pos sites (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) _)
  exact ⟨⟨ord,r,board,bits,age,dims,r.base,c.branch,grainPos,opened,c.contracts,le_rfl,qFits,
    Nat.mul_pos (Nat.two_pow_pos _) units,hostPos,first,⟨scaled,cover⟩,copies,
    fun w hw=> (fit.trans hw).trans_lt Nat.lt_two_pow_self⟩⟩

/-- The two cutoffs are fixed before either the observed height or the input circuit is chosen. -/
theorem cofinal_host_geometry :
    ∃τ₀ : ℕ, ∀τ≥τ₀, ∃β₀ : ℕ, ∀β≥β₀, ∀ᶠ h : ℕ in atTop,
      ∀{cp n M : ℕ} (X : Approximation F cp n), 10*(X.size+1)≤M →
        Nonempty (c.HostGeometry τ β h M X) :=by
  let a:=localSocketRate G c.rounds c.g
  refine ⟨2*a,fun τ reserve=>?_⟩
  let budget:=2*(a+(τ+κ+4))+Nat.clog 2 G.b*(c.rounds+1)
  exact ⟨max 20 budget,fun β paid=>c.host_geometry τ β
    ((le_max_left ..).trans paid) reserve ((le_max_right ..).trans paid)⟩

end
end Hierarchy.DescentSixParty.EpochRotor

end OAI
