import OAI.Hierarchy.DescentDatedResetBook
import OAI.Hierarchy.DescentDatedEventualAddress

namespace OAI
/-! # Uniform numerical extents of the primed reset and its signed routing -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement
open DescentPackedWalsh DescentGLPacked DescentSIMDLookup DescentDatedAddressBook Filter
noncomputable section
set_option quotPrecheck false

variable {ι : ℕ→Type*} (p : ∀h,ι h→Placement)
  (pay gain : ∀h,ι h→ℕ) (positive : ∀h i,0<(p h i).geo.bits)
local notation "E" => fun h i=>(p h i).estimator (pay h i) (gain h i) (positive h i)

structure ScalarRoom (p : ∀h,ι h→Placement) (pay gain : ∀h,ι h→ℕ) : Prop where
  hosts : Bounded (fun h i=>(p h i).geo.hosts)
  ports : Bounded (fun h i=>(p h i).geo.ports)
  pitch : Bounded (fun h i=>(p h i).geo.pitch)
  payload : ∃C : ℕ,∀ᶠ h:ℕ in atTop,∀i,pay h i≤C*h
  axis : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).geo.high+(p h i).geo.low≤K*(Nat.log 2 h+1)^2
  lanes : ∀ᶠ h:ℕ in atTop,∀i,let g:=(p h i).geo;laneBits (g.high+g.low) (pay h i) g.bits=g.low
  small : ∀ᶠ h:ℕ in atTop,∀i,8*(p h i).geo.bits≤pay h i/2
  gains : ∀ᶠ h:ℕ in atTop,∀i,gain h i≤(p h i).geo.bits
  routeBits : ∀ᶠ h:ℕ in atTop,∀i,let g:=(p h i).geo;(g.bits+g.bits)*2^g.low≤pay h i/2
  square : ∀ᶠ h:ℕ in atTop,∀i,let g:=(p h i).geo;(g.high+g.low)*(g.high+g.low)≤pay h i/2

local macro "reset_rate" : tactic =>
  `(tactic| repeat' first
    | assumption
    | apply Bounded.add
    | apply Bounded.mul
    | apply Bounded.max'
    | apply Bounded.sub
    | apply Bounded.div
    | apply Bounded.padded
    | apply Bounded.logPage
    | apply Bounded.const)

theorem remix_span_rate (b : ScalarRoom p pay gain) :
    Bounded (fun h i=>(p h i).remixEnd (pay h i) (gain h i) (positive h i)-(p h i).middle) := by
  obtain ⟨K,axis⟩:=b.axis
  obtain ⟨C,hw⟩:=b.payload
  have H:=b.hosts
  have D:=b.ports
  have pitch:=b.pitch
  have late : ∀ᶠ h:ℕ in atTop,∀i,((E) h i).dim≤1*h := by
    filter_upwards [axis,DescentWalshPrecision.eventually_log_square K] with h ax lg
    intro i
    change (p h i).geo.high + (p h i).geo.low ≤ 1*h
    simpa only [Nat.one_mul] using (ax i).trans lg
  have size:=Bounded.pow_of_linear late
  have dim : Bounded (fun h i=>((E) h i).dim) := size.of_le fun _ _=>Nat.lt_two_pow_self.le
  have high : Bounded (fun h i=>2^(p h i).geo.high) :=
    size.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have target : Bounded (fun h i=>(p h i).routedHosts) := by
    change Bounded (fun h i=>((1+(p h i).geo.ports)+((E) h i).dim)*(p h i).geo.hosts)
    reset_rate
  have hosts : Bounded (fun h i=>((E) h i).hosts) :=
    target.of_le fun h i=>((p h i).estimator_columns (pay h i) (gain h i) (positive h i)).2.2.2.2.le
  have sheet : Bounded (fun h i=>page (p h i).geo.hosts (p h i).geo.high) := by
    apply Bounded.of_le (le:=fun h i=>page_le (p h i).geo.hosts (p h i).geo.high)
    reset_rate
  have suffix : Bounded (fun h i=>(p h i).suffixWords) := by
    apply Bounded.of_le (le:=fun h i=>(p h i).suffix_le)
    change Bounded (fun h i=>
      (((E) h i).dim+2)*page (p h i).geo.hosts (p h i).geo.high+
      (2*((E) h i).dim+8)*((p h i).geo.hosts+1)+4*((p h i).geo.ports*(p h i).geo.pitch+1)+
      2*((p h i).geo.hosts*(p h i).geo.ports+1)+
      11*((p h i).geo.hosts*(((E) h i).dim+1)+(p h i).geo.hosts*(p h i).geo.ports+1)+
      2*(((p h i).geo.hosts*(((E) h i).dim+1)+(p h i).geo.hosts*(p h i).geo.ports)*2^(p h i).geo.high+1)+1)
    reset_rate
  obtain ⟨A,hc⟩:=hosts
  have fixed : Bounded (fun h i=>((E) h i).staticEnd-((E) h i).origin) := by
    refine ⟨6*(A+C+1)+23,?_⟩
    filter_upwards [EstimatorArena.eventually_immutable_extent A C K,hc,hw,axis,b.lanes,b.small,b.gains] with h bound hH wh ax lanes small gains
    intro i
    exact bound _ (hH i) (wh i) (ax i) (lanes i) (small i) (gains i)
  have hosts' : Bounded (fun h i=>((E) h i).hosts):=⟨A,hc⟩
  have mutableRoom : Bounded (fun h i=>((E) h i).endAddress-((E) h i).origin) := by
    apply Bounded.of_le (x:=fun h i=>(((E) h i).staticEnd-((E) h i).origin)+
      12*(((E) h i).dim+1)*(((E) h i).hosts+1)*2^((E) h i).dim)
    · reset_rate
    · intro h i
      have area:=((E) h i).mutable_extent
      have zero : ((E) h i).dataGap=0:=rfl
      rw [zero,Nat.add_zero] at area
      omega
  have root : Bounded (fun h i=>2^(pay h i/2)) := Bounded.pow_of_linear (K:=C)
    (hw.mono fun h wh i=>(Nat.div_le_self ..).trans (wh i))
  have gates : Bounded (fun h i=>DescentGLControlCode.Count ((E) h i).dim) := by
    apply Bounded.of_le (x:=fun h i=>3*((E) h i).dim*((E) h i).dim)
    · reset_rate
    · intro h i;exact DescentGLNielsen.length_le _
  have route : Bounded (fun h i=>(p h i).remixEnd (pay h i) (gain h i) (positive h i)-((E) h i).endAddress) := by
    let work (h : ℕ) (i : ι h) :=
      let e:= (E) h i
      let n:=DescentGLControlCode.Count e.dim
      let q:=2^(pay h i/2)
      let patches:=(p h i).routedHosts*2^(p h i).geo.high
      4*((1+n)*q+n+e.dim*2^(p h i).geo.high+1)+2*(patches+1)+n+(7*n+1)*(2*(patches+1)+q)
    apply Bounded.of_eventually_le (b:=work)
    · dsimp only [work];reset_rate
    · filter_upwards [b.routeBits,b.square] with h routes squares
      intro i
      have used:=BankImage.Dated.paid_extent ((E) h i).endAddress (p h i).routedHosts
        (p h i).geo.high (p h i).geo.low (p h i).geo.bits (pay h i) (routes i) (squares i)
      change (p h i).remixEnd (pay h i) (gain h i) (positive h i)≤((E) h i).endAddress+
        4*_+2*_+_+_*_ at used
      dsimp only at used
      dsimp only [work]
      have dim_eq : ((E) h i).dim = (p h i).geo.high + (p h i).geo.low := rfl
      rw [dim_eq]
      omega
  apply ((suffix.add mutableRoom).add route).of_le
  intro h i
  have pre := (p h i).end_eq
  have low:= (p h i).estimator_range (pay h i) (gain h i) (positive h i)
  change (p h i).endAddress≤((E) h i).staticEnd ∧ _ ∧ _ at low
  change ((p h i).remixEnd (pay h i) (gain h i) (positive h i))-(p h i).middle≤
    (p h i).suffixWords+(((E) h i).endAddress-(p h i).endAddress)+
      ((p h i).remixEnd (pay h i) (gain h i) (positive h i)-((E) h i).endAddress)
  omega

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement

end OAI
