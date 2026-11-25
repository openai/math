import OAI.Hierarchy.TaggedWideDualControlRows
import OAI.Hierarchy.TaggedWidePortBill
import OAI.Hierarchy.TaggedWideControl
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # Uniform pricing of the two native controllers and the purchased cuts -/

noncomputable section
namespace Hierarchy.Tagged.WidePhysicalBill
open Filter Real
open scoped Classical BigOperators

/-- The integers entering the physical board identity, before any estimate. -/
structure Charges (types : ℕ) where
  rows : Bool → ℕ
  cpu : Bool → ℕ
  flagWord : ℕ
  site : ℕ
  cuts : Fin types → ℕ
  sockets : Fin types → ℕ
  selectors : ℕ
  workspace : ℕ
  external : ℕ

def Charges.total {types : ℕ} (c : Charges types) (h : ℕ) : ℕ :=
  let m := fun b => controlHeight h (c.rows b)
  c.cpu false+c.cpu true+c.flagWord+c.site+(∑i,c.cuts i)+
    29*(pins h h+28*pins (m false) (m false)+28*pins (m true) (m true))+
    (c.selectors+c.workspace)+c.external+(∑i,c.sockets i)

def factor (N types : ℕ) : ℝ := 160000000*((N:ℝ)+1)^2+2*types+20000

/-- A raw controller row bound pays its power-of-two padding, the CPU's
per-row work, and every occurrence of that controller's address-sized pins. -/
theorem at_parent {h w types N : ℕ} (c : Charges types) {R : ℝ}
    (hh : 0<h) (hw : h≤w) (one : 1≤R) (small : R≤(2:ℝ)^h)
    (rows : ∀b,(c.rows b:ℝ)≤(2:ℝ)^h*R)
    (cpu : ∀b,c.cpu b≤20000000*2^(controlHeight h (c.rows b))*(h+1)*(N+1)^2)
    (selectors : (c.selectors:ℝ)≤(2:ℝ)^h*h*R)
    (flag : (c.flagWord:ℝ)≤(2:ℝ)^h*w*R) (site : (c.site:ℝ)≤(2:ℝ)^h*w*R)
    (space : (c.workspace:ℝ)≤(2:ℝ)^h*w*R) (ports : (c.external:ℝ)≤(2:ℝ)^h*w*R)
    (cuts : ∀i,(c.cuts i:ℝ)≤(2:ℝ)^h*w*R) (sockets : ∀i,(c.sockets i:ℝ)≤(2:ℝ)^h*w*R) :
    (∀j,(WideHost.dualControlRows h (c.rows false) (c.rows true) j:ℝ)≤(2:ℝ)^h*R) ∧
    (c.total h:ℝ)≤factor N types*((2:ℝ)^h*w*R) ∧
    (h:ℝ)*2^h+c.selectors≤2*((2:ℝ)^h*h*R) := by
  let V := (2:ℝ)^h*w*R
  have hr : 0≤R := zero_le_one.trans one
  have pad b := control_padding hh one small (rows b)
  have hww : (h:ℝ)≤w := by exact_mod_cast hw
  have h1 : (h:ℝ)+1≤2*w := by exact_mod_cast (show h+1≤2*w by omega)
  have native (b : Bool) : (c.cpu b:ℝ)≤80000000*((N:ℝ)+1)^2*V := by
    have cap : (c.cpu b:ℝ)≤20000000*(2:ℝ)^(controlHeight h (c.rows b))*((h:ℝ)+1)*((N:ℝ)+1)^2 := by
      exact_mod_cast cpu b
    apply cap.trans
    calc
      _ ≤ 20000000*(2*(2:ℝ)^h*R)*(2*w)*((N:ℝ)+1)^2 := by
        gcongr; first | exact (pad b).2.2.2
      _ = _ := by dsimp [V]; ring
  have sockets₀ (b : Bool) : (pins (controlHeight h (c.rows b)) (controlHeight h (c.rows b)):ℝ)≤12*V := by
    apply (control_port_bill _ h (pad b).2.2.1 (pad b).2.2.2).trans
    dsimp [V]
    calc
      _ ≤ 6*(2*(2:ℝ)^h*R)*w := by gcongr
      _ = _ := by ring
  have top : (2:ℝ)^h≤(2:ℝ)^h*R := le_mul_of_one_le_right (by positivity) one
  have tag : (pins h h:ℝ)≤6*V := by
    apply (control_port_bill h h (by omega) top).trans
    dsimp [V]
    calc
      _ ≤ 6*((2:ℝ)^h*R)*w := by gcongr
      _ = _ := by ring
  have sel : (c.selectors:ℝ)≤V := selectors.trans (by dsimp [V]; gcongr)
  have sum (f : Fin types→ℕ) (p : ∀i,(f i:ℝ)≤V) : (∑i,(f i:ℝ))≤(types:ℝ)*V := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => p i)
  refine ⟨WideHost.dual_control_count _ _ _ top (rows false) (rows true),?_,?_⟩
  · change (c.total h:ℝ)≤factor N types*V
    unfold Charges.total factor
    push_cast
    change (c.flagWord:ℝ)≤V at flag
    change (c.site:ℝ)≤V at site
    change (c.workspace:ℝ)≤V at space
    change (c.external:ℝ)≤V at ports
    have pos : 0≤V := by dsimp [V]; positivity
    linarith only [native false,native true,flag,site,space,ports,sel,sum _ cuts,sum _ sockets,
      tag,sockets₀ false,sockets₀ true,pos]
  · have low := le_mul_of_one_le_right (by positivity : 0≤(2:ℝ)^h*h) one
    linarith only [selectors,low]

/-- Finite component estimates may have independent constants and logarithmic
degrees. The same two numbers can be used for every component thereafter. -/
theorem common {κ A : ℝ} {I : Type*} [Fintype I]
    (base fee : I → WideParent κ A → ℝ) (positive : ∀ i x,0≤base i x)
    (bounded : ∀i,∃ c p : ℝ, 0≤c ∧ 0≤p ∧
      ∀ᶠ x in WideParent.large κ A,fee i x≤c*(base i x*(log (x.h:ℝ))^p)) :
    ∃ C P : ℝ, 1≤C ∧ 0≤P ∧ ∀ᶠ x in WideParent.large κ A,
      ∀i,fee i x≤C*(base i x*(log (x.h:ℝ))^P) := by
  choose c p hc hp per using bounded
  let C := 1+∑i,c i
  let P := ∑i,p i
  have hC : 1≤C := by dsimp [C]; linarith only [Finset.sum_nonneg (s:=Finset.univ) (fun i _=>hc i)]
  have hP : 0≤P := Finset.sum_nonneg (fun i _=>hp i)
  have large : Tendsto (fun x : WideParent κ A=>(x.h:ℝ)) (WideParent.large κ A) atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  refine ⟨C,P,hC,hP,?_⟩
  filter_upwards [eventually_all.mpr per,(tendsto_log_atTop.comp large).eventually_ge_atTop 1] with x rx loghi i
  apply (rx i).trans
  have ci : c i≤C := by
    have hi := Finset.single_le_sum (s:=Finset.univ) (fun j _=>hc j) (Finset.mem_univ i)
    dsimp [C]; linarith
  have pi : p i≤P := Finset.single_le_sum (fun j _=>hp j) (Finset.mem_univ i)
  exact mul_le_mul ci (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le loghi pi) (positive i x))
    (mul_nonneg (positive i x) (Real.rpow_nonneg (zero_le_one.trans loghi) _)) (zero_le_one.trans hC)

/-- The component estimates refer to raw rows and native costs. Padding the two
sorts and charging the 57 control banks remain consequences of these estimates. -/
structure Receipts {types : ℕ} (h w N : ℕ) (c : Charges types) (R : ℝ) : Prop where
  rows : ∀b,(c.rows b:ℝ)≤(2:ℝ)^h*R
  cpu : ∀b,c.cpu b≤20000000*2^(controlHeight h (c.rows b))*(h+1)*(N+1)^2
  selectors : (c.selectors:ℝ)≤(2:ℝ)^h*h*R
  flag : (c.flagWord:ℝ)≤(2:ℝ)^h*w*R
  site : (c.site:ℝ)≤(2:ℝ)^h*w*R
  workspace : (c.workspace:ℝ)≤(2:ℝ)^h*w*R
  external : (c.external:ℝ)≤(2:ℝ)^h*w*R
  cuts : ∀i,(c.cuts i:ℝ)≤(2:ℝ)^h*w*R
  sockets : ∀i,(c.sockets i:ℝ)≤(2:ℝ)^h*w*R

/-- A single constant and degree fit the physical board, its honest selector
tape, and the actual 57 recursive control row counts on all wide parents. -/
theorem eventually_bill {κ A K p : ℝ} {types N : ℕ} (c : WideParent κ A → Charges types)
    (hK : 1≤K) (hp : 0≤p)
    (paid : ∀ᶠ x in WideParent.large κ A,Receipts x.h x.w N (c x) (K*(log (x.h:ℝ))^p)) :
    ∃ C d : ℝ, 1≤C ∧ 0≤d ∧ ∀ᶠ x in WideParent.large κ A,
      (∀j,(WideHost.dualControlRows x.h ((c x).rows false) ((c x).rows true) j:ℝ)≤
        C*((2:ℝ)^x.h*(log (x.h:ℝ))^d)) ∧
      ∀ cost selectors : ℕ,cost≤(c x).total x.h → selectors≤(c x).selectors →
        (cost:ℝ)≤C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^d) ∧
        (x.h:ℝ)*2^x.h+selectors≤C*((2:ℝ)^x.h*x.h*(log (x.h:ℝ))^d) := by
  have grow : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop := tendsto_comap
  have growR : Tendsto (fun x : WideParent κ A=>(x.h:ℝ)) (WideParent.large κ A) atTop :=
    tendsto_natCast_atTop_atTop.comp grow
  have Ftwo : 2≤factor N types := by unfold factor; nlinarith [sq_nonneg ((N:ℝ)+1),Nat.cast_nonneg (α:=ℝ) types]
  have Fone : 1≤factor N types := by linarith
  refine ⟨factor N types*K,p,one_le_mul_of_one_le_of_one_le Fone hK,hp,?_⟩
  filter_upwards [paid,(tendsto_log_atTop.comp growR).eventually_ge_atTop 1,
    grow.eventually (GapScale.eventual_polynomial 0 K p hp)] with x rx loghi enough
  let R := K*(log (x.h:ℝ))^p
  have logpos := Real.log_pos x.formats.1
  have small : K*(2*(x.h:ℝ))^p≤(2:ℝ)^x.h := by simpa [gap] using enough
  have rs : R≤(2:ℝ)^x.h := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow logpos.le (by linarith [Real.log_le_self (Nat.cast_nonneg x.h)] :
      log (x.h:ℝ)≤2*(x.h:ℝ)) hp) (zero_le_one.trans hK)).trans small
  have rOne : 1≤R := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow loghi hp)
  have rpos : 0≤R := zero_le_one.trans rOne
  have hh : 0<x.h := by have := x.property.1.1; change 2≤x.h at this; omega
  obtain ⟨control,work,selector⟩ := at_parent (c x) hh x.property.1.2.1 rOne rs rx.rows rx.cpu
    rx.selectors rx.flag rx.site rx.workspace rx.external rx.cuts rx.sockets
  change ((c x).total x.h:ℝ)≤factor N types*((2:ℝ)^x.h*x.w*R) at work
  constructor
  · intro j
    apply (control j).trans
    change (2:ℝ)^x.h*R≤_
    calc
      _ ≤ factor N types*((2:ℝ)^x.h*R) := le_mul_of_one_le_left (by positivity) Fone
      _ = _ := by dsimp [R]; ring
  · intro cost sel hc hs
    constructor
    · apply (show (cost:ℝ)≤(c x).total x.h by exact_mod_cast hc).trans
      exact work.trans_eq (by dsimp [R]; ring)
    · apply (add_le_add (le_refl ((x.h:ℝ)*2^x.h)) (show (sel:ℝ)≤(c x).selectors by exact_mod_cast hs)).trans
      apply selector.trans
      calc
        _ ≤ factor N types*((2:ℝ)^x.h*x.h*R) := mul_le_mul_of_nonneg_right Ftwo (by positivity)
        _ = _ := by dsimp [R]; ring

/-- Index the independently estimated hardware components without counting
the generated CPU and control-pin costs a second time. -/
inductive Part (types : ℕ)
  | rows (side : Bool)
  | flag | site | selectors | workspace | external
  | cut (i : Fin types)
  | socket (i : Fin types)
  deriving DecidableEq, Fintype

def Part.scale {types : ℕ} (h w : ℕ) : Part types → ℝ
  | .rows _ => (2:ℝ)^h
  | .selectors => (2:ℝ)^h*h
  | _ => (2:ℝ)^h*w

def Part.fee {types : ℕ} (c : Charges types) : Part types → ℝ
  | .rows b => c.rows b
  | .flag => c.flagWord
  | .site => c.site
  | .selectors => c.selectors
  | .workspace => c.workspace
  | .external => c.external
  | .cut i => c.cuts i
  | .socket i => c.sockets i

theorem of_component_bounds {κ A : ℝ} {types N : ℕ} (c : WideParent κ A → Charges types)
    (cpu : ∀ᶠ x in WideParent.large κ A, ∀b,(c x).cpu b≤
      20000000*2^(controlHeight x.h ((c x).rows b))*(x.h+1)*(N+1)^2)
    (bills : ∀i : Part types, ∃ K p : ℝ, 0≤K ∧ 0≤p ∧
      ∀ᶠ x in WideParent.large κ A,Part.fee (c x) i≤K*(Part.scale x.h x.w i*(log (x.h:ℝ))^p)) :
    ∃ C d : ℝ, 1≤C ∧ 0≤d ∧ ∀ᶠ x in WideParent.large κ A,
      (∀j,(WideHost.dualControlRows x.h ((c x).rows false) ((c x).rows true) j:ℝ)≤
        C*((2:ℝ)^x.h*(log (x.h:ℝ))^d)) ∧
      ∀ cost selectors : ℕ,cost≤(c x).total x.h → selectors≤(c x).selectors →
        (cost:ℝ)≤C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^d) ∧
        (x.h:ℝ)*2^x.h+selectors≤C*((2:ℝ)^x.h*x.h*(log (x.h:ℝ))^d) := by
  obtain ⟨C,p,hC,hp,all⟩ := common (fun i (x : WideParent κ A)=>Part.scale x.h x.w i)
    (fun i x=>Part.fee (c x) i)
    (fun i x=>by cases i <;> simp only [Part.scale] <;> positivity) bills
  apply eventually_bill (N:=N) c hC hp
  filter_upwards [all,cpu] with x bound native
  have eq (B : ℝ) : C*(B*(log (x.h:ℝ))^p)=B*(C*(log (x.h:ℝ))^p) := by ring
  simp only [eq] at bound
  exact ⟨fun b=>bound (.rows b),native,bound .selectors,bound .flag,bound .site,bound .workspace,
    bound .external,fun i=>bound (.cut i),fun i=>bound (.socket i)⟩

end Hierarchy.Tagged.WidePhysicalBill

end
end OAI
