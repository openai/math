import OAI.Hierarchy.TaggedWideMountedBill
import OAI.Hierarchy.TaggedWideControl
import OAI.Hierarchy.TaggedGapScale
import OAI.Hierarchy.TaggedWideReadoutParts

namespace OAI
/-! # The two real RAM text sizes pay for the control circuits on their true tape lengths -/
noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open ThreeFlat.Diagonal.TraceRows
open ProbeStage.Native
open Real Filter
open scoped Classical BigOperators Topology

/-- A program's native dimensions include the initial array, fuel and the actual
observed addresses. Its padded comparison height is determined from their sum. -/
structure Mounted (h N : ℕ) where
  W : ℕ
  initial : ℕ
  fuel : ℕ
  outputs : ℕ
  proc : Procedure W
  ret : Word W
  start : Word W
  addr : Fin outputs→Word W
  word : 3≤W+1
  labels : proc.labels+3≤2^(W+1)
  fits : initial≤2^W
  clock : fuel+outputs≤2^(W+1)
  textBound : text proc≤N
  cheap : CheapCode proc
  width : W+1≤4*(h+1)
namespace Mounted
variable {h N : ℕ} (a : Mounted h N)

def rows := a.initial+(a.fuel+a.outputs)

def gate : Gate := Gate.ofProcedure (S:=a.initial) (f:=a.fuel) a.proc a.ret a.start a.addr
  (controlHeight h a.rows) a.word a.labels a.fits a.clock

theorem capacity : a.rows≤2^(controlHeight h a.rows) :=
  (le_max_right (2^h) a.rows).trans (Nat.le_pow_clog (by decide) _)

theorem ran (header : ℕ→Word a.W) (out : Memory a.W) (budget : ℕ)
    (time : budget+2<a.fuel) (run : a.proc.Exec (initialMemory a.initial header) out budget) :
    a.gate.Ran header out :=
  Gate.ofProcedure_run a.proc a.ret a.start a.addr _ a.word a.labels a.fits a.clock header out budget time run

theorem cpu {F : Type*} [Field F] (fit : a.rows≤2^(2*h)) :
    (a.gate.hardware (F:=F)).cells+(a.gate.hardware (F:=F)).internal+Fintype.card a.gate.Pin≤
    20000000*2^(controlHeight h a.rows)*(h+1)*(N+1)^2 := by
  have hm : controlHeight h a.rows≤2*h := Nat.clog_le_of_le_pow (max_le
    (Nat.pow_le_pow_right (by decide) (show h≤2*h by omega)) fit)
  exact Gate.ofProcedure_bill a.proc a.ret a.start a.addr _ N a.word a.labels a.fits a.clock
    a.textBound a.cheap a.width hm a.capacity

/-- Any honest near-linear row charge fits below the square of the parent
row count, uniformly over every allowed parent width. -/
theorem eventually_rows {κ A : ℝ} (K d : ℝ) (hK : 0≤K) (hd : 0≤d) :
    ∀ᶠ x in WideParent.large κ A,∀ v : ℕ,
    (v:ℝ)≤K*((2:ℝ)^x.h*(log (x.h:ℝ))^d) → v≤2^(2*x.h) := by
  have grow : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [grow.eventually (GapScale.eventual_polynomial 0 K d hd)] with x hx v small
  have enough : K*(2*(x.h:ℝ))^d≤(2:ℝ)^x.h := by simpa [gap] using hx
  have loghi : log (x.h:ℝ)≤2*(x.h:ℝ) := by linarith [log_le_self (Nat.cast_nonneg x.h)]
  have one := (mul_le_mul_of_nonneg_left (rpow_le_rpow (log_pos x.formats.1).le loghi hd) hK).trans enough
  have two := mul_le_mul_of_nonneg_left one (by positivity : 0≤(2:ℝ)^x.h)
  have bound : (v:ℝ)≤(2:ℝ)^(2*x.h) := by rw [two_mul,pow_add]; linarith only [small,two]
  exact_mod_cast bound

variable {F : Type*} [Field F] {k w M n : ℕ} (b : Mounted h N)
    (p : Parts F k h w M n) (first : p.first=a.gate) (paid : p.paid=b.gate)

include first paid in
theorem sizes :
    p.first.m=controlHeight h (p.first.S+(p.first.f+p.first.u)) ∧
    p.paid.m=controlHeight h (p.paid.S+(p.paid.f+p.paid.u)) ∧
    p.paid.S+(p.paid.f+p.paid.u)≤2^p.paid.m := by
  rw [first,paid]
  exact ⟨rfl,rfl,b.capacity⟩

include first in
/-- The observation flag consumes one native word on the prefix CPU. -/
theorem flag_bill {κ A : ℝ} (x : WideParent κ A) (atHeight : h=x.h) (atWidth : w=x.w) :
    WidePhysicalBill.Part.fee p.charges .flag≤8*(WidePhysicalBill.Part.scale (types:=n) h w .flag*(log (h:ℝ))^(0:ℝ)) := by
  have hw : h≤w := by
    rw [atHeight,atWidth]
    exact x.property.1.2.1
  have hh : 1≤h:=by have hh:=x.property.1.1; change 2≤x.h at hh;omega
  have one : 1≤2^h:=Nat.one_le_two_pow
  have pow : w≤2^h*w:=by simpa using Nat.mul_le_mul_right w one
  have bits := a.width
  change ((p.first.W+1:ℕ):ℝ)≤_
  rw [first]
  simp only [WidePhysicalBill.Part.scale, Real.rpow_zero,mul_one]
  have bound : a.W+1≤8*(2^h*w):=by omega
  change ((a.W+1:ℕ):ℝ) ≤ 8*((2:ℝ)^h*w)
  exact_mod_cast bound

include first paid in
theorem charges_cpu (fit₀ : a.rows≤2^(2*h)) (fit₁ : b.rows≤2^(2*h)) (side : Bool) :
    p.charges.cpu side≤20000000*2^(controlHeight h (p.charges.rows side))*(h+1)*(N+1)^2 := by
  cases side
  · change (p.first.hardware (F:=F)).cells+(p.first.hardware (F:=F)).internal+Fintype.card p.first.Pin≤
      20000000*2^(controlHeight h (p.first.S+(p.first.f+p.first.u)))*(h+1)*(N+1)^2
    rw [first]
    exact a.cpu fit₀
  · change (p.paid.hardware (F:=F)).cells+(p.paid.hardware (F:=F)).internal+Fintype.card p.paid.Pin≤
      20000000*2^(controlHeight h (p.paid.S+(p.paid.f+p.paid.u)))*(h+1)*(N+1)^2
    rw [paid]
    exact b.cpu fit₁

end Mounted
end Hierarchy.Tagged.WideControlJoin

end
end OAI
