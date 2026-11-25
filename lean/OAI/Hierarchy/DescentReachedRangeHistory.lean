import OAI.Hierarchy.DescentRangeRegisterType
import OAI.Hierarchy.DescentRetainedResetRangeOrigin
import OAI.Hierarchy.DescentRetainedRangeCopies

namespace OAI
/-! # Lifetimes of the three physical rotor range words along a selected chronology -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentTerminalSliceRuns DescentSIMDLookup
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentEpochTagKeys DescentBundleHistory
open DescentOrderedReset DescentResetAttachments DescentRouterBank DescentRotor DescentResetGates Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

variable {p R : ℕ} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k wire hist : ℕ}
variable {W₀ : MarkedWorld F d P bits} {a₀ z₀ D₀ age z₁ D₁ : ℕ}
    {start : Reached W₀ G q ε S k a₀ z₀ D₀ wire hist} {now : Reached W G q ε S k age z₁ D₁ wire hist}
variable (hp : 0<p) (a : Archive W₀)
variable (pages : ∀{V : MarkedWorld F d P bits} {i g D : ℕ} {tick : Reached V G q ε S k i g D wire hist},
    (prev : Path start tick)→(whole : prev.whole p)→Register (prev.archive p hp a whole).bit)
abbrev RangePages (root_ : Reached W₀ G q ε S k a₀ z₀ D₀ wire hist) (hp : 0<p) (a : Archive W₀) :=
  ∀{V : MarkedWorld F d P bits} {i g D : ℕ} {tick : Reached V G q ε S k i g D wire hist},
    (prev : Path root_ tick)→(whole : prev.whole p)→Register (prev.archive p hp a whole).bit

variable (one : 1≤R) (pins : ∀v,p∣bits v) (sh : WorldShape p R a.bit)

include hp a pages one pins sh in
/-- The native date interfaces compare the literal carried word with the previous physical
register. The fresh interface is solely the local newly-issued lane descriptor on its birth date.
No range comparison is needed on the seed, an ordinary birth or the relay bank. -/
def Copies (path : Path start now) (whole : path.whole p) (aligned : path.aligned p R) : Prop := by
  induction path with
  | here=>exact True
  | @ordinary _ i z D z' D' cap prev u he T c norm target ticket ih=>
    let old:=prev.archive p hp a whole
    let prior:=pages prev whole
    let newPage:=pages (prev.ordinary ticket) whole
    exact ih whole aligned.1 ∧ ∀x y,roots ticket old x=Sum.inl y →
      ∀j,j<(repeatFields ((archiveShape hp one pins a sh prev whole aligned.1).nodeFields y).flatten).length → ∀f,newPage.word x j f=prior.word y j f
  | @reset _ i z D _ _ _ _ _ _ _ cap prev ctl b ih=>
    let old:=prev.archive p hp a whole.1
    let prior:=pages prev whole.1
    let newPage:=pages (prev.reset b) whole
    let origin:=resetOrigin b hp whole.2 old
    let key:=DescentOrderedReset.grains _ b.count b.order
    let fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole.2).symm
    let lane:=b.reset.laneProgram key (b.reset.unit/p) p hp fit
    let device:=fun v=>ofProgram (fun e=>boundaryWidth b.reset.bank v e/p)
      (b.reset.laneWidth_eq (b.reset.unit/p) p fit v) hp (lane v)
    exact ih whole.1 aligned.1 ∧ (∀x y,origin x=Sum.inl y → ∀j,j<(repeatFields ((archiveShape hp one pins a sh prev whole.1 aligned.1).nodeFields y).flatten).length →
      ∀f,newPage.word x j f=prior.word y j f) ∧
      (∀x v,origin x=Sum.inr (Sum.inr v) → ∀j,j<(repeatFields ((device v.1).sliceFields v.2).flatten).length →
        ∀f,newPage.word x j f=atSlot (device v.1) v.2 j f)

variable {s : ℕ} (op : RotorSpec) (menu : Runnable F op) (code : Encoding (Label G s z₀ op) (dictionary G op menu p) a.bit)
theorem reached_ranges (path : Path start now) (whole : path.whole p) (aligned : path.aligned p R)
    (fixed : path.OnlyRotor op) (source : ∀x,classify G p s (code.atNode x)≠.rotor)
    (native : Copies hp a pages one pins sh path whole aligned) :
    let encoded:=encodePath op menu path hp whole fixed a code
    let shape:=archiveShape hp one pins a sh path whole aligned
    ∀x : NodeOrder.All (path.archive p hp a whole).bit,classify G p s (encoded.atNode x)=.rotor →
      ∀j,j<(repeatFields (shape.nodeFields x).flatten).length →
        ∀f,(pages path whole).word x j f=atSlot (shape.sites x.1) x.2 j f := by
  induction path with
  | here=>intro encoded shape x rotor;exact (source x rotor).elim
  | @ordinary _ i z D z' D' cap prev u he T c norm target ticket ih=>
    intro encoded shape x rotor j active f
    let old:=prev.archive p hp a whole
    let oldCode:=encodePath op menu prev hp whole fixed a code
    let oldShape:=archiveShape hp one pins a sh prev whole aligned.1
    have limit : T.z≤z₀:=ticket.quantum.trans cap.grain ▸ grain_le prev
    have token:=ordinary_at op menu ticket old oldCode limit x
    have fieldEq:=ordinary_fields ticket old oldShape hp one pins aligned.2 x
    change classify G p s _=.rotor at rotor
    change encoded.atNode x=_ at token
    change shape.nodeFields x=_ at fieldEq
    rw [token] at rotor
    cases which : roots ticket old x with
    | inl y=>
      simp only [which,Sum.elim_inl] at fieldEq rotor
      have live : j<(repeatFields (oldShape.nodeFields y).flatten).length:=fieldEq ▸ active
      exact ((native.2 x y which j live f).trans ((ih whole aligned.1 fixed native.1) y rotor j live f)).trans
        (of_fields _ _ _ _ fieldEq j f).symm
    | inr birth=>
      rw [which] at rotor
      rcases birth with ⟨_,_⟩
      cases rotor
  | @reset _ i z D n h C f g cut tail cap prev ctl b ih=>
    intro encoded shape x rotor j active f
    let old:=prev.archive p hp a whole.1
    let oldCode:=encodePath op menu prev hp whole.1 fixed.1 a code
    let oldShape:=archiveShape hp one pins a sh prev whole.1 aligned.1
    have token:=reset_at op menu b hp whole.2 fixed.2 old oldCode x
    have fieldEq:=reset_range_origin b hp whole.2 old oldShape one aligned.2.1 aligned.2.2.2 x
    change encoded.atNode x=_ at token
    change shape.nodeFields x=_ at fieldEq
    rw [token] at rotor
    cases which : resetOrigin b hp whole.2 old x with
    | inl y=>
      simp only [which,Sum.elim_inl] at fieldEq rotor
      have live : j<(repeatFields (oldShape.nodeFields y).flatten).length:=fieldEq ▸ active
      exact ((native.2.1 x y which j live f).trans ((ih whole.1 aligned.1 fixed.1 native.1) y rotor j live f)).trans
        (of_fields _ _ _ _ fieldEq j f).symm
    | inr right=>
      cases right with
      | inl relay=>rw [which] at rotor;cases rotor
      | inr bank=>
        simp only [which,Sum.elim_inr] at fieldEq
        have live:=active
        rw [fieldEq] at live
        exact (native.2.2 x bank which j live f).trans (of_fields _ _ _ _ fieldEq j f).symm

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
