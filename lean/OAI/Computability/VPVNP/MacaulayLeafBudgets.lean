import OAI.Computability.VPVNP.MacaulayReaderScans
import OAI.Computability.VPVNP.AffinePinResources
import OAI.Computability.VPVNP.MacaulayEntryPhase
import OAI.Computability.VPVNP.MacaulayPinArm

/-! # Shared time and space budgets for the three Macaulay entry arms

The live bank includes the signed counter, mask and value tables, two
ordinal words, and a full residual exponent buffer. Exhaustive counting and
ordinal scans contribute to the clock. Their exponent does not contribute
to the stack-height bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ReaderPlan

open PolynomiallyBounded RankQuery.Stack

/-- Includes the packed extension-field result and the residual buffer. -/
def live (P : ReaderPlan) (e v w signedSpace : ℕ) :=
  w + P.arity + P.arity*w + e*v + signedSpace + AffinePin.Query.space P.arity e w v

/-- Common tick bound for signed equation evaluation, affine pin lookup and copying an encoded
scalar constant. -/
def scalarTime (P : ReaderPlan) (e v w signedExp : ℕ) :=
  max (2^signedExp) (max (MacaulayRead.Arms.Pin.cost P.arity e w v) (5*(e*v)+2))

/-- Tick bound for both ordinal scans and the post-scan scalar computation and buffer cleanup
of a matrix-entry arm. -/
def armTime (P : ReaderPlan) (e v w signedSpace signedExp : ℕ) :=
  let b := P.live e v w signedSpace
  P.scanTime w b + MacaulayRead.Arms.postTicks b P.arity w (P.scalarTime e v w signedExp)

/-- Stack bound for the selected entry arm, including the ordinal scans, temporary exponent
buffer and decoder allowance. -/
def armSpace (P : ReaderPlan) (e v w signedSpace : ℕ) :=
  let b := P.live e v w signedSpace
  P.scanSpace w b + MacaulayRead.Arms.transient b P.arity w + MacaulayRowDispatch.ticks w

/-- Time bound for decoding a row, routing it to the appropriate entry arm and returning the
scalar. -/
def readTime (P : ReaderPlan) (e v w signedSpace signedExp : ℕ) :=
  MacaulayRowDispatch.ticks w + (4 + P.armTime e v w signedSpace signedExp)

theorem pin_cost_mono (t w : ℕ) {e e' v v' : ℕ} (he : e ≤ e') (hv : v ≤ v') :
    AffinePin.Query.cost t e w v ≤ AffinePin.Query.cost t e' w v' := by
  unfold AffinePin.Query.cost AffinePin.Stage.cost AffinePin.Reader.cost EvaluatorDigitLookup.lookupTicks
    AffinePin.Output.cost SliceArithmetic.AddCall.callCap
  gcongr

theorem pin_space_mono (t w : ℕ) {e e' v v' : ℕ} (he : e ≤ e') (hv : v ≤ v') :
    AffinePin.Query.space t e w v ≤ AffinePin.Query.space t e' w v' := by
  apply Nat.add_le_add _ (pin_cost_mono t w he hv)
  unfold AffinePin.Query.storage
  gcongr

/-- All local clocks and stack heights are charged using their respective
budgets. The signed-call time is the only exponential term besides the two
ordinal scans. -/
theorem leaf_bounds (P : ReaderPlan) (w signedSpace signedExp : ℕ) {e v E V : ℕ} (he : e ≤ E) (hv : v ≤ V)
    (d : PairCall.Inputs) (ht : d.arity = P.arity) (hL : d.degree false ≤ P.source) (hD : d.degree true ≤ P.column) :
    let live := P.live E V w signedSpace
    let cap := P.armSpace E V w signedSpace
    let clock := P.armTime E V w signedSpace signedExp
    (w ≤ live ∧ P.arity ≤ live ∧ P.arity*w ≤ live ∧ e*v ≤ live ∧ signedSpace ≤ live ∧
      AffinePin.Query.space P.arity e w v ≤ live) ∧
    (PairCall.equationSpace w live d ≤ cap ∧ PairCall.poweredSpace w live ≤ cap ∧
      live + MacaulayRowDispatch.ticks w ≤ cap ∧ MacaulayRead.Arms.transient live P.arity w ≤ cap ∧
      max live (P.arity*w) + (5*w+2) ≤ cap) ∧
    ∀ time, time ≤ 2^signedExp →
      P.scanTime w live + MacaulayRead.Arms.postTicks live P.arity w
        (max time (max (MacaulayRead.Arms.Pin.cost P.arity e w v) (5*(e*v)+2))) ≤ clock := by
  intro b cap clock
  obtain ⟨_,_,hs,hp⟩ := P.scan_bounds w b d ht hL hD
  have h₁ := Nat.mul_le_mul he hv
  have h₂ := pin_cost_mono P.arity w he hv
  have h₃ := pin_space_mono P.arity w he hv
  have hb : w ≤ b := by dsimp [b,live]; omega
  have htbuf : P.arity*w ≤ b := by dsimp [b,live]; omega
  constructor
  · dsimp [b,live]; omega
  constructor
  · have eq : cap = P.scanSpace w b + MacaulayRead.Arms.transient b P.arity w + MacaulayRowDispatch.ticks w := rfl
    rw [eq]
    dsimp only [MacaulayRead.Arms.transient]
    omega
  · intro time htime
    apply Nat.add_le_add_left
    unfold MacaulayRead.Arms.postTicks scalarTime MacaulayRead.Arms.Pin.cost
    gcongr

private theorem clogMax {f g : ℕ → ℕ} (hf : PolynomiallyBounded (fun n => Nat.clog 2 (f n)))
    (hg : PolynomiallyBounded (fun n => Nat.clog 2 (g n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (max (f n) (g n))) :=
  (clog_add hf hg).of_le fun _ => Nat.clog_mono_right _ (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

theorem leaf_resources (P : ℕ → ReaderPlan) {w e v signedSpace signedExp : ℕ → ℕ}
    (hw : PolynomiallyBounded w) (he : PolynomiallyBounded e) (hv : PolynomiallyBounded v)
    (hs : PolynomiallyBounded signedSpace) (hx : PolynomiallyBounded signedExp)
    (ht : PolynomiallyBounded (fun n => (P n).arity)) (hd : PolynomiallyBounded (fun n => Nat.clog 2 (P n).degree))
    (hn : PolynomiallyBounded (fun n => Nat.clog 2 (P n).points)) (hq : PolynomiallyBounded (fun n => Nat.clog 2 (P n).order)) :
    PolynomiallyBounded (fun n => (P n).live (e n) (v n) (w n) (signedSpace n)) ∧
    PolynomiallyBounded (fun n => (P n).armSpace (e n) (v n) (w n) (signedSpace n)) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 ((P n).readTime (e n) (v n) (w n) (signedSpace n) (signedExp n))) := by
  obtain ⟨hpin,hpinSpace,_⟩ := AffinePin.Query.resources ht he hw hv
  have hLive : PolynomiallyBounded (fun n => (P n).live (e n) (v n) (w n) (signedSpace n)) :=
    ((((hw.add ht).add (ht.mul hw)).add (he.mul hv)).add hs).add hpinSpace
  obtain ⟨hcap,hclock,hrouter⟩ := resources P hw hLive ht hd hn hq
  have hpincost := ((((PolynomiallyBounded.const 5).mul hw).add (.const 2)).add hpin)
  have hscalar := (((PolynomiallyBounded.const 5).mul (he.mul hv)).add (.const 2))
  have hleaves := clogMax (clog_pow ((PolynomiallyBounded.const 2).clog) hx) (clogMax hpincost.clog hscalar.clog)
  have hbuf := (ht.mul hw).add (.const 1)
  have hticks := clog_add (clog_add ((PolynomiallyBounded.const 2).clog) (clogMax
    ((((PolynomiallyBounded.const 5).mul hLive).add (.const 2)).clog) hleaves)) ((hbuf.add (hw.add (.const 1))).clog)
  have htrans := ((hLive.add (ht.mul hw)).add hw).add
    (((((PolynomiallyBounded.const 5).mul hLive).add (ht.mul hw)).add hw).add (.const 4))
  exact ⟨hLive,(hcap.add htrans).add hrouter,clog_add hrouter.clog
    (clog_add ((PolynomiallyBounded.const 4).clog) (clog_add hclock hticks))⟩

end RadicalCertificate.MonomialIndex.ReaderPlan

end VPVNP
end Computability
end OAI
