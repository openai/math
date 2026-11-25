import OAI.Hierarchy.ProbeBroadcastPinValue
import OAI.Hierarchy.ProbeSiteHost

namespace OAI
/-! # Every native signed coefficient on untrusted public and private wires -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Diagonal MotifBinaryPacking MotifOuterTerms TraceCircuit Routing
open SiteHardware
open scoped Classical BigOperators

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k r : ℕ}
  [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

/-- The site has a permanent pin for each bit in its bounded aperture.
The physical field itself supplies canonical zeros above its actual width. -/
def Packet.rawSiteView (P : Packet F edge req) (h : Histogram (Fin P.terms) r) (i : Fin k)
    (c : Fin (2^(r*P.selectorBits))) (x : State (P.inputWidths r) i) (y : State (P.outputWidths h) i) :
    LocalPins P i r→Bool
  | .inl (j,b) => (blocks r P.selectorBits).symm ((word _).symm c) j b
  | .inr (.inl p,j) => (x p).val.testBit j.val
  | .inr (.inr p,j) => (y p).val.testBit j.val

private theorem test_or_zero {n : ℕ} (x : Fin (2^n)) (j : ℕ) :
    (if j<n then x.val.testBit j else false)=x.val.testBit j := by
  by_cases low : j<n
  · simp [low]
  · simp [low,Nat.testBit_eq_false_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt low)))]

omit [Nonempty (Fin k)] in
private theorem cast_state_val {a b : Widths k} (eqn : a=b) {i : Fin k} (x : State a i)
    (p : (portGraph k).Port i) :
    ((cast (congrArg (fun t=>State t i) eqn) x) p).val=(x p).val := by cases eqn;rfl

omit [Nonempty (Fin k)] in
theorem Packet.rawSiteView_word (P : Packet F edge req) (h : Histogram (Fin P.terms) r) (i : Fin k)
    (u : {w : Fin r→Fin P.terms // histogram w=h}) (x : State (P.inputWidths r) i)
    (y : State (P.outputWidths h) i) :
    P.rawSiteView h i (P.copyCode h u) x y =
      localView P i u.val x (cast (congrArg (fun g=>State g i)
        (word_installed (fun t=>optionWidths edge (P.count t)) h u).symm) y) := by
  funext pin
  let a:=P.width • demandWidths edge req
  let W:=fun t=>optionWidths edge (P.count t)
  let z:=cast (congrArg (fun g=>State g i) (word_installed W h u).symm) y
  cases pin with
  | inl b =>
    change (blocks r P.selectorBits).symm ((word _).symm (P.selectorWord r u.val)) b.1 b.2=_
    rw [P.selectorWord_bits,Equiv.symm_apply_apply]
    rfl
  | inr s =>
    rcases s with ⟨p,j⟩
    have full := test_or_zero (socketFields a W u.val i x z p) j.val
    rcases p with p|p
    · exact full.symm
    · exact (congrArg (fun n=>n.testBit j.val) (cast_state_val (word_installed W h u).symm y p)).symm.trans full.symm

theorem Packet.physical_signed_site (P : Packet F edge req) (rt : Fin k) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (x : State (P.inputWidths r) i) (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i) :
    let q:=G.chordWidths (fun _=>r*P.selectorBits)
    let yz:=splitPortState (P.outputWidths h) q i z
    let c:=BroadcastPins.candidate q i p yz.2 (r*P.selectorBits)
    P.broadcastMatrix rt r G h i x z=
      TypedWiring.value (BroadcastPins.network F q i p fit) (BroadcastPins.read q i yz.2) *
      ((NativeHistogram.network F (NativeHistogram.alphabet_pos P) P.selectorBits h).eval ((word _).symm c) *
       TypedWiring.value (typedSite P i r) (P.rawSiteView h i c x yz.1)) := by
  intro q yz c
  apply P.physical_entry rt G h i p fit x z
  intro u decoded
  have chosen : c=P.copyCode h u:=decoded
  change TypedWiring.value (typedSite P i r) (P.rawSiteView h i c x yz.1)=P.siteEntry h u i x yz.1
  rw [chosen,P.rawSiteView_word,typedSite_eval]
  let W:=fun t=>optionWidths edge (P.count t)
  exact (P.eval_site i u.val x (cast (congrArg (fun g=>State g i) (word_installed W h u).symm) yz.1)).symm

end Hierarchy.Probe
end

end OAI
