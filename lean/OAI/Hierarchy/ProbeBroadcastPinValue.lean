import OAI.Hierarchy.ProbeBroadcastPinEquality

namespace OAI
/-! # The signed local matrix on every possible physical selector input -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Diagonal MotifBinaryPacking MotifOuterTerms TraceCircuit Routing
open scoped Classical BigOperators

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k r : ℕ}
    [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}

def Packet.checkCode (P : Packet F edge req) (h : Histogram (Fin P.terms) r)
    (v : Fin (2^(r*P.selectorBits))) :=
  (NativeHistogram.network F (NativeHistogram.alphabet_pos P) P.selectorBits h).eval
    ((word _).symm v)

/-- The actual native histogram network recognizes the embedded selector
image even on invalid padded alphabets and over fields of positive characteristic. -/
theorem Packet.checkCode_value (P : Packet F edge req) (h : Histogram (Fin P.terms) r)
    (c : Fin (2^(r*P.selectorBits))) :
    P.checkCode h c=if ∃u,P.copyCode h u=c then 1 else 0 := by
  by_cases found : ∃u,P.copyCode h u=c
  · obtain ⟨u,rfl⟩:=found
    have witness : ∃v,P.copyCode h v=P.copyCode h u:=⟨u,rfl⟩
    rw [ite_eq_left witness]
    simpa [checkCode,copyCode,u.property] using NativeHistogram.broadcast_eval P h u.val
  · rw [ite_eq_right found]
    let bits:=(blocks r P.selectorBits).symm ((word _).symm c)
    have coding : (word _).symm c=blocks r P.selectorBits bits := (Equiv.apply_symm_apply _ _).symm
    unfold checkCode
    rw [coding,NativeHistogram.eval]
    apply ite_eq_right
    rintro ⟨valid,hist⟩
    let w:=(fun i=>NativeHistogram.letter (NativeHistogram.alphabet_pos P) (bits i))
    let u : {s : Fin r→Fin P.terms // histogram s=h}:=⟨w,hist.symm⟩
    apply found
    refine ⟨u,(word _).symm.injective ?_⟩
    change (word _).symm (P.selectorWord r w)=_
    rw [P.selectorWord_bits,coding]
    congr 1
    funext i
    apply (word _).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simp [w,NativeHistogram.letter,NativeHistogram.valid,valid i,Packet.encode]

/-- One arbitrary socket word with bad local copies or wrong histogram has
zero coefficient. On a successful read the ordinary signed matrix uses its
single stable-compactor site LUT. The arbitrary value of inactive LUT pins
cancels in the zero case. -/
theorem Packet.physical_entry (P : Packet F edge req) (rt : Fin k) (G : PortGraph (Fin k) B)
    (h : Histogram (Fin P.terms) r) (i : Fin k) (p : (portGraph k).Port i)
    (fit : r*P.selectorBits≤G.chordWidths (fun _=>r*P.selectorBits) p.val.1)
    (x : State (P.inputWidths r) i)
    (z : State (P.outputWidths h+G.chordWidths (fun _=>r*P.selectorBits)) i)
    (signed : F)
    (value : ∀u : {w : Fin r→Fin P.terms // histogram w=h},
      BroadcastPins.candidate _ i p (splitPortState _ _ i z).2 (r*P.selectorBits)=P.copyCode h u →
      signed=P.siteEntry h u i x (splitPortState _ _ i z).1) :
    let q:=G.chordWidths (fun _=>r*P.selectorBits)
    let yz:=splitPortState (P.outputWidths h) q i z
    let c:=BroadcastPins.candidate q i p yz.2 (r*P.selectorBits)
    P.broadcastMatrix rt r G h i x z=
      TypedWiring.value (BroadcastPins.network F q i p fit) (BroadcastPins.read q i yz.2) *
        (P.checkCode h c*signed) := by
  intro q yz c
  rw [BroadcastPins.eval,P.checkCode_value]
  have recover (u : {w : Fin r→Fin P.terms // histogram w=h})
      (consistent : yz.2=colourState q i (P.copyCode h u)) : c=P.copyCode h u := by
    apply Fin.ext
    change (yz.2 p).val%2^(r*P.selectorBits)=(P.copyCode h u).val
    rw [consistent]
    have wide : r*P.selectorBits≤q p.val.1:=fit
    simp only [colourState,extendColour,dite_eq_left wide]
    exact Nat.mod_eq_of_lt (P.copyCode h u).isLt
  by_cases code : ∃u,P.copyCode h u=c
  · obtain ⟨u,encoded⟩:=code
    have existsCode : ∃v,P.copyCode h v=c:=⟨u,encoded⟩
    rw [ite_eq_left existsCode,one_mul]
    by_cases ok : yz.2=colourState q i c
    · rw [ite_eq_left ok,one_mul,value u encoded.symm]
      have honest : yz.2=colourState q i (P.copyCode h u) := by rw [encoded];exact ok
      have uniqueWord:=(colourState_injective q i p fit).comp (P.copyCode h).injective
      have check : P.checkEntry h u=1 := by simpa [Packet.checkEntry,u.property] using NativeHistogram.broadcast_eval P h u.val
      unfold broadcastMatrix
      change (∑v, (if yz.2=colourState q i (P.copyCode h v) then (1:F) else 0)*
          ((if i=rt then P.checkEntry h v else 1)*P.siteEntry h v i x yz.1))=_
      rw [Finset.sum_eq_single u]
      · simp [honest,check]
        rfl
      · intro v _ diff
        have nope : yz.2≠colourState q i (P.copyCode h v) := fun eq=>diff (uniqueWord (eq.symm.trans honest))
        simp [nope]
      · simp
    · rw [ite_eq_right ok,zero_mul]
      exact P.broadcastMatrix_reject rt G h i x z (fun u hu=>ok (by rw [recover u hu];exact hu))
  · rw [ite_eq_right code,zero_mul,mul_zero]
    exact P.broadcastMatrix_reject rt G h i x z (fun u hu=>code ⟨u,(recover u hu).symm⟩)

end Hierarchy.Probe
end

end OAI
