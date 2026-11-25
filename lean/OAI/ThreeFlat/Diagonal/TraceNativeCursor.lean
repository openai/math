import OAI.ThreeFlat.Diagonal.TraceTrueCursor
import OAI.ThreeFlat.Diagonal.TraceTrueEndpoint
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Contracting the actual prepared first/relay leaf networks recovers the native H trace -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner TraceSuffix RAM.PhysicalPrelude
open scoped BigOperators Classical
variable {F : Type*} [Fintype F] [Field F] {w p r k S base f q low : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
    (hF : Fintype.card F≤2^w) (st : Word w)
noncomputable def nativeCursorFactor {copies T : ℕ} (span : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool)
    (hk : 2≤q+1) (fields : Fields (q+1) copies (Fin (1+(((q+1)+low)+((q+1)+low))))
      (PayloadAddress low (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) (i : Fin (q+1)) (L : Lane (q+1)) : F :=
  let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
  let send := outgoingPorts fields i L
  let recv := incomingPorts hk fields i L
  let port := RelayNetwork.pins I.tag send recv
  if i=0 then
    (pairLeaf hF t.width t.labels base st t.header t.time r k t.grid L copies T span pub).eval
      (Fin.append (localPairPins span pin low (finFunctionFinEquiv L).val) port)
  else
    (RelayNetwork.network (r:=copies) I.tag (layout hF t.width t.labels base st t.header t.time r k t.grid).mask i).eval port

theorem nativeCursorFactor_eq {copies T : ℕ} (span : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool)
    (hk : 2≤q+1) (fields : Fields (q+1) copies (Fin (1+(((q+1)+low)+((q+1)+low))))
      (PayloadAddress low (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) (i : Fin (q+1)) (L : Lane (q+1)) :
    nativeCursorFactor M t hF st span pub pin hk fields i L =
      vertexFactor (layout hF t.width t.labels base st t.header t.time r k t.grid).mask ((layout hF t.width t.labels base st t.header t.time r k t.grid).localTensor (fullHeader span pin pub)) fields i L := by
  rw [←portTensor_eq hk]
  by_cases first : i=0
  · subst i
    simpa only [nativeCursorFactor,eq_self,ite_true] using
      pairLeaf_eval hF t.width t.labels base st t.header t.time r k t.grid L copies T span pub pin
        (outgoingPorts fields 0 L) (incomingPorts hk fields 0 L)
  · unfold nativeCursorFactor
    rw [ite_eq_right first,RelayNetwork.eval]
    by_cases check : PortChecks (layout hF t.width t.labels base st t.header t.time r k t.grid).mask i (outgoingPorts fields i L) (incomingPorts hk fields i L) <;>
      simp only [portTensor,check,first,ite_false,ite_true]

/-- The pin-vector expression on the right is exactly the native endpoint used by
`FoldTrace.native_matrix_trace`, including its padded H instruction text and raw input tape. -/
theorem native_cursor_trace {copies : ℕ} (hk : 2≤q+1) (I : Image F w) (D : Fin I.advice→Bool)
    (par : Fin I.parameters→Bool) (span : 2*I.endpointBits≤S) (sep : 2*I.endpointBits≤base)
    (x y : Fin I.endpointBits→Bool) :
    (∑ fields : Fields (q+1) copies (Fin (1+(((q+1)+low)+((q+1)+low))))
      (PayloadAddress low (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells), ∏ i, ∏ L,
      nativeCursorFactor M t hF st span (publicAt I base (NativeTrace.executable M) D par) (endpointPin x y) hk fields i L) =
    (NativeTrace.network M t hF st).eval
      (advicePins base (NativeTrace.executable M) (I.tapeBit D x y par)) := by
  simp_rw [nativeCursorFactor_eq]
  exact (trueNetwork_cursor hF t.width t.labels base st t.header t.time r k t.grid span _ _).trans
    (trueEndpoint_eval hF t.width t.labels base st t.header t.time r k I D par (NativeTrace.executable M) span sep x y)


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
