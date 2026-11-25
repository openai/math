import OAI.ThreeFlat.Diagonal.TraceNativeCursor
import OAI.ThreeFlat.Diagonal.HistoryAssembly

namespace OAI
/-! # Actual initial history atoms in the order external bits, outgoing words, incoming words -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor LaneCursor.RowLayout TraceSourceOwner TraceSuffix
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] {w p r k S base f q low : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
    (hF : Fintype.card F≤2^w) (st : Word w)
structure SiteLeaf (F Pins Half : Type*) where
  width : ℕ
  table : BitNetwork F width
  read : Pins → Half → Half → Fin width → Bool

noncomputable def cursorAtom (copies T : ℕ) (span : 2*T≤S) (pub : ℕ→Bool)
    (i : Fin (q+1)) (L : Lane (q+1)) : SiteLeaf F (Fin (2*T)→Bool) (BucketIndex.PortData copies (1+(((q+1)+low)+((q+1)+low))) low
      (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells) :=
  let I := bitIndex hF t.width t.labels base st t.header t.time r k t.grid L
  if i=0 then {
    width := retained T low (finFunctionFinEquiv L).val+BucketIndex.ports copies I.t
    table := pairLeaf hF t.width t.labels base st t.header t.time r k t.grid L copies T span pub
    read := fun pin send recv => Fin.append (localPairPins span pin low (finFunctionFinEquiv L).val)
      (RelayNetwork.pins I.tag send recv) }
  else {
    width := BucketIndex.ports copies I.t
    table := RelayNetwork.network I.tag (layout hF t.width t.labels base st t.header t.time r k t.grid).mask i
    read := fun _ send recv => RelayNetwork.pins I.tag send recv }

theorem cursorAtom_eval (copies T : ℕ) (span : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool)
    (hk : 2≤q+1) (fields : Fields (q+1) copies (Fin (1+(((q+1)+low)+((q+1)+low)))) (PayloadAddress low (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells))
    (i : Fin (q+1)) (L : Lane (q+1)) :
    let a := cursorAtom M t hF st copies T span pub i L
    a.table.eval (a.read pin (outgoingPorts fields i L) (incomingPorts hk fields i L)) =
      nativeCursorFactor M t hF st span pub pin hk fields i L := by
  let evaluate (a : SiteLeaf F (Fin (2*T) → Bool)
      (BucketIndex.PortData copies (1+(((q+1)+low)+((q+1)+low))) low
        (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells)) :=
    a.table.eval (a.read pin (outgoingPorts fields i L) (incomingPorts hk fields i L))
  change evaluate (cursorAtom M t hF st copies T span pub i L) = _
  unfold cursorAtom nativeCursorFactor
  by_cases first : i=0
  · simp only [ite_eq_left first]
    rfl
  · simp only [ite_eq_right first]
    rfl

theorem cursorAtom_width (copies T : ℕ) (span : 2*T≤S) (pub : ℕ→Bool) (i : Fin (q+1)) (L : Lane (q+1)) :
    (cursorAtom M t hF st copies T span pub i L).width =
      (if i=0 then retained T low (finFunctionFinEquiv L).val else 0)+
        BucketIndex.ports copies (bitIndex hF t.width t.labels base st t.header t.time r k t.grid L).t := by
  by_cases first : i=0 <;> simp only [cursorAtom,first,ite_true,ite_false,Nat.zero_add]


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
