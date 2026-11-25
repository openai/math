import OAI.Hierarchy.DescentResetStemReindexed

namespace OAI
/-! # The shared broadcast tables remain resident after the complete stem issuer -/
namespace Hierarchy.DescentResetStemHeaders
open DescentSIMDLookup DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M b w : ℕ}

theorem TablesOK.below {base : ℕ} {m m' : Memory w} (seen : TablesOK H G M b base m)
    (same : ∀x,x<outputBase H G M b base→m' x=m x) : TablesOK H G M b base m':=by
  let n:=H*chunks G M
  have shape : outputBase H G M b base=base+2^b+span n+span n:=by
    simp only [outputBase,romSize,n,two_mul,Nat.add_assoc]
  refine ⟨fun v=>?_,fun p=>?_,fun p=>?_⟩
  · have hv:=v.isLt
    rw [same];exact seen.word v
    change base+v.val<_;rw [shape];omega
  · have hv:=(row H G M p).isLt.trans_le (span_ge n)
    rw [same];exact seen.actor p
    change base+2^b+(row H G M p).val<_;rw [shape];omega
  · have hv:=(row H G M p).isLt.trans_le (span_ge n)
    rw [same];exact seen.mask p
    change base+2^b+span n+(row H G M p).val<_;rw [shape];omega

theorem full_resident (K raw base : ℕ) (m : Memory w) (room : outputBase H G M b base<2^w) :
    TablesOK H G M b base ((phase w K H G M b raw base).image m):=
  (prepared w H G M b base m room).2.1.below fun _x hx=>ProbeStage.Native.columns_frame _ _ (.inl hx)
end
end Hierarchy.DescentResetStemHeaders

namespace Hierarchy.DescentResetStemIssuer
open DescentSIMDLookup DescentPackedZip DescentResetStemMux Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w Q K : ℕ}

theorem original_below (base : ℕ) (key : Fin Q→Expr) (head : Fin Q→Fin K→Expr) (a b M H G out : ℕ)
    (m : Memory w) (price : base+words K a b M≤out) (word : out<2^w) (x : ℕ) (early : x<base) :
    output base key head a b M H G out m x=m x:=by
  have low : x<out:=early.trans_le ((Nat.le_add_right ..).trans price)
  exact (ProbeStage.Native.columns_frame (fields base key head a b M) _ (.inl low)).trans
    ((mount K a b M base m (price.trans_lt word)).2.2.2.1 x (.inl early))

end
end Hierarchy.DescentResetStemIssuer

namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Layout
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentResetStemHeaders ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f b K P H G M Q w : ℕ}
variable (A : Mixed.Layout) (parse : DescentResetStemKey.Decoder D f)
  (s : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)

/-- No value or predicate from the original private stem is used. -/
theorem header_stays (m : Memory w) (room : A.stop D f b K M P H G Q<2^w) :
    TablesOK H G M b (A.hdr D f M P H G Q) (A.output parse s src b K M P H G m):=by
  let mapBase:=A.mapping D f M P G Q
  let headBase:=A.hdr D f M P H G Q
  let muxBase:=A.mux D f b K M P H G Q
  let out:=A.out D f b K M P H G Q
  let first:=DescentResetStemKey.Columns.output parse s src A.base M P G m
  let mid:=(DescentResetStemKeyReindex.phase w mapBase P H G M).image first
  let sent:=(phase w (2*K) H G M b A.raw headBase).image mid
  have pre : outputBase H G M b headBase≤ muxBase:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have ext : muxBase≤out:=Nat.le_add_right ..
  have word:= (show out≤A.stop D f b K M P H G Q from Nat.le_add_right ..).trans_lt room
  have inputs:=full_resident (H:=H) (G:=G) (M:=M) (b:=b) (2*K) A.raw headBase mid (pre.trans_lt (ext.trans_lt word))
  exact inputs.below (fun x low=>DescentResetStemIssuer.original_below muxBase (A.key D f M P H G)
    (A.heads D f b M P H G s (K:=K)) (f+2) b M H G out sent le_rfl word x (low.trans_le pre))

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Layout

end OAI
