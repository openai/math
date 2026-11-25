import OAI.Hierarchy.DescentDonorWalkObservation
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Host-shared ordinal and hub tables from the true preceding host census -/
namespace Hierarchy.DescentRawCablePanel.DonorHeaders
open DescentHaloWalkRAM DescentPackedZip DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {D H w : ℕ} (R : Fin H→Fin D→Option (Fin H)) (flag : Fin H→Bool)
local notation "P" => breadth D

/-- The missing-venue sentinel requires no extra cell in the real predecessor
census. Its rank stays meaningful while its hub flag is false. -/
def hubExpr (ends flags : Bank) (H : ℕ) : Expr :=
  .branch .lt (.lookup ends .row) (.lit H) (.lookup flags (.lookup ends .row)) (.lit 0)

def schedule (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (hub : Bank) (ord tags H D w : ℕ) :=
  ((scan w T.endpoints.base (H*breadth D) (body W H D 4)).seq (scan w ord (H*breadth D) (Ranks.body T (breadth D)))).seq
    (scan w tags (H*breadth D) (hubExpr T.endpoints hub H))
def after (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (hub : Bank) (ord tags H D : ℕ) (m : Memory w) :=
  image tags (H*breadth D) (hubExpr T.endpoints hub H)
    (image ord (H*breadth D) (Ranks.body T (breadth D)) (image T.endpoints.base (H*breadth D) (body W H D 4) m))

def clocks (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (hub : Bank) (H D : ℕ) :=
  ((4+H*breadth D*(2*(body W H D 4).work+4))+(4+H*breadth D*(2*(Ranks.body T (breadth D)).work+4)))+
    (4+H*breadth D*(2*(hubExpr T.endpoints hub H).work+4))

private def report (A : Procedure w) (m dest : Memory w) (ticks : ℕ)
    (ranks flags frame : Prop) : Prop :=
  A.Exec m dest ticks ∧ ranks ∧ flags ∧ frame ∧ CheapCode A

private theorem append_scan (A : Procedure w) (m before : Memory w) (ticks tags n : ℕ)
    (field : Expr) (old ranks flags frame : Prop)
    (first : A.Exec m before ticks ∧ old ∧ CheapCode A) (fit : field.Fits w tags)
    (limit : tags+n<2^w) (save : old → ranks) (values : flags) (keep : frame) :
    report (A.seq (scan w tags n field)) m (image tags n field before)
      (ticks+(4+n*(2*field.work+4))) ranks flags frame := by
  exact ⟨@Procedure.Exec.then w A (scan w tags n field) m before (image tags n field before) ticks
      (4+n*(2*field.work+4)) first.1 (scan_exec tags n field before fit limit),
    save first.2.1,values,keep,
    @ProtocolRAM.cheap_seq w A (scan w tags n field) first.2.2 (scan_cheap w tags n field)⟩

private theorem eval_hub (ends hub : Bank) (memory : Memory w) (i : Word w) (u : Option (Fin H))
    (readEnd : ends.read memory i=(number u:Word w)) (range : H<2^w)
    (readHub : ∀v : Fin H,hub.read memory (v.val:Word w)=((flag v).toNat:Word w)) :
    (hubExpr ends hub H).eval memory i=((u.elim false flag).toNat:Word w) := by
  change (if DescriptorExpr.Comparison.lt.test (ends.read memory i) (H:Word w)
    then hub.read memory (ends.read memory i) else 0)=_
  rw [readEnd]
  cases u with
  | none => simp [number,Option.elim,DescriptorExpr.Comparison.test]
  | some v =>
    have lt : (v.val:Word w)<(H:Word w) := by
      change (v.val:Word w).val<(H:Word w).val
      rw [Fin.val_cast_of_lt (v.isLt.trans range),Fin.val_cast_of_lt range]
      exact v.isLt
    simpa [number,Option.elim,DescriptorExpr.Comparison.test,lt] using readHub v

private theorem endpoint_read (ends : Bank) (ord n : ℕ) (f g : Expr) (m : Memory w)
    (room : n≤ends.size) (fit : ends.Fits w ord) (i : Fin n) :
    ends.read (image ord n g (image ends.base n f m)) (i.val:Word w)=f.eval m (i.val:Word w) := by
  have earlier : ends.base+i.val<ord :=
    (Nat.add_lt_add_left (i.isLt.trans_le room) ends.base).trans_le fit.2.2
  exact (bank_read ends _ (i.isLt.trans_le room) fit).trans
    ((ProtocolRAMGeneratedWrite.frame_image ord n g _ _ (.inl earlier)).trans
      (ProtocolRAMGeneratedWrite.read_image ends.base n f m i))

set_option maxHeartbeats 600000 in
theorem run (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (hub : Bank) (ord tags : ℕ) (m : Memory w)
    (first : DescentHaloWalkRAM.Fits W T.endpoints.base H D w) (second : Ranks.Fits T ord H P w)
    (next : ord+H*P≤tags) (limit : tags+H*P<2^w)
    (roster : DescentHaloWalkRAM.Reads W R m)
    (heads : ∀(v:Fin H)(p:Fin P),m (T.start.base+(Ranks.id v p).val)=((v.val*P:ℕ):Word w))
    (prior : T.start.base+T.start.size≤T.endpoints.base)
    (range : H<2^w) (hubs : hub.Fits w T.endpoints.base) (amount : H≤hub.size)
    (source : ∀v : Fin H,m (hub.base+v.val)=(Bool.toNat (flag v):Word w)) :
    let dest:=after W T hub ord tags H D m
    report (schedule W T hub ord tags H D w) m dest (clocks W T hub H D)
      (∀v p,dest (ord+(DescentHaloWalkRAM.row v p).val)=(observedRank R v p:Word w))
      (∀v p,dest (tags+(DescentHaloWalkRAM.row v p).val)=((observedHub R v flag p).toNat:Word w))
      (∀a,a<T.endpoints.base→dest a=m a) := by
  intro dest
  let n:=H*P
  let f:=body W H D 4
  let g:=Ranks.body T P
  let mid:=image T.endpoints.base n f m
  let ranks:=image ord n g mid
  let field:=hubExpr T.endpoints hub H
  have span : T.endpoints.base+n≤ord :=
    (Nat.add_le_add_left second.sizeEnd T.endpoints.base).trans second.endpoints.2.2
  have startOrd : T.endpoints.base≤ord := (Nat.le_add_right T.endpoints.base n).trans span
  have ordTags : ord≤tags := (Nat.le_add_right ord n).trans next
  have early (a : ℕ) (before : a<T.endpoints.base) : ranks a=m a :=
    (ProtocolRAMGeneratedWrite.frame_image ord n g mid a (.inl (before.trans_le startOrd))).trans
      (ProtocolRAMGeneratedWrite.frame_image T.endpoints.base n f m a (.inl before))
  have endFit : T.endpoints.Fits w tags := ⟨second.endpoints.1,second.endpoints.2.1,
    second.endpoints.2.2.trans ordTags⟩
  have hubFit : hub.Fits w tags := ⟨hubs.1,hubs.2.1,hubs.2.2.trans (startOrd.trans ordTags)⟩
  have fit : field.Fits w tags := ⟨⟨endFit,trivial⟩,trivial,⟨hubFit,endFit,trivial⟩,trivial⟩
  refine append_scan ((scan w T.endpoints.base n f).seq (scan w ord n g)) m ranks
    ((4+n*(2*f.work+4))+(4+n*(2*g.work+4))) tags n field
    (∀(v:Fin H)(p:Fin P),ranks (ord+(DescentHaloWalkRAM.row v p).val)=(observedRank R v p:Word w))
    _ _ _ (DescentHaloCompilation.rank_rows R W T ord first second m roster heads prior) fit limit ?_ ?_ ?_
  · intro printed v p
    let i:=DescentHaloWalkRAM.row v p
    exact (ProtocolRAMGeneratedWrite.frame_image tags n field ranks (ord+i.val)
      (.inl ((Nat.add_lt_add_left i.isLt ord).trans_le next))).trans (printed v p)
  · intro v p
    let i:=DescentHaloWalkRAM.row v p
    refine (ProtocolRAMGeneratedWrite.read_image tags n field ranks i).trans
      (eval_hub flag T.endpoints hub ranks (i.val:Word w) (walk R v (path p) 4) ?_ range ?_)
    · exact (endpoint_read T.endpoints ord n f g m second.sizeEnd second.endpoints i).trans
        (body_at W T.endpoints.base first R m roster v p 4)
    · intro u
      have small:=u.isLt.trans_le amount
      exact (bank_read hub ranks small hubs).trans
        ((early _ ((Nat.add_lt_add_left small hub.base).trans_le hubs.2.2)).trans (source u))
  · intro a small
    exact (ProtocolRAMGeneratedWrite.frame_image tags n field ranks a
      (.inl (small.trans_le (startOrd.trans ordTags)))).trans (early a small)


end
end Hierarchy.DescentRawCablePanel.DonorHeaders

end OAI
