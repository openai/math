import OAI.Computability.BorderVNP.DiagonalTallyReportWrites

/-! # Recovering all private bundle inputs through the native chronological writes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BottomReports RoutingISA

/-- Addresses containing original scanner input words survive the listed stores. -/
def ReportReadsClear (live : ℕ → Prop) (ss : List ReportWrite) :=
  ∀ a, live a → ∀ t ∈ ss, a < t.address ∨ t.address+t.data.length ≤ a

theorem ReportReadsClear.sublist {live : ℕ → Prop} {ss ts : List ReportWrite}
    (h : ReportReadsClear live ts) (incl : ss ⊆ ts) : ReportReadsClear live ss :=
  fun a ha t ht => h a ha t (incl ht)

theorem ReportReadsClear.read {live : ℕ → Prop} {ss : List ReportWrite}
    (h : ReportReadsClear live ss) (m : ℕ → ℕ) {a : ℕ} (ha : live a) :
    applyWrites m ss a=m a := writes_outside m ss a (h a ha)

/-- The opaque one-copy body and scalar sidecar fit in their delivered interval.
The two translated staging bounds are private-assignment address arithmetic. -/
structure ReportBundle.SiteRoom (b : ReportBundle) (l : ReportLayout) (w description : ℕ) : Prop where
  body : (CellSparse.Packet.Source.boxBody b.factors).length ≤ l.bodyCap
  descriptionRoom : l.fieldWidth+l.bodyCap+(TallySidecar.bits l.fieldWidth b.positions).length ≤ description
  values : TallySidecar.Fits l.fieldWidth b.positions
  marked : b.positions.length ≤ b.header.cap
  padding : b.header.boxBase+(b.header.orig+b.positions.length) < 2^w
  translated : ∀ i < b.positions.length, b.header.boxBase+b.relative i < 2^w

/-- All seven cursors are monotone over any suffix of the actual bundle stream. -/
theorem local_le_fold (bs : List ReportBundle) (q : LocalReportCursor) :
    let t := bs.foldl LocalReportCursor.advance q
    q.packed ≤ t.packed ∧ q.refs ≤ t.refs ∧ q.descriptors ≤ t.descriptors ∧
    q.prior ≤ t.prior ∧ q.external ≤ t.external ∧ q.privateUse ≤ t.privateUse ∧
    q.supplement ≤ t.supplement ∧ q.previousRows ≤ t.previousRows := by
  induction bs generalizing q with
  | nil => simp
  | cons b bs ih =>
    have h := ih (q.advance b)
    simp only [List.foldl_cons,LocalReportCursor.advance,ReportCursor.afterBundle] at h ⊢
    omega

/-- The actual compact endpoints fit in their length-only allocated partitions. -/
structure BundleScanRoom (w : ℕ) (bs : List ReportBundle) (q : LocalReportCursor) : Prop where
  packed : (bs.foldl LocalReportCursor.advance q).packed < q.refs
  refs : (bs.foldl LocalReportCursor.advance q).refs < q.descriptors
  descriptors : (bs.foldl LocalReportCursor.advance q).descriptors < 2^w
  prior : (bs.foldl LocalReportCursor.advance q).prior < 2^w
  external : (bs.foldl LocalReportCursor.advance q).external < 2^w
  privateUse : (bs.foldl LocalReportCursor.advance q).privateUse < 2^w
  supplement : (bs.foldl LocalReportCursor.advance q).supplement ≤ q.packed
  rows : (bs.foldl LocalReportCursor.advance q).previousRows < 2^w

/-- The original receipt consists of a complete private bit string at its delivered site address. -/
def ReportBundle.delivered (b : ReportBundle) (l : ReportLayout) (description : ℕ) (m : ℕ → ℕ) :=
  ∀ j : Fin description, m (b.header.siteSlot+j.val)=
    (CellSparse.Packet.Source.siteWithTally l.fieldWidth l.bodyCap b.factors
      (TallySidecar.bits l.fieldWidth b.positions) j).toNat

/-- Recover the header and opaque site string at *each* native iteration from the original
grouped table and receipt, including after earlier packed, checker and operand stores. -/
theorem bundleInputs_of_received (w : ℕ) (l : ReportLayout) (description : ℕ)
    (bs : List ReportBundle) (q : LocalReportCursor) (p : ℕ) (original m : ℕ → ℕ)
    (live : ℕ → Prop) (read : ∀ a, live a → m a=original a)
    (clear : ReportReadsClear live (bundleWrites l bs q))
    (headers : CellPacket.WordsAt original p (bs.flatMap fun b => b.header.words))
    (headerLive : ∀ i < 6*bs.length, live (p+i))
    (sites : ∀ b ∈ bs, b.delivered l description original ∧ b.SiteRoom l w description ∧
      b.header.siteSlot+description ≤ q.packed ∧ ∀ j : Fin description, live (b.header.siteSlot+j.val))
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets < 2^w)
    (headerEnd : p+6*bs.length < 2^w) (room : BundleScanRoom w bs q) :
    bundleInputs w l description bs q p m := by
  induction bs generalizing q p m with
  | nil => trivial
  | cons b bs ih =>
    let next := q.advance b
    let t := bs.foldl LocalReportCursor.advance next
    have mono := local_le_fold bs next
    obtain ⟨hp,hr,hd,hn,he,hu,hs,hw⟩ := room
    change t.packed < q.refs at hp
    change t.refs < q.descriptors at hr
    change t.descriptors < 2^w at hd
    change t.prior < 2^w at hn
    change t.external < 2^w at he
    change t.privateUse < 2^w at hu
    change t.supplement ≤ q.packed at hs
    change t.previousRows < 2^w at hw
    change next.packed ≤ t.packed ∧ next.refs ≤ t.refs ∧ next.descriptors ≤ t.descriptors ∧
      next.prior ≤ t.prior ∧ next.external ≤ t.external ∧ next.privateUse ≤ t.privateUse ∧
      next.supplement ≤ t.supplement ∧ next.previousRows ≤ t.previousRows at mono
    dsimp only [next,LocalReportCursor.advance,ReportCursor.afterBundle] at mono
    obtain ⟨arrived,site,raw,literal⟩ := sites b List.mem_cons_self
    simp only [List.flatMap_cons] at headers
    simp only [List.length_cons,Nat.mul_succ] at headerLive headerEnd
    have headLen : b.header.words.length=6 := rfl
    refine ⟨?_,?_⟩
    · refine ⟨?_,?_,site.body,site.descriptionRoom,width,site.values,by omega,by omega,
        .inl raw,?_,?_,by omega⟩
      · intro i
        rw [read _ (headerLive i.val (by have h : i.val<6 := i.isLt; omega))]
        exact headers.left i
      · intro j
        rw [read _ (literal j)]
        exact arrived j
      · refine ⟨site.marked,?_,?_,?_,?_,site.padding,site.translated,.inr ?_⟩
        all_goals simp only [BundleHeader.writer]
        all_goals unfold ReportBundle.useCount at mono
        all_goals omega
      · constructor
        all_goals try simp only [ReportBundle.frame,DiagonalTallyOperandArray.Frame.nrows,
          DiagonalTallyOperandArray.Frame.nrefs]
        all_goals unfold ReportBundle.useCount at mono
        all_goals omega
    · have headClear := clear.sublist (ss := b.writes l q) (fun _ h => List.mem_append_left _ h)
      apply ih next (p+6) (b.image l q m)
      · intro a ha
        rw [b.writes_image,headClear.read m ha,read a ha]
      · exact clear.sublist (fun _ h => List.mem_append_right _ h)
      · simpa only [headLen] using headers.right
      · intro i hi
        simpa only [Nat.add_assoc] using headerLive (6+i) (by omega)
      · intro s h
        obtain ⟨del,fit,addr,src⟩ := sites s (List.mem_cons_of_mem _ h)
        exact ⟨del,fit,by dsimp [next,LocalReportCursor.advance,ReportCursor.afterBundle]; omega,src⟩
      · omega
      · refine ⟨?_,?_,hd,hn,he,hu,?_,hw⟩
        · change t.packed < q.refs+b.useCount
          omega
        · change t.refs < q.descriptors+5*b.useCount
          omega
        · change t.supplement ≤ q.packed+1+3*b.positions.length
          omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
