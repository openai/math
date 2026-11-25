import OAI.Hierarchy.DescentResetPeerPublicTerms

namespace OAI
/-! # Address bounds of every original structural reset probe -/
namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentSIMDLookup DescentResetLocalRoster DescentDyadicSpan ProtocolRAM
noncomputable section
variable (L : RawTables.Layout) (A : DescentContactPreROM.Layout) (old : Banks A) {w : ℕ}

/-- Every candidate in the four finite probe families, including empty old slots, reads
only the earlier directory, private pages, literal dictionaries and issued contact columns. -/
theorem term_fits
    (keys : ∀j,(old.keys j).Fits w L.base) (pages : ∀s r,(old.pages s r).Fits w L.base)
    (starts : old.actorStarts.Fits w L.base) (actors : old.actorData.Fits w L.base)
    (before : L.endAddress ≤ A.first) (room : A.endAddress < 2^w) :
    ∀j c,((terms L A old).all j c).Fits w A.endAddress := by
  classical
  obtain ⟨a,b,c,d,e⟩:=A.ordered
  have past : L.endAddress ≤ A.endAddress:=before.trans (a.trans (b.trans (c.trans (d.trans e))))
  obtain ⟨o,p,q,r⟩:=L.bounds
  have below : L.base ≤ A.endAddress:=o.trans (p.trans (q.trans (r.trans past)))
  have fresh (bank : Bank) (cut : bank.base+bank.size ≤ L.endAddress) : bank.Fits w A.endAddress :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((cut.trans past).trans_lt room),cut.trans past⟩
  have prior {bank : Bank} (fits : bank.Fits w L.base) : bank.Fits w A.endAddress :=
    ⟨fits.1,fits.2.1,fits.2.2.trans below⟩
  let n:=span (L.hosts*L.shapes)
  let a₀:=span (L.shapes*2^(L.keyBits*L.lanes))
  let b₀:=span (L.shapes*2^L.lanes)
  let depth:=PrivateEvidence.page L.shapes L.privateSlots L.privateBits L.lanes
  have hu : L.first=L.base+(2*n+L.privateSlots*depth):=rfl
  have hv : L.second=L.first+(n+a₀):=rfl
  have hw : L.trunk=L.second+(n+a₀):=rfl
  have hx : L.endAddress=L.trunk+(n+b₀):=rfl
  have par : (PrivateEvidence.parent L.base L.hosts L.shapes).Fits w A.endAddress := by
    apply fresh
    change L.base+n ≤ L.endAddress
    omega
  have liftOld (bank : Bank) (fits : bank.Fits w L.base) (i : ℕ) :
      (PrivateEvidence.atOld L.base L.hosts L.shapes bank i).Fits w A.endAddress :=
    ⟨prior fits,⟨⟨par,trivial⟩,trivial⟩⟩
  have stem (side : Bool) (x : Expr) (fit : x.Fits w A.endAddress) :
      (RawTables.stemOperand L side x).Fits w A.endAddress := by
    let t:=RawTables.stemAddress L side
    have stop : t+n+a₀ ≤ L.endAddress:=by cases side <;> dsimp [t,RawTables.stemAddress] <;> omega
    refine ⟨fresh _ ?_,⟨fresh _ ?_,trivial⟩,fit⟩
    · change t+n+a₀ ≤ L.endAddress
      exact stop
    · change t+n ≤ L.endAddress
      omega
  intro j chunk
  obtain ⟨j,rfl⟩:=(Axes.order _ _ _).surjective j
  rw [Axes.Fields.all_at]
  rcases j with j | j | t | j
  · exact stem _ _ (liftOld _ (keys j) chunk.val)
  · refine ⟨fresh _ ?_,⟨fresh _ ?_,trivial⟩,prior actors,⟨prior starts,trivial⟩,trivial⟩
    · change L.trunk+n+b₀ ≤ L.endAddress
      omega
    · change L.trunk+n ≤ L.endAddress
      omega
  · have table:=DescentContactProbePitch.table_fits A.hosts A.shapes A.groups A.batch A.fieldBits A.pitchBase
      ((d.trans e).trans_lt room) 4
    apply DescentContactProbePitch.atChunk_fits A.fieldBits A.pitchBase A.endAddress
      ⟨table.1,table.2.1,table.2.2.trans (d.trans e)⟩ _ _ chunk
    exact ⟨A.output_fits (A.index t.1 t.2) room,trivial⟩
  · change (if h : ∃p,localPrivateId A.residual (2^A.n) L.privateSlots p=j then
        PrivateEvidence.operand L.base L.hosts L.shapes L.privateSlots L.privateBits L.lanes
          (old.pages h.choose.1 h.choose.2.1) h.choose.2.2 chunk.val else .lit 0).Fits w A.endAddress
    split
    next use =>
      let x:=use.choose
      have slot : (x.2.2.val+1)*depth ≤ L.privateSlots*depth:=Nat.mul_le_mul_right _ x.2.2.isLt
      rw [Nat.succ_mul] at slot
      refine ⟨fresh _ ?_,⟨fresh _ ?_,trivial⟩,liftOld _ (pages ..) chunk.val⟩
      · change L.base+2*n+x.2.2.val*depth+depth ≤ L.endAddress
        omega
      · change L.base+n+n ≤ L.endAddress
        omega
    next =>trivial

end
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

end OAI
