import OAI.Hierarchy.DescentStemNumberOperands
import OAI.Hierarchy.DescentStemProjectedRegister

namespace OAI
/-! # Address bounds for the six physical inputs to a numbered stem -/
namespace Hierarchy
open DescentSIMDLookup DescentDyadicSpan DescentPackedZip DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

namespace DescentStemNumberOperands.Plan
theorem all_fit (P : Plan) {w : ℕ} (base : ℕ) (saved : Bank)
    (x : Fin (2^P.coord.fine)) (lo : Fin (2^P.coord.residual)) (signed self «meta» : Expr)
    (sig : signed.Fits w base) (who : self.Fits w base) (active : «meta».Fits w base)
    (key : saved.Fits w base) (room : P.endAddress base<2^w) (j : Fin 6) :
    (P.stem base saved x lo signed self «meta» j).Fits w (P.endAddress base):=by
  have lo₁ : base≤P.convertBase base:=by rw [convertBase,P.coord.extent];omega
  have lo₂ : P.convertBase base≤P.endAddress base:=Nat.le_add_right ..
  have cast (j : Fin 3) (e : Expr) (read : e.Fits w base) : (P.converted base j e).Fits w (P.endAddress base):=by
    let pair:=Book.tables P.gate P.width P.coord.lanes (P.convertBase base) j
    obtain ⟨l,r⟩:=Book.geometry P.gate P.width P.coord.lanes (P.convertBase base) j le_rfl room (P.width_bound j)
    have fit:DescentPackedZip.Fits pair e (.lit 0) (P.rawWidth j) 0 P.coord.lanes (P.endAddress base) w:=
      ⟨ProtocolRAMGeneratedWrite.fits_mono _ (lo₁.trans lo₂) read,trivial,l,r,rfl,rfl⟩
    exact ⟨fit.apply,fit.right,fit.shift,fit.left⟩
  have axis (i : Fin 3) : (P.coord.src base saved i x lo).Fits w (P.endAddress base):=
    ProtocolRAMGeneratedWrite.fits_mono _ lo₂
      (P.coord.layout.src_fits base saved (P.coord.number (i,x,lo)) key (lo₂.trans_lt room))
  fin_cases j
  · exact cast 0 signed sig
  · exact axis 0
  · exact cast 1 self who
  · exact axis 1
  · exact cast 2 «meta» active
  · exact axis 2
end DescentStemNumberOperands.Plan

namespace DescentResetStemPackedIssue.Mixed.Projected
open DescentResetStemIncidence
theorem signed_register_fits {w D f Q : ℕ} (base ptr K P H G X M₀ M b : ℕ) (x : Fin X) (j : Fin Q)
    (pointer : ptr+span H≤base) (roof : extent base ptr D f b K P H G X M₀ M Q<2^w) :
    (signedRegister (D:=D) (f:=f) base ptr K P H G X M₀ M x j).Fits w
      (extent base ptr D f b K P H G X M₀ M Q):=by
  let start:=splitAt base Q D P G X f M₀ M
  let a:=plan start ptr K H
  let loc:=a.mapping D f M P G (X*Q)
  let cap:=a.hdr D f M P H G (X*Q)
  let limit:=a.stop D f (b*7) K M P H G (X*Q)
  have part : base≤ start:=by dsimp [start,splitAt];rw [DescentResetStemProject.extent];omega
  have left : start≤loc:=by
    dsimp [loc,a,plan,Layout.mapping,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start]
    omega
  have middle : loc≤cap:=Nat.le_add_right ..
  have right : cap≤limit:=by
    dsimp only [cap,limit,Layout.stop,Layout.out,Layout.mux,DescentResetStemHeaders.outputBase]
    omega
  change limit<2^w at roof
  have room:=right.trans_lt roof
  let q:=finProdFinEquiv (j,(0:Fin (D+1)).succ)
  have raw:=DescentResetStemProject.page_fits q x ((left.trans middle).trans_lt room)
  let bank:=DescentResetStemProject.bank base (Q*(D+2)) P G X f M₀ M q x
  have ok : bank.Fits w loc:=⟨raw.1,raw.2.1,raw.2.2.trans left⟩
  exact ProtocolRAMGeneratedWrite.fits_mono _ right
    (DescentResetStemKeyReindex.fits bank ok (pointer.trans (part.trans left)) room)
end DescentResetStemPackedIssue.Mixed.Projected
end
end Hierarchy

end OAI
