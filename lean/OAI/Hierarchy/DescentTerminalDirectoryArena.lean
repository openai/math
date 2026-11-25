import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalPlaneArena
import OAI.Hierarchy.DescentTerminalRowArenaSort
import OAI.Hierarchy.DescentTerminalMeterSuffix

namespace OAI
/-! # Home-page windows and paid row-event staging after the actual terminal sort -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalRowArena DescentTerminalVertexFields
open DescentTerminalSiteShelves
open DescentTerminalDataPlane.Arena (buy size)
noncomputable section

theorem bounds (A:Arena) (pool:ℕ) :
    endEvents A pool≤A.start+92*(A.sites+A.rows+A.packets+pool+1) := by
  have initial:=A.finish_le
  have pages:=DescentTerminalDataPlane.Arena.cost (A.sites+1)
  have events_:=DescentTerminalDataPlane.Arena.cost pool
  change A.finish+size (A.sites+1)+size pool≤_
  by_cases noSites : A.sites=0
  · have emptyPage : size (A.sites+1)=2 := by rw [noSites]; decide
    omega
  · omega

private theorem gather_fits {w out : ℕ} (D : Directory)
    (active : D.span.active.Fits w out) (owner : D.span.owner.Fits w out)
    (localRow : D.span.localRow.Fits w out) (ports : D.ports.Fits w out)
    (count : D.count.Fits w out) (firstWord : D.firstWord.Fits w out)
    (skip : D.skip.Fits w out) (texture : D.texture.Fits w out)
    (countShift : D.countShift.Fits w out) (modeShift : D.modeShift.Fits w out)
    (skipShift : D.skipShift.Fits w out) (wordShift : D.wordShift.Fits w out) :
    (gather D).Fits w out := by
  let site := Expr.lookup D.span.owner .row
  have siteFit : site.Fits w out := ⟨owner,trivial⟩
  have rowFit : (Expr.lookup D.span.localRow .row).Fits w out := ⟨localRow,trivial⟩
  have portFit : (Expr.lookup D.ports site).Fits w out := ⟨ports,siteFit⟩
  have modeFit : (rowMode D).Fits w out := ⟨rowFit,portFit,trivial,⟨rowFit,portFit⟩,trivial⟩
  have addrFit : (Expr.lookup D.firstWord site).Fits w out := ⟨firstWord,siteFit⟩
  exact ⟨⟨active,trivial⟩,trivial,trivial,⟨countShift,count,siteFit⟩,⟨modeShift,modeFit⟩,
    ⟨skipShift,skip,siteFit⟩,⟨wordShift,texture,addrFit⟩,⟨texture,addrFit,trivial⟩⟩

theorem gather_room {w:ℕ} (A:Arena) (pool:ℕ) (early:Fin 8→Bank)
    (prior:∀j,(early j).base+(early j).size≤A.finish) (end_:endEvents A pool<2^w) :
    (gather (directory A early)).Fits w (events A pool).base := by
  let t:=(events A pool).base
  have original:A.finish<2^w:=by change A.finish+size (A.sites+1)+size pool<2^w at end_;omega
  have mono:A.finish≤t:=Nat.le_add_right ..
  have static (i:Fin 8) : (early i).Fits w t:=
    ⟨Nat.two_pow_pos _,by have:=prior i;omega,(prior i).trans mono⟩
  have bfit (i:ℕ) (h:i<22) : (A.bank i).Fits w t:=
    DescentTerminalDenseHeaderRAM.fits_mono (A.fits_band original h (by decide)) mono
  have pf : (page A).Fits w t := by
    change 0<size (A.sites+1) ∧ size (A.sites+1)<2^w ∧ _≤_
    exact ⟨Nat.two_pow_pos _,by change A.finish+size (A.sites+1)+size pool<2^w at end_;omega,le_rfl⟩
  exact gather_fits (directory A early) (bfit 10 (by decide)) (bfit 11 (by decide))
    (bfit 12 (by decide)) (static 0) (static 1) (static 2) (static 3) pf
    (static 4) (static 5) (static 6) (static 7)

theorem guarded_room {w blocks : ℕ} (m:MaskedShelf blocks) (end_:ℕ) (sites:ℕ)
    (fits : ∀i,(m.channel i).Fits w end_ ∧ (m.weight i).Fits w end_) (rom:m.table.Fits w end_) :
    (guardedMask m sites).Fits w end_ := by
  have add (ls:List (Fin (channels blocks))) : (sumExpr (maskTerm m) ls).Fits w end_ := by
    induction ls with
    | nil=>trivial
    | cons i rest ih=>exact ⟨⟨(fits i).2,(fits i).1,trivial⟩,ih⟩
  exact ⟨trivial,trivial,⟨rom,add _⟩,trivial⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
