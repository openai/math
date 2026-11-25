import OAI.Hierarchy.ProbeSparseParticipantSheet
import OAI.Hierarchy.TaggedWideROMRead
import OAI.Hierarchy.ProtocolRAMRowChoiceFits
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # RAM input pages for the original sparse elected-site scatter -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM SiteScatter
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

variable {W T : ℕ}

theorem PublicSheet.of_origin (p : Shape) (sites rom start : ℕ) (fields : Fields p) (m : Memory W)
    (source : p.Origin sites rom m)
    (table : ∀j : Fin 3,(RoleROM.bank (rom+j.val*p.count) p.count).Fits W (start+1))
    (mult : (RoleROM.bank (rom+3*p.count) sites).Fits W (start+1))
    (fit : ∀i,(fields.selected i).Fits W (start+1) ∧ (fields.site i).Fits W (start+1) ∧
      ∀j,(fields.value i j).Fits W (start+1))
    (siteRoom : sites≤2^W) (partyRoom : p.parties≤2^W) (colRoom : p.columns≤2^W)
    (room : start+p.span sites<2^W) : PublicSheet p sites rom start W fields m := by
  let stride:=RoleROM.bank (rom+3*p.count) sites
  have col (j : Fin 3) : (SiteScatter.column rom p.candidates p.parties p.columns j).Fits W (start+1):=⟨table j,trivial⟩
  have tag (f : Fin p.parties→Expr) (h : ∀i,(f i).Fits W (start+1)) :
      (SiteScatter.localTag (I:=p.candidates) (C:=p.columns) rom f).Fits W (start+1):=
    BoughtSockets.choose_fits_bound _ _ _ _ (fun i=>CatalogueRows.fits_atRow _ _ (h i) (col 0)) (col 1)
  have val : (SiteScatter.fieldValue (I:=p.candidates) rom fields.value).Fits W (start+1):=
    BoughtSockets.choose_fits_bound _ _ _ _ (fun i=>BoughtSockets.choose_fits_bound _ _ _ _
      (fun j=>CatalogueRows.fits_atRow _ _ ((fit i).2.2 j) (col 0)) (col 2)) (col 1)
  have stored : (SiteScatter.selectedValue (I:=p.candidates) rom fields.selected fields.value).Fits W (start+1):=
    ⟨tag _ (fun i=>(fit i).1),trivial,trivial,val⟩
  have index : (SiteScatter.fieldIndex (I:=p.candidates) (C:=p.columns) rom stride fields.site).Fits W (start+1):=
    ⟨⟨mult,tag _ (fun i=>(fit i).2.1)⟩,col 2⟩
  have space : start+1+sites*p.columns+p.count+p.count<2^W := by
    dsimp only [Shape.span] at room
    omega
  refine ⟨source.directory,by omega,partyRoom,colRoom,?_,stored,⟨stored,trivial,trivial,trivial,index⟩,space⟩
  intro s
  exact RoleROM.read source.strides .row (s.val:Word W) s siteRoom rfl

/-- A previous scatter preserves the public rows on their stated occupied
interval. Directory mounts are reconstructed cell by cell, without a
second evaluation of their originating word map. -/
theorem Shape.Origin.copy_low (p : Shape) {sites rom : ℕ} {initial m : Memory W}
    (source : p.Origin sites rom initial) (fix : ∀i,rom≤ i→i<rom+p.advice sites→m i=initial i) :
    p.Origin sites rom m := by
  constructor
  · intro j i
    have hj:=Nat.mul_le_mul_right p.count j.isLt
    rw [Nat.succ_mul] at hj
    have hi : i.val < p.count := i.isLt
    change m (rom+j.val*p.count+i.val)=_
    rw [fix _ (by omega) (by unfold Shape.advice;omega)]
    exact source.directory j i
  · intro s
    have hs:=s.isLt
    change m (rom+3*p.count+s.val)=_
    rw [fix _ (by omega) (by unfold Shape.advice;omega)]
    exact source.strides s

theorem Dated.public_ballot_sheet (p : Dated T) (rom work : ℕ) (table : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (initial m : Memory W) (j : Fin T)
    (fix : ∀i,p.ballotROM rom j≤ i→i<p.ballotROM rom j+(p.ballot j).advice p.sites→
      m i=p.words rom table transport initial i)
    (x : Fields (p.ballot j))
    (directories : ∀i : Fin 3,(RoleROM.bank (p.ballotROM rom j+i.val*(p.ballot j).count) (p.ballot j).count).Fits W (work+1))
    (mult : (RoleROM.bank (p.ballotROM rom j+3*(p.ballot j).count) p.sites).Fits W (work+1))
    (safe : ∀i,(x.selected i).Fits W (work+1) ∧ (x.site i).Fits W (work+1) ∧ ∀c,(x.value i c).Fits W (work+1))
    (sites : p.sites≤2^W) (party : (p.ballot j).parties≤2^W) (cols : (p.ballot j).columns≤2^W)
    (space : work+(p.ballot j).span p.sites<2^W) :
    PublicSheet (p.ballot j) p.sites (p.ballotROM rom j) work W x m :=
  PublicSheet.of_origin _ _ _ _ _ _ (Shape.Origin.copy_low _ (p.ballot_origin rom table transport initial j) fix)
    directories mult safe sites party cols space

/-- Ordinary RAM lookup banks include dyadic padding; these numerical
bounds cover their actual extents even when the logical page is empty. -/
private theorem page_bank {W start base n endROM : ℕ} (baseFits : base≤endROM)
    (sizeFits : n≤endROM) (gap : 3*endROM+2≤ start) (room : start<2^W) :
    (RoleROM.bank base n).Fits W (start+1) := by
  change 0<ProtocolRAMPurchaseSampler.span n ∧ ProtocolRAMPurchaseSampler.span n<2^W ∧
    base+ProtocolRAMPurchaseSampler.span n≤ start+1
  have low:=ProtocolRAMPurchaseSampler.lt_span n
  have high:=ProtocolRAMPurchaseSampler.span_le n
  omega

theorem Dated.global_banks (p : Dated T) {rom work : ℕ}
    (gap : 3*p.romEnd rom+2≤work) (room : work<2^W) :
    (RoleROM.bank (p.siteROM rom) p.siteDirectorySize).Fits W (work+1) ∧
    (p.siteStride rom).Fits W (work+1) := by
  have endROM : p.siteROM rom+p.siteDirectorySize≤p.romEnd rom := by
    dsimp only [Dated.romEnd,Dated.maskROM,Dated.controlROMStart,Dated.firstROM,endOf]
    omega
  have first : rom+p.sites=p.siteROM rom:=rfl
  exact ⟨page_bank (by omega) (by omega) gap room,
    page_bank (by omega) (by omega) gap room⟩

theorem PublicSheet.of_placement (p : Shape) {sites rom start endROM : ℕ} (fields : Fields p) (m : Memory W)
    (source : p.Origin sites rom m) (page : rom+p.advice sites≤endROM)
    (gap : 3*endROM+2≤ start) (paid : start+p.span sites<2^W)
    (fit : ∀i,(fields.selected i).Fits W (start+1) ∧ (fields.site i).Fits W (start+1) ∧
      ∀j,(fields.value i j).Fits W (start+1))
    (parties : p.parties≤2^W) (cols : p.columns≤2^W) : PublicSheet p sites rom start W fields m := by
  have work : start<2^W := by omega
  dsimp only [Shape.advice] at page
  apply PublicSheet.of_origin p sites rom start fields m source _ _ fit (by omega) parties cols paid
  · intro j
    have h:=Nat.mul_le_mul_right p.count j.isLt
    rw [Nat.succ_mul] at h
    exact page_bank (by omega) (by omega) gap work
  · exact page_bank (by omega) (by omega) gap work

/-- The entire original Dated ROM is admissible before this dates's
public sheet. Its three input directories, its site-stride directory and
its complete emitted scatter workload are accounted for by the global
read-only and writable tape endpoints. -/
theorem Dated.ballot_public (p : Dated T) (rom work : ℕ) (table : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (initial m : Memory W) (j : Fin T)
    (fix : ∀i,p.ballotROM rom j≤ i→i<p.ballotROM rom j+(p.ballot j).advice p.sites→
      m i=p.words rom table transport initial i)
    (x : Fields (p.ballot j))
    (safe : ∀i,(x.selected i).Fits W (p.ballotStart work j+1) ∧ (x.site i).Fits W (p.ballotStart work j+1) ∧
      ∀c,(x.value i c).Fits W (p.ballotStart work j+1))
    (party : (p.ballot j).parties≤2^W) (cols : (p.ballot j).columns≤2^W)
    (gap : 3*p.romEnd rom+2≤work) (range : p.workEnd work<2^W) :
    PublicSheet (p.ballot j) p.sites (p.ballotROM rom j) (p.ballotStart work j) W x m := by
  have origin:=Shape.Origin.copy_low _ (p.ballot_origin rom table transport initial j) fix
  have endPage : p.ballotROM rom j+(p.ballot j).advice p.sites≤p.controlROMStart rom:=
    extent _ _ j
  have romRange : p.controlROMStart rom≤p.romEnd rom:=
    by dsimp only [Dated.romEnd,Dated.maskROM,endOf];omega
  have minWork : work≤p.ballotStart work j:=
    by dsimp only [Dated.ballotStart,offset,Dated.rolesEnd];omega
  have runPage : p.ballotStart work j+(p.ballot j).span p.sites≤p.controlStart work:=
    extent _ _ j
  have limit : p.controlStart work≤p.workEnd work:=
    by dsimp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,endOf];omega
  exact PublicSheet.of_placement _ _ _ origin (endPage.trans romRange) (gap.trans minWork)
    (runPage.trans_lt (limit.trans_lt range)) safe party cols

theorem Dated.control_public (p : Dated T) (rom work : ℕ) (table : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (initial m : Memory W) (j : Fin T)
    (fix : ∀i,p.controlROM rom j≤ i→i<p.controlROM rom j+(p.control j).advice p.sites→
      m i=p.words rom table transport initial i)
    (x : Fields (p.control j))
    (safe : ∀i,(x.selected i).Fits W (p.controlBase work j+1) ∧ (x.site i).Fits W (p.controlBase work j+1) ∧
      ∀c,(x.value i c).Fits W (p.controlBase work j+1))
    (party : (p.control j).parties≤2^W) (cols : (p.control j).columns≤2^W)
    (gap : 3*p.romEnd rom+2≤work) (range : p.workEnd work<2^W) :
    PublicSheet (p.control j) p.sites (p.controlROM rom j) (p.controlBase work j) W x m := by
  have origin:=Shape.Origin.copy_low _ (p.control_origin rom table transport initial j) fix
  have endPage : p.controlROM rom j+(p.control j).advice p.sites≤p.maskROM rom:=extent _ _ j
  have romRange : p.maskROM rom≤p.romEnd rom:=by dsimp only [Dated.romEnd];omega
  have minWork : work≤p.controlBase work j:=
    by dsimp only [Dated.controlBase,offset,Dated.controlStart,endOf,Dated.rolesEnd];omega
  have runPage : p.controlBase work j+(p.control j).span p.sites≤p.maskStart work:=extent _ _ j
  have limit : p.maskStart work≤p.workEnd work:=by dsimp only [Dated.workEnd,Dated.slotStart];omega
  exact PublicSheet.of_placement _ _ _ origin (endPage.trans romRange) (gap.trans minWork)
    (runPage.trans_lt (limit.trans_lt range)) safe party cols

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
