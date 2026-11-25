import OAI.Hierarchy.DescentResetRetainedSetup
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentResetChannelSubwords

namespace OAI
/-! # Exact origin of each native retained operand after the saved basis change -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGLPacked DescentGLPacked.BankImage DescentGLNielsen
open DescentGL DescentColonies DescentOrdinaryAtomFieldRAM DescentSixParty.Chronology DescentPlainTerminal.Suffix
open DescentIssuedFallbackPanel ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : DescentResetRetainedSetup.Layout)
abbrev Values := Fin v.sources→Fin v.hosts→Fin v.groups→Cell v.wholeWord

def scalarAt (x : v.Values) (i : Fin v.channels) (h : Fin v.hosts) (g : Fin v.groups) (b : Fin v.blocks) :=
  let z:=(finProdFinEquiv.symm i : Fin v.fields×Fin v.previousNodes)
  ScalarOperand.take (a:=v.bits) z.2 (x (v.sourceID z.1 b) h g)
def before (size : 2^(v.high+v.low)=v.groups*v.blocks) (x : v.Values) (i : Fin v.channels)
    (h : Fin v.hosts) (t : Block (v.high+v.low)) :=
  let p:=(finProdFinEquiv.symm (Fin.cast size t) : Fin v.groups×Fin v.blocks)
  v.scalarAt x i h p.1 p.2

theorem basis_reads (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w)
    (prior : ∀i,(old i).Fits w base) (key : saved.Fits w base) (space : v.mixed base<2^w)
    (size : 2^(v.high+v.low)=v.groups*v.blocks) (batch : 2^v.low=v.gatherLanes*v.blocks)
    (hg : 0<v.gatherLanes) (hb : 0<v.blocks) (hp : 0<v.previousLanes)
    (L : DescentGL.Layout (v.high+v.low)) (chosen : m saved.base=((DescentExterior.matrixCode L).val:Word w))
    (x : v.Values) (capacity : ∀i,v.hosts*chunks v.groups v.previousLanes≤(old i).size)
    (read : ∀i,Reads (old i) (x i) v.previousLanes m) (j : Fin v.channels) :
    Dense (h:=v.high) (l:=v.low) (v.mixedBank base j).base
      (fun h t=>v.before size x j h ((rearrange L).symm t)) (v.basisImage base old saved m) :=by
  obtain ⟨lo,a,b,c,_⟩:=v.order base
  have cut:=a.trans (b.trans c)
  let fi:=v.firstCode base w old
  let m₁:=fi.image m
  let m₂:=v.digitImage base old m
  have room:=cut.trans_lt space
  have shapes (i : Fin v.sources) :=Strip.fits (w:=w) base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord i room
  have earlier (i : Fin v.sources) : Reads (v.retiled base i) (x i) v.gatherLanes m₁ :=
    Strip.read base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord old m prior room i (x i) hp (capacity i) (read i)
  have live (i : ℕ) (h:i<v.digits base) : m₂ i=m₁ i:=ROM.frame _ _ _ _ _ (.inl h)
  have fit (i : Fin v.channels) (b₀ : Fin v.blocks) : (v.oldScalar base i b₀).Fits w (v.slots base):=by
    let z:=(finProdFinEquiv.symm i : Fin v.fields×Fin v.previousNodes)
    let p:=v.sourceID z.1 b₀
    have oldFits:=(shapes p).1
    exact ⟨ROM.bank_room (ScalarOperand.pages v.bits v.previousNodes v.gatherLanes) (v.wholeWord*v.gatherLanes)
       (v.digits base) (v.slots base) z.2 le_rfl le_rfl ((b.trans c).trans_lt space),
       ⟨⟨oldFits.1,oldFits.2.1,oldFits.2.2.trans a⟩,trivial⟩⟩
  have see (i : Fin v.channels) (b₀ : Fin v.blocks) : Source (v.oldScalar base i b₀)
      (fun h g=>v.scalarAt x i h g b₀) v.gatherLanes m₂:=by
    let z:=(finProdFinEquiv.symm i : Fin v.fields×Fin v.previousNodes)
    let p:=v.sourceID z.1 b₀
    have cap:=(shapes p).2
    have keep : Reads (v.retiled base p) (x p) v.gatherLanes m₂:=by
      intro rowId
      have addr:= (Nat.add_lt_add_left ((row _ _ _ rowId).isLt.trans_le cap) _).trans_le (shapes p).1.2.2
      exact (live _ addr).trans (earlier p rowId)
    exact ScalarOperand.fetched _ _ z.2 (v.slots base) m₂ (x p) (source_column _ _ (fit i b₀).2.1 _ _ cap keep)
      (fit i b₀).1 rfl (ScalarOperand.initialized (v.digits base) v.bits v.previousNodes v.gatherLanes m₁ z.2)
  obtain ⟨init,initKeep⟩:=Strip.any base v.hosts v.groups v.previousLanes v.gatherLanes v.wholeWord old m prior room
  have oldAddr : saved.base<base:=by have:=key.1;have:=key.2.2;omega
  have keyRead : m₂ saved.base=((DescentExterior.matrixCode L).val:Word w):=
    (live _ (oldAddr.trans_le lo)).trans ((initKeep _ (.inl oldAddr)).trans chosen)
  obtain ⟨last,found,_,dense,_⟩:=SignedFields.from_slots (v.slots base) saved (v.oldScalar base) L size batch hg hb
    (v.scalarAt x) m₂ fit see ⟨key.1,key.2.1,key.2.2.trans (lo.trans a)⟩ keyRead space
  obtain ⟨physical,_,_⟩:=SignedFields.from_slots_any (D:=v.channels) (H:=v.hosts) (h:=v.high) (l:=v.low)
    (b:=v.bits) (M:=v.gatherLanes) (v.slots base) saved (v.oldScalar base) m₂ fit
    ⟨key.1,key.2.1,key.2.2.trans (lo.trans a)⟩ space
  have eqn:=ProtocolRAM.exec_unique _ m₂ _ last physical found
  rw [show v.basisImage base old saved m=last from eqn]
  exact dense j

open DescentSixParty.PackedFlow.Channels in
theorem moved_reads (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w)
    (prior : ∀i,(old i).Fits w base) (key : saved.Fits w base) (space : v.tables base<2^w)
    (size : 2^(v.high+v.low)=v.groups*v.blocks) (batch : 2^v.low=v.gatherLanes*v.blocks)
    (hg : 0<v.gatherLanes) (hb : 0<v.blocks) (hp : 0<v.previousLanes)
    (cut : v.cut≤v.high+v.low) (pitch : v.matrixLanes*v.donors=2^v.low) (live : 0<v.matrixLanes)
    (L : DescentGL.Layout (v.high+v.low)) (chosen : m saved.base=((DescentExterior.matrixCode L).val:Word w))
    (x : v.Values) (capacity : ∀i,v.hosts*chunks v.groups v.previousLanes≤(old i).size)
    (read : ∀i,Reads (old i) (x i) v.previousLanes m) (j : Fin v.channels) :
    Reads (v.hostBank base j) (blockValues cut (v.before size x j) L) v.decodedLanes (v.movedImage base old saved m) :=by
  have pre : v.mixed base≤v.tables base:=Nat.le_add_right ..
  have dense:=v.basis_reads base old saved m prior key (pre.trans_lt space) size batch hg hb hp L chosen x capacity read j
  have product : v.grouped*v.donors=2^(v.high+v.low):=by
    unfold grouped donors
    rw [←pow_add,Nat.add_sub_of_le cut]
  have counts : chunks v.grouped v.matrixLanes=2^v.high:=by
    have regroup:=chunks_group v.grouped v.matrixLanes v.donors live (Nat.two_pow_pos _)
    rw [product,pitch,chunk_count] at regroup
    exact regroup.symm
  have readable : Reads (v.mixedBank base j) (blockValues cut (v.before size x j) L) v.matrixLanes
      (v.basisImage base old saved m):=grouped_remix cut pitch live _ _ L _ dense
  apply Strip.read (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord
    (v.mixedBank base) _ (fun i=>v.mixed_fit base i (pre.trans_lt space)) space j _ live
  · change v.hosts*chunks v.grouped v.matrixLanes≤2^Nat.clog 2 (v.hosts*2^v.high)
    rw [counts];exact Nat.le_pow_clog (by decide) _
  · exact readable

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
