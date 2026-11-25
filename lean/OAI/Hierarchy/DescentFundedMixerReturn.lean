import OAI.Hierarchy.DescentFundedSetup
import OAI.Hierarchy.DescentFundedRosterInput

namespace OAI
/-! # Both computed trunk sources and the earlier printed root packets on one RAM -/
namespace Hierarchy.DescentFundedCensus.Setup
open DescentSIMDLookup DescentPackedZip DescentGL DescentGLPacked DescentColonies
open DescentGLPacked.BankImage DescentIssuedFallbackPanel DescentResetHostSize
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DescentFundedCensus.Setup) {w : ℕ}

theorem earlier {base : ℕ} (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w)
    (keys : key.Fits w base) (fits : ∀b,(old b).Fits w base) (space : s.roof base<2^w)
    {b H G M : ℕ} (e : Expr) (safe : e.Fits w base) (x : Fin H→Fin G→Cell b) (value : Source e x M m) :
    Source e x M (s.memory base old key m) :=by
  intro q
  exact (eval_below e _ m _ safe (fun a ha=>(s.any base old key m fits keys space).2.2 a (.inl ha))).trans (value q)

def lowData (oldValue : Fin s.blocks→Fin s.hosts→Fin s.oldGroups→Cell s.precision)
    (dim : 2^(s.high+s.low)=s.oldGroups*s.blocks) (cut : s.cut≤ s.high+s.low) (μ : DescentGL.Layout (s.high+s.low))
    (h : Fin s.hosts) (hi : Block s.cut) :=
  encode s.precision s.donors fun lo=>let z:=Fin.cast dim ((rearrange μ).symm (join cut hi lo))
    let ix:Fin s.oldGroups×Fin s.blocks:=finProdFinEquiv.symm z
    oldValue ix.2 h ix.1

theorem returned {base n r Q : ℕ} (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w)
    (keys : key.Fits w base) (fits : ∀b,(old b).Fits w base) (space : s.roof base<2^w)
    (μ : DescentGL.Layout (s.high+s.low)) (saved : m key.base=((DescentExterior.matrixCode μ).val:Word w))
    (dim : 2^(s.high+s.low)=s.oldGroups*s.blocks) (pitch : 2^s.low=s.gatherLanes*s.blocks)
    (cut : s.cut≤ s.high+s.low) (repack : s.outputLanes*s.donors=2^s.low)
    (po : 0<s.oldLanes) (pg : 0<s.gatherLanes) (pb : 0<s.blocks) (pp : 0<s.outputLanes)
    (oldValue : Fin s.blocks→Fin s.hosts→Fin s.oldGroups→Cell s.precision)
    (oldSize : ∀b,s.hosts*chunks s.oldGroups s.oldLanes≤(old b).size) (oldReads : ∀b,DescentPackedColony.Reads (old b) (oldValue b) s.oldLanes m)
    (signed : Fin (2*s.capacity)→Expr)
    (chips : Fin (2*s.capacity)→Fin s.hosts→Block s.cut→Fin s.donors→Cell (DescentSignedCableCodec.width s.degree s.capacity))
    (queued : ∀j,(signed j).Fits w base) (observed : ∀j,Source (signed j) (fun h g=>encode _ s.donors (chips j h g)) s.outputLanes m)
    (small : 2*s.capacity<2^s.precision)
    {sf bankBits : ℕ} (stencil : Expr) (presence : Fin Q→Expr) (bank : Bool → Code r×Option (Fin (2^n))→Expr)
    (panel : Fin s.hosts→Block s.cut→Cell sf) (active : Fin Q→Fin s.hosts→Block s.cut→Cell 1)
    (root : Bool → Code r×Option (Fin (2^n))→Fin s.hosts→Block s.cut→Cell bankBits)
    (earlyPanel : stencil.Fits w base) (earlierPresence : ∀j,(presence j).Fits w base) (earlierRoot : ∀z k,(bank z k).Fits w base)
    (panelValue : Source stencil panel s.outputLanes m) (isPresent : ∀j,Source (presence j) (active j) s.outputLanes m)
    (stored : ∀z k,Source (bank z k) (root z k) s.outputLanes m) :
    let m':=s.memory base old key m
    Source (.lookup (s.primary base) .row) (s.lowData oldValue dim cut μ) s.outputLanes m' ∧
    Source (s.secondary base signed) (fun h g=>encode s.precision s.donors
      (fun l=>(Arrivals.count chips h g l:ℕ))) s.outputLanes m' ∧ Source stencil panel s.outputLanes m' ∧
    (∀j,Source (presence j) (active j) s.outputLanes m') ∧ ∀z k,Source (bank z k) (root z k) s.outputLanes m' :=by
  intro m'
  have paid:=s.read base old key m keys fits space μ saved dim pitch cut repack po pg pb pp oldValue oldSize oldReads
  have tally:=s.secondary_read base old key m keys fits space signed chips queued observed small
  have stems:=s.order base
  have low:=s.primary_fit base (stems.2.2.2.trans_lt space)
  have lanesEq:=chunks_group (2^s.cut) s.outputLanes s.donors pp (Nat.two_pow_pos _)
  have co:2^s.cut*s.donors=2^(s.high+s.low):=by unfold donors;rw [←pow_add,Nat.add_sub_of_le cut]
  rw [co,repack,DescentGLPacked.chunk_count] at lanesEq
  have extent:s.hosts*chunks (2^s.cut) s.outputLanes≤(s.primary base).size:=by
    rw [←lanesEq]
    exact Nat.le_pow_clog (by decide) _
  refine ⟨source_column _ _ low m' _ extent paid,?_,s.earlier old key m keys fits space stencil earlyPanel panel panelValue,
    fun j=>s.earlier old key m keys fits space _ (earlierPresence j) _ (isPresent j),
    fun z k=>s.earlier old key m keys fits space _ (earlierRoot z k) _ (stored z k)⟩
  convert tally.2 using 2
  rename_i h
  funext g
  apply congrArg (encode s.precision s.donors)
  funext l
  exact Fin.ext (Fin.val_cast_of_lt ((Arrivals.count_le chips h g l).trans_lt small))

end
end Hierarchy.DescentFundedCensus.Setup

end OAI
