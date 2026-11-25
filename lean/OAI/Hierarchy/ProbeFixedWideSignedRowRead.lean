import OAI.Hierarchy.ProbeFixedWideSignedRow
import OAI.Hierarchy.ProbeFixedPartyIndex
import OAI.Hierarchy.TaggedWideCalendarPartyRead

namespace OAI
/-! # Native reads of the retained local packet under the paired gathers -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged Tagged.WideControlJoin Tagged.WideStack AdaptiveProbe ProbeStage
open WireTelescope WireTelescope.PassMatrix WideCPU SiteScatter Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 720000
variable {F Ex Sel Data I : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype Data]
    {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h w unitCost : ℕ) (a : Attempt) (G : Gate)
local notation "pinsType" => SitePins Ex Sel Data G
local notation "degree" => v.widePacketDegree
local notation "cap" => v.wideNeighborCap w unitCost
local notation "formats" => v.signedPartyCount h a
variable {T : ℕ} (g : Dated T) (work : ℕ) (j : Fin T) (s : Fin g.sites)
    (words : Bool → Fin v.widePacketDegree → Fin (v.wideNeighborCap w unitCost) → SitePins Ex Sel Data G ⊕ Bool)
    (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
    (dense : ∀i:Fin G.u,(G.addr i).val=i.val)
    (inside : ∀ f : SiteControls.Field v.widePacketDegree, controlAddress g work j s f < G.u)
    (small : v.wideNeighborDigits w unitCost ≤ G.W+1)
local notation "seen" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))
local notation "ctrl" f:arg => (out (controlAddress (deg:=degree) g work j s f)).val
variable {sizes : Bool→I→ℕ} (parts : ∀b,PassiveWindow.Parts I (Fin v.widePacketDegree) (v.wideNeighborCap w unitCost) (sizes b))
    (state : Bool→I→ℕ→Bool)
local notation "bank" b:arg => Function.uncurry (ChordAperture.canonical (parts b) (state b))
local notation "pins" => Sum.elim (Sum.elim seen (bank false)) (bank true)
local notation "read" => ballotWord (Ex:=Ex) (Sel:=Sel) (D:=Data) G g work j s

include dense

theorem signedCandidate_read (index : Fin formats)
    (fits : ∀b q,sizes b q≤cap) (room : ∀b q,ChordAperture.room (parts b) q<cap)
    (length : ∀b i q,ctrl (.inl (b,.inl (i,q)))=(ChordAperture.sizeAt (parts b) i q).val)
    (head : ∀b i endp,ctrl (.inl (b,.inr (.inl (i,endp))))=(ChordAperture.head (parts b) i endp).val)
    (extent : ∀b q,ctrl (.inl (b,.inr (.inr q)))=ChordAperture.room (parts b) q)
    (live : ∀b i p,(parts b).owner i=some p→∀u:Fin ((parts b).width i),
      Sum.elim seen id (words b i (u.castLE ((parts b).within i)))=state b p ((parts b).base i+u.val)) :
    TypedWiring.value (P:=pinsType) (v.signedRowCandidate h w unitCost a G g work j s words inside small index) seen=
      TypedWiring.value (P:=Gathered pinsType degree cap) (v.signedParty (V:=pinsType) h w a cap (v.partyRoleBits h) (v.partyLaneBits h w a unitCost)
        v.partyKeyBits read index) pins :=
  spillGather_value G g work j s out ext sel data dense inside words small _ parts state fits le_rfl
    room length head extent live

/-- The native original atom index and its actual participant select precisely
the same ordered packet's physical circuit on the canonical old and new words. -/
theorem signedParty_read (atom : v.widePacketMenuIndex h a) (party : Fin (v.wideBallotParties h a))
    (fits : ∀b q,sizes b q≤cap) (room : ∀b q,ChordAperture.room (parts b) q<cap)
    (length : ∀b i q,ctrl (.inl (b,.inl (i,q)))=(ChordAperture.sizeAt (parts b) i q).val)
    (head : ∀b i endp,ctrl (.inl (b,.inr (.inl (i,endp))))=(ChordAperture.head (parts b) i endp).val)
    (extent : ∀b q,ctrl (.inl (b,.inr (.inr q)))=ChordAperture.room (parts b) q)
    (live : ∀b i p,(parts b).owner i=some p→∀u:Fin ((parts b).width i),
      Sum.elim seen id (words b i (u.castLE ((parts b).within i)))=state b p ((parts b).base i+u.val)) :
    TypedWiring.value (P:=pinsType) (v.signedRowCandidate h w unitCost a G g work j s words inside small (v.partyIndex h a atom party)) seen=
      TypedWiring.value (P:=Gathered pinsType degree cap) (v.signedPartyAt (V:=pinsType) h w a cap (v.partyRoleBits h) (v.partyLaneBits h w a unitCost)
        v.partyKeyBits read atom party) pins :=by
  rw [v.signedCandidate_read h w unitCost a G g work j s words out ext sel data dense inside small parts state _
    fits room length head extent live,v.signedParty_at]

open private rowBlock from OAI.Hierarchy.TaggedWideCalendarDateRead
section SignedMatrix
variable {A : Type} {n columns : ℕ} {J : Fin n→Type} [∀i,Fintype (J i)]
    (demand : Fin n→Widths g.sites) (offer : ∀i,J i→Widths g.sites)
    (M : ∀i c,SiteMatrix (State (demand i)) (State (offer i c)) F) (rest : Widths g.sites) (c : ∀i,J i)
local notation "before" => ∑i,demand i
local notation "after" => ∑i,offer i (c i)
local notation "port" => (portGraph g.sites).Port s
variable (x : State (rest + ∑i,demand i) s) (y : State (rest + ∑i,offer i (c i)) s)
local notation "pass" => fun p:port=>rest p.val.1
local notation "old" => fun p:port=>before p.val.1
local notation "new" => fun p:port=>after p.val.1
variable (l : PassiveWindow.Parts ((portGraph g.sites).Port s) (Fin v.widePacketDegree) (v.wideNeighborCap w unitCost)
      (fun p => rest p.val.1 + (∑i,demand i) p.val.1))
    (r : PassiveWindow.Parts ((portGraph g.sites).Port s) (Fin v.widePacketDegree) (v.wideNeighborCap w unitCost)
      (fun p => rest p.val.1 + (∑i,offer i (c i)) p.val.1))
local notation "agree" i:arg q:arg => PassiveWindow.linked pass old new l r i q
local notation "rawState" => fun (b:Bool) (p:port) d=>if b then (y p).val.testBit d else (x p).val.testBit d
local notation "size" => fun (b:Bool) (p:port)=>if b then pass p+new p else pass p+old p
local notation "slices" => (fun b:Bool=>Bool.rec (motive:=fun b=>PassiveWindow.Parts port (Fin degree) cap (size b)) l r b)
local notation "canon" b:arg => Function.uncurry (ChordAperture.canonical (slices b) (rawState b))
local notation "tape" => Sum.elim (Sum.elim seen (canon false)) (canon true)
local notation "input" => rowBlock demand rest s x
local notation "output" => rowBlock (fun i=>offer i (c i)) rest s y
variable (place : A↪Fin g.sites) (ballot : A→Fin n)
    (atom : A→v.widePacketMenuIndex h a) (party : A→Fin (v.wideBallotParties h a))
local notation "kind" => fun t=>v.partyIndex h a (atom t) (party t)
variable {tbits : ℕ} (mode : ballotAddress g work j s 0<G.u) (tagFit : v.signedPartyCount h a+1≤2^tbits) (tagSmall : tbits≤G.W+1)

/-- Each actual elected local party is evaluated after native selection and
canonical gathering. Other original rows contribute exactly their identity
entries. The carried interval is checked by the fixed passive comparator. -/
theorem signedRow_value (word : A→Fin columns→Word G.W) (column : Fin columns)
    (selected : ∀t,(word t column).val=(kind t).val+1) (posted : out (ballotAddress g work j s 0)=table place word s column)
    (fits : ∀b p,size b p≤cap) (rooms : ∀b q,ChordAperture.room (slices b) q<cap)
    (length : ∀b i q,ctrl (.inl (b,.inl (i,q)))=(ChordAperture.sizeAt (slices b) i q).val)
    (head : ∀b i endpoint,ctrl (.inl (b,.inr (.inl (i,endpoint))))=(ChordAperture.head (slices b) i endpoint).val)
    (extent : ∀b q,ctrl (.inl (b,.inr (.inr q)))=ChordAperture.room (slices b) q)
    (source : ∀i p,l.owner i=some p→∀u:Fin (l.width i),
      Sum.elim seen id (words false i (u.castLE (l.within i)))=(x p).val.testBit (l.base i+u.val))
    (target : ∀i p,r.owner i=some p→∀u:Fin (r.width i),
      Sum.elim seen id (words true i (u.castLE (r.within i)))=(y p).val.testBit (r.base i+u.val))
    (len : ∀i q,ctrl (.inr ((i,q),0))=(PassiveWindow.header cap (l.view old i) (r.view new q) (agree i q)).val)
    (start : ∀i q (b:Bool),ctrl (.inr ((i,q),if b then 2 else 1))=
      (PassiveWindow.heads cap (l.view old i) (r.view new q) b).val)
    (real : ∀t,place t=s→TypedWiring.value (P:=Gathered pinsType degree cap) (v.signedPartyAt (V:=pinsType) h w a cap (v.partyRoleBits h)
      (v.partyLaneBits h w a unitCost) v.partyKeyBits read (atom t) (party t)) tape=
        M (ballot t) (c (ballot t)) s (input (ballot t)) (output (ballot t)))
    (away : ∀i,(∀t,place t=s→ballot t≠i)→M i (c i) s (input i) (output i)=1) :
    TypedWiring.value (P:=pinsType) (v.signedRow h w unitCost a G g work j s words inside mode tagFit tagSmall small) seen=
      matrix M rest c s x y :=by
  apply datedProgram_value G g work j s out ext sel data dense inside demand offer M rest c x y l r words
    tagFit mode tagSmall _ place ballot kind word column selected posted source target len start _ away
  intro t atSite
  rw [v.signedParty_read h w unitCost a G g work j s words out ext sel data dense inside small
    slices rawState (atom t) (party t) fits rooms length head extent]
  · exact real t atSite
  · rintro (_|_) <;>first | exact source | exact target
end SignedMatrix

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
