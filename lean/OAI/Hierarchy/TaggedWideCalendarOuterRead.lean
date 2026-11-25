import OAI.Hierarchy.TaggedWideCalendarDateWords
import OAI.Hierarchy.TaggedWireShelfReads
import OAI.Hierarchy.TaggedWideCalendarDatedState
import OAI.Hierarchy.TaggedWideBranchEndpointPlacement

namespace OAI
/-! # The named party data words on the original adjacent calendar sheets -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged Tagged.WideStack Tagged.WideControlJoin WireTelescope WireTelescope.CalendarTape
open ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
set_option quotPrecheck false

variable {X R D Ex Se : Type} [Fintype R] [Fintype D] [Fintype Ex] [Fintype Se] {K degree cap : ℕ}
    (slot : Event→Slot X) (shape : X→Widths K) (es : List Event) (start : X) (path : Path slot es start)
    (room : R→ℕ) (socket : R↪Fin (K*degree))
    (cells : ∀x,(Σs,SiteBit (shape x) s)↪((r:R)×Fin (room r)))
    (z : SiteChoices slot shape es start path)
local notation "allBits" => placedBits slot shape es start path (timelineFin slot shape cells es start path) z
variable (wire : Fin ((es.length+1)*Fintype.card ((r:R)×Fin (room r)))→D) (j : Fin es.length) (s : Fin K) (side : Bool)
local notation "date" => if side then j.succ else j.castSucc
local notation "T" => boundaryState slot es start path date
local notation "state" => datedState slot shape s es start path date (z s)
variable (G : Gate) (ex : Ex→Bool) (sel : Se→Bool) (data : D→Bool) (out : Memory G.W)
local notation "seen" => Sum.elim ex (Sum.elim sel (Sum.elim data (G.terminal out)))
local notation "words" => outerWord (Ex:=Ex) (Sel:=Se) (cap:=cap) G es room socket wire j s side

omit [Fintype D] [Fintype Ex] [Fintype Se] in
/-- Read a real native row, including its actual same-chord prefix shift in
the mathematical party state. The location is a single named coordinate on
the original paid sheet, also for repeated and parallel physical chords. -/
theorem outer_state_read (history : ∀a,data (wire a)=allBits a)
    (u : SiteBit (shape T) s) (r : R) (q : Fin degree) (b : Fin (room r))
    (selected : cells T ⟨s,u⟩=⟨r,b⟩) (atSite : socket r=finProdFinEquiv (s,q)) (fits : b.val<cap) :
    Sum.elim seen id (words q ⟨b.val,fits⟩)=siteBits (shape T) s state u := by
  rw [outerWord_at (cap:=cap) G es room socket wire j s ex sel data out side q r atSite ⟨b.val,fits⟩ b.isLt,history]
  have read:=dated_body slot shape cells es start path z date s u
  rw [selected] at read
  exact read

omit [Fintype D] [Fintype Ex] [Fintype Se] in
/-- The active coordinate carries its actual party bit. -/
theorem outer_state_digit (history : ∀a,data (wire a)=allBits a)
    (u : SiteBit (shape T) s) (r : R) (q : Fin degree) (b : Fin (room r))
    (selected : cells T ⟨s,u⟩=⟨r,b⟩) (atSite : socket r=finProdFinEquiv (s,q)) (fits : b.val<cap) :
    Sum.elim seen id (words q ⟨b.val,fits⟩)=(state u.1).val.testBit u.2.val :=by
  exact (outer_state_read slot shape es start path room socket cells z wire j s side G ex sel data out
    history u r q b selected atSite fits).trans (Computability.VPVNP.LiveHeader.testBit_wordBits (state u.1) u.2).symm

omit [Fintype D] [Fintype Ex] [Fintype Se] in
/-- Combine the genuine boundary numbering with the native earlier-row
prefix on the original physical chord. This is also the source read for
an expanded role bank when two paid rows have the same neighbor. -/
theorem outer_original_row {n : ℕ} (ends : Fin n→Chord K) (qty : Fin n→ℕ)
    (port : Fin n×Bool↪R) (fit : ∀i b,qty i≤room (port (i,b)))
    (shapeAt : AdaptiveProbe.installedWidths ends qty=shape T)
    (numbered : cells T=(NamedAperture.transport shapeAt).symm.toEmbedding.trans
      (NamedAperture.place ends qty port room fit))
    (history : ∀a,data (wire a)=allBits a) (p : (bitGraph (rowGraph ends) qty).Port s)
    (q : Fin degree) (atSite : socket (port (p.1.1.1,p.1.2))=finProdFinEquiv (s,q))
    (fits : p.1.1.2.val<cap) :
    let original:=cast (congrArg (fun U=>State U s) shapeAt.symm) state
    Sum.elim seen id (words q ⟨p.1.1.2.val,fits⟩)=
      (original (sourcePort ends qty p)).val.testBit
        (TaggedShorterCommonScan.earlier (NamedAperture.key ends) qty p.1.1.1.val
          (NamedAperture.key ends p.1.1.1)+p.1.1.2.val) :=by
  intro original
  let u:=NamedAperture.transportAt shapeAt (NamedAperture.atPort ends qty p)
  have selected : cells T ⟨s,u⟩=⟨port (p.1.1.1,p.1.2),p.1.1.2.castLE (fit _ _)⟩ :=by
    rw [numbered,←NamedAperture.transport_pair shapeAt]
    simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
    exact NamedAperture.port_read ends qty port room fit p
  exact (outer_state_read slot shape es start path room socket cells z wire j s side G ex sel data out
    history u _ q _ selected atSite fits).trans
    ((NamedAperture.rowBits_transport ends qty shapeAt state p).symm.trans
      (NamedAperture.rowBit_prefix ends qty original p))

end Hierarchy.ProbeStage.CoreBoard.LedgerStep

namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction
open scoped Classical
variable {F T E H P D : Type} [CommSemiring F] [Fintype T] [Fintype E] [Fintype H] [Fintype P]
    (B : T→Board F) (room : E→ℕ) (ord : Pin B room H P≃D)
    (z : ∀i,(B i).Slots) (y : PrivatePorts room) (history : H→Bool) (plane : P→Bool)

omit [Fintype T] [Fintype E] [Fintype H] [Fintype P] in
theorem written_time (t : H) :
    (write B room z y history plane ∘ ord.symm) (ord (.inr (.inr (.inl t))))=history t :=by
  rw [Function.comp_apply,Equiv.symm_apply_apply]
  rfl
end Hierarchy.Tagged.WideStack.Leaf

namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open CalendarTape
open scoped Classical
variable {K n : ℕ} {R : Type} (ends : Fin n→Chord K) (qty : Fin n→ℕ)
    (port : Fin n×Bool↪R) (room : R→ℕ) (fits : ∀i b,qty i≤room (port (i,b)))

/-- Width rebasing on the real branch keeps each occupied original row and
each bit of its native width word at exactly its chronological address. -/
theorem at_word {B : Widths K} (shape : AdaptiveProbe.installedWidths ends qty=B)
    (cells : (Σs,SiteBit B s)↪((r:R)×Fin (room r)))
    (numbered : cells=(transport shape).symm.toEmbedding.trans (place ends qty port room fits))
    (r : Bundle qty) (b : Bool) :
    cells ((transport shape) (halfBits ends qty (r,b)))=⟨port (r.1,b),r.2.castLE (fits r.1 b)⟩ :=by
  rw [numbered]
  exact (congrArg (place ends qty port room fits) ((transport shape).symm_apply_apply _)).trans
    (read ends qty port room fits r b)

end Hierarchy.WireTelescope.NamedAperture
end

end OAI
