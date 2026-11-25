import OAI.Hierarchy.TaggedWireTerminalPorts
import OAI.Hierarchy.TaggedWireTimelineLast

namespace OAI
/-! # An active terminal old-row bit is read from its final chronological slot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ReportSockets WireTelescope CalendarTape
open ProtocolRAMEmit ProtocolRAM.Calendar
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked)
    (B : Mount (S:=S) π (name (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
    (fixed : Fin edges→ℕ) (stock : Goods h W k→ℕ) (reserved used : Catalysts h W k→ℕ)
    (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)
variable {M den w R : ℕ} {rows : Fin edges→ProtocolRAMEmit.Row}
    {G : Geometry (boardLayout h (2^W) k w R) M den rows} (H : MatrixReceipt B fixed stock reserved used G)
local notation "N" => siteLast h (2^W) k+1
local notation "layout" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "counts" => SettledMatrix.Layout.bits fixed stock reserved used
local notation "U" => B.actual.chordWidths fixed+(commodityGraph π name).chordWidths stock+
  (catalystGraph name).chordWidths (fun c=>reserved c-used c)
local notation "role" => ports S π depth marked unique fixed stock reserved used ident
variable (cap : Public S h W k attempts→ℕ)
variable (room : ∀p : NamedAperture.LiveEnd (SettledMatrix.Layout.bits fixed stock reserved used),
    SettledMatrix.Layout.bits fixed stock reserved used p.val.1 ≤
      cap (ports S π depth marked unique fixed stock reserved used ident p))

private theorem state_cast {K : ℕ} {A B : Widths K} (eq : A=B) (i : Fin K) (x : State A i) (b : SiteBit B i) :
    siteBits A i x (NamedAperture.transportAt eq.symm b)=siteBits B i (cast (congrArg (fun V=>State V i) eq) x) b := by
  subst B;rfl

private theorem read_transport {K : ℕ} {A B : Widths K} {T : Type} (eq : A=B)
    (placed : (Σi,SiteBit A i) ↪ T) (reported : (Σi,SiteBit B i) ↪ T)
    (packing : placed=(NamedAperture.transport eq).toEmbedding.trans reported)
    {i : Fin K} (bit : SiteBit B i) {t : T} (hit : reported ⟨i,bit⟩=t) :
    placed ⟨i,NamedAperture.transportAt eq.symm bit⟩=t := by
  subst B
  subst placed
  exact hit

set_option maxHeartbeats 1000000 in
/-- At the last time in the same zero-padded tape, the digit of the publicly
numbered old port is exactly the physical bit consumed by the settled matrix. -/
theorem prior_bit {X : Type} (slot : Event→Slot X) (wire : X→Widths N)
    (cells : ∀x,(Σs,SiteBit (wire x) s) ↪ (Σu,Fin (cap u))) (es : List Event)
    (x : X) (j : Path slot es x) (choices : SiteChoices slot wire es x j)
    (width : wire (terminal slot es x j)=U)
    (packing : cells (terminal slot es x j) =
      (NamedAperture.transport width).toEmbedding.trans (place S π depth marked unique B pad fixed stock reserved used ident H cap room))
    {s : Fin N} (p : (bitGraph (rowGraph (layout).family) counts).Port s) :
    let key : NamedAperture.LiveEnd counts:=⟨(p.1.1.1,p.1.2),Nat.zero_lt_of_lt p.1.1.2.isLt⟩
    let physical : Σu,Fin (cap u):=⟨role key,p.1.1.2.castLE (room key)⟩
    let old:=H.old_width (siteNumber h (2^W) k).injective pad
    let z:=cast (congrArg (fun V=>State V s) width) (lastState slot wire s es x j (choices s))
    placedBits slot wire es x j (timelineFin slot wire cells es x j) choices
        (bodyIndex es (Fin.last es.length) physical)=
      rowBits (layout).family counts (cast (congrArg (fun V=>State V s) old.symm) z) p := by
  intro key physical old z
  let measured:=NamedAperture.transportAt old (NamedAperture.atPort (layout).family counts p)
  let prior:=NamedAperture.transportAt width.symm measured
  let reported := place S π depth marked unique B pad fixed stock reserved used ident H cap room
  have address : cells (terminal slot es x j) ⟨s,prior⟩=physical :=
    read_transport width (cells (terminal slot es x j)) reported packing measured
      (read S π depth marked unique B pad fixed stock reserved used ident H cap room p)
  let lastCell := fun t : Σu,Fin (cap u) =>
    placedBits slot wire es x j (timelineFin slot wire cells es x j) choices
      (bodyIndex es (Fin.last es.length) t)
  refine (congrArg lastCell address.symm).trans
    ((last_body slot wire cells es x j choices s prior).trans ?_)
  exact (state_cast width s _ measured).trans
    (NamedAperture.rowBits_transport (layout).family counts old z p).symm

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
end

end OAI
