import OAI.Hierarchy.ProtocolRAMTurnEdgeData
import OAI.Hierarchy.TaggedWireCommodityGraphs
import OAI.Hierarchy.ProtocolRAMTurnRoleData
import OAI.Hierarchy.ProtocolRAMRetainedSource

namespace OAI
/-! # Named original starts and normalized endpoint words of paid terminal rows -/

noncomputable section
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open AdaptiveProbe ProbeStage CoreBoard WordSeats ReportSockets HistoryRoles WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (uni : Exclusive mark)
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))

local notation "P" => HistoryRoles.Public S h W k attempts
local notation "inj" => Equiv.injective (siteNumber h (2^W) k)
local notation "Sources" => ProtocolRAMTurnGeometry.Source edges h (2^W) k

/-- Normalizing either ordering of the two physical endpoints gives the
actual tail and head of the installed chord. This also covers already ordered sockets. -/
theorem printed_ends_of_pair (p : Bool → P) (e : Fin edges)
    (joins : let chord := filledChord B.actual pad e
      (HistoryRoles.name (HistoryRoles.site S (p false)) = chord.1.1 ∧
       HistoryRoles.name (HistoryRoles.site S (p true)) = chord.1.2) ∨
      (HistoryRoles.name (HistoryRoles.site S (p false)) = chord.1.2 ∧
       HistoryRoles.name (HistoryRoles.site S (p true)) = chord.1.1)) :
    ProtocolRAMTurnOperands.printed S true p false true = (ProtocolRAMTurnEdges.ends B inj pad e).1 ∧
    ProtocolRAMTurnOperands.printed S true p true true = (ProtocolRAMTurnEdges.ends B inj pad e).2 := by
  let chord := filledChord B.actual pad e
  have lo : chord.1.1 < chord.1.2 := chord.property
  change _ = chord.1.1.val ∧ _ = chord.1.2.val
  change (_ = chord.1.1 ∧ _ = chord.1.2) ∨ (_ = chord.1.2 ∧ _ = chord.1.1) at joins
  rcases joins with ⟨a,b⟩ | ⟨a,b⟩
  · simp [ProtocolRAMTurnOperands.printed, a, b, lo]
  · simp [ProtocolRAMTurnOperands.printed, a, b, not_lt_of_ge lo.le]

/-- The bought role endpoints are the two chord names, even if the catalogue
stores them in the opposite order from the physical terminal operator. -/
theorem paid_endpoint_pair (e : Fin edges) (id : Catalogue S π depth mark) (p : Bool → P)
    (aligned : filledChord B.actual pad e = HistoryRoles.sorted S π depth mark (.inl id))
    (ports : ∀ b, p b = .inl (HistoryRoles.paid S π depth mark uni (id,b))) :
    let chord := filledChord B.actual pad e
    (HistoryRoles.name (HistoryRoles.site S (p false)) = chord.1.1 ∧
     HistoryRoles.name (HistoryRoles.site S (p true)) = chord.1.2) ∨
    (HistoryRoles.name (HistoryRoles.site S (p false)) = chord.1.2 ∧
     HistoryRoles.name (HistoryRoles.site S (p true)) = chord.1.1) := by
  let a := actualEnds S π depth mark id
  have atSide (b : Bool) :
      HistoryRoles.name (HistoryRoles.site S (p b)) = HistoryRoles.name (Incident.choose a b) := by
    rw [ports]
    exact congrArg HistoryRoles.name (HistoryRoles.paid_site S π depth mark uni id b)
  let chord := orderedChord (HistoryRoles.name a.1) (HistoryRoles.name a.2)
    (HistoryRoles.name.injective.ne (actual_distinct S π depth mark id))
  have equal : filledChord B.actual pad e = chord := aligned
  dsimp only
  rw [equal, atSide, atSide]
  change (HistoryRoles.name a.1 = chord.1.1 ∧ HistoryRoles.name a.2 = chord.1.2) ∨
      (HistoryRoles.name a.1 = chord.1.2 ∧ HistoryRoles.name a.2 = chord.1.1)
  by_cases lo : HistoryRoles.name a.1 < HistoryRoles.name a.2
  · exact Or.inl (by simp [chord, orderedChord, lo])
  · exact Or.inr (by simp [chord, orderedChord, lo])

theorem paid_printed_ends (e : Fin edges) (id : Catalogue S π depth mark) (p : Bool → P)
    (aligned : filledChord B.actual pad e = HistoryRoles.sorted S π depth mark (.inl id))
    (ports : ∀ b, p b = .inl (HistoryRoles.paid S π depth mark uni (id,b))) :
    ProtocolRAMTurnOperands.printed S true p false true = (ProtocolRAMTurnEdges.ends B inj pad e).1 ∧
    ProtocolRAMTurnOperands.printed S true p true true = (ProtocolRAMTurnEdges.ends B inj pad e).2 :=
  printed_ends_of_pair S π B pad p e (paid_endpoint_pair S π depth mark uni B pad e id p aligned ports)

/-- The unsorted pair of genuine source sites. Fixed catalogue rows already
use their sorted chord, while goods and reserves keep their forward endpoints. -/
def originalEnd (src : Sources) (side : Bool) :=
  match src with
  | .inl e => (portGraph _).vertex (filledChord B.actual pad e) side
  | .inr (.inl i) => (commodityGraph π HistoryRoles.name).vertex i side
  | .inr (.inr c) => (catalystGraph HistoryRoles.name).vertex c side

theorem original_side (fixed : Fin edges → ℕ) (ident : {e // 0 < fixed e} → Catalogue S π depth mark)
    (pay : Fin edges → Bool → P)
    (aligned : ∀ e : {e // 0 < fixed e}, filledChord B.actual pad e.val=HistoryRoles.sorted S π depth mark (.inl (ident e)))
    (ports : ∀ (e : {e // 0 < fixed e}) b, pay e.val b = .inl (HistoryRoles.paid S π depth mark uni (ident e,b)))
    (src : Sources) (live : ProtocolRAMLiveTurnOrder.retain fixed src) (b : Bool) :
    HistoryRoles.name (HistoryRoles.site S (RoleProgram.publicRoleFor S π pay src b)) =
      originalEnd S π B pad src b := by
  rcases src with e | i | c
  · let row : {i // 0 < fixed i} := ⟨e,live⟩
    obtain ⟨left,right⟩ := paid_printed_ends S π depth mark uni B pad e (ident row) (pay e)
      (aligned row) (ports row)
    cases b
    · exact Fin.ext left
    · exact Fin.ext right
  · change HistoryRoles.name (HistoryRoles.goodsSite (HistoryRoles.goods π (i,b))) = _
    rw [HistoryRoles.goods_site]
    cases b <;> rfl
  · cases b <;> rfl

/-- The original first socket is the raw initial site visited by this source,
including payloads, altimeter commodities, and catalyst reserves. -/
theorem original_start (fixed : Fin edges → ℕ) (ident : {e // 0 < fixed e} → Catalogue S π depth mark)
    (pay : Fin edges → Bool → P)
    (aligned : ∀ e : {e // 0 < fixed e}, filledChord B.actual pad e.val=HistoryRoles.sorted S π depth mark (.inl (ident e)))
    (ports : ∀ (e : {e // 0 < fixed e}) b, pay e.val b = .inl (HistoryRoles.paid S π depth mark uni (ident e,b)))
    (src : Sources) (live : ProtocolRAMLiveTurnOrder.retain fixed src) :
    (HistoryRoles.name (HistoryRoles.site S (RoleProgram.publicRoleFor S π pay src false))).val =
      ProtocolRAMTurnEdges.visit B inj pad src 0 := by
  rcases src with e | i | c
  · let row : {i // 0 < fixed i} := ⟨e,live⟩
    exact (paid_printed_ends S π depth mark uni B pad e (ident row) (pay e) (aligned row) (ports row)).1
  · change (HistoryRoles.name (HistoryRoles.goodsSite (HistoryRoles.goods π (i,false)))).val =
      (HistoryRoles.name (WordSeats.site π (commodityTurn i 0))).val
    rw [HistoryRoles.goods_site, commodity_start]; rfl
  · rfl

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
