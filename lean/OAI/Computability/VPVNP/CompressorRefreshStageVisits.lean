import OAI.Computability.VPVNP.CompressorRefreshScheduledRuns
import OAI.Computability.VPVNP.CompressorPhaseVisits

/-!
# Multiplicities of the actual degree-refresh recipes

The flat scan of each recipe has exactly its interval's number of calls.
The expander ROM has one call per hardwired edge. The final base scan
visits only lane zero. These counts match the charged visit scopes in
the online directory budget.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Scheduled

open BurstRAM Schedule Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open LevelRecipe NewSlots Allocation PhaseVisits
open scoped Fin.CommRing

variable {w a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (c : DyadicRefreshChoice X E hdH conn F)
  (ties : Fin t ≃ Tie (2^a)) (old : IncidenceDirectory w) (start stride : ℕ)

local notation "sh" => shape (t := t) E hdH conn F stride
local notation "J" => Stage sh

/-- The integral cursor difference; only the ROM starts from a nonzero edge ordinal. -/
def visits (j : J) := j.limit X start - j.first

/-- One worker row in the flat refresh calendar. -/
def phase {s : LevelRecipe.Shape} : Stage s → PhaseVisits.Phase
  | .gather | .offsets => ⟨.oldSlots,1⟩
  | .bundles | .slot _ => ⟨.oldSites,1⟩
  | .demand _ | .term => ⟨.motifs,1⟩
  | .supply => ⟨.oldSites,s.dH⟩
  | .rom _ => ⟨.once,1⟩
  | .base => ⟨.oldBase,s.ports*s.degree⟩

theorem tapes_length (j : J) : (tapes (w := w) X E hdH conn F c start stride j).length =
    visits X E hdH conn F start stride j := by
  cases j <;> simp [tapes,visits,Stage.limit,Stage.first,Allocation.plan]

theorem source_calls {cap : ℕ} {j : J} {m : Memory w} {rs : List (Report w)}
    (run : Source X E hdH conn F hd c ties old start stride cap j m rs) :
    rs.length = visits X E hdH conn F start stride j :=
  (by simpa [branchPaths] using congrArg List.length ((runSegment_iff ..).mp run).2.2 :
    rs.length = (tapes (w := w) X E hdH conn F c start stride j).length).trans
    (tapes_length X E hdH conn F c start stride j)

theorem source_packets (cap : ℕ) (L : Allocation.PrepareLayout X old a₀ dH t stride start)
    {m : Memory w} {rs : List (Report w)} (run : Build.Run X E hdH conn F hD hd c ties old start stride cap L m rs) :
    ∃ ps : List (SourceWalk.Packet J w), ps.map SourceWalk.Packet.stage = LevelRecipe.order sh ∧
      ps.flatMap SourceWalk.Packet.reports = rs ∧
      SourceWalk.Chronological (Source X E hdH conn F hd c ties old start stride cap) m ps ∧
      rs.length = ((LevelRecipe.order sh).map (visits X E hdH conn F start stride)).sum := by
  have walk := sources X E hdH conn F hD hd c ties old start stride cap L m rs run
  obtain ⟨ps,stages,data,chron⟩ := walk.packets
  exact ⟨ps,stages,data,chron,walk.report_count _ (fun _ _ _ h ↦ source_calls X E hdH conn F hd c ties old start stride h)⟩

variable {S : BlockSchedule k} {B : S.Templates} {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}

/-- The certificate attaches an actual refresh-state source row to its object
kind and visit multiplicity, using the original pass's selected term. -/
theorem visits_eq_scope {g : ℕ} (X : State S.portExponent (S.portExponent+g))
    (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
    (sel : List Bool) (capacity start stride : ℕ) {ties : ℕ}
    (j : Stage (shape (t := ties) S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh stride)) :
    let origin := PassOrigin.refresh (B := B) (f := f) (hf := hf) X
    let v : SelectedLevel B f hf := ⟨_,_,_,_,X,_,origin,c,sel⟩
    visits X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh start stride j =
      (phase j).scope.count capacity v * (phase j).perObject := by
  intro origin v
  have hp := PortRefresh.bundleCount_positions X (IncidenceDirectory.baseOrder X)
  cases j <;> simp only [visits,Stage.limit,Stage.first,phase,Scope.count,SelectedLevel.oldSlots,
    PassOrigin.motifCount,origin,v,Nat.sub_zero,Nat.mul_one,Nat.add_sub_cancel_left,
    Allocation.plan,Allocation.Plan.segments,shape,LevelRecipe.Shape.ports,LevelRecipe.Shape.degree]
  all_goals first | exact hp | rw [← hp] | ring

end CompressorRecords.PortRefresh.Scheduled

end VPVNP
end Computability
end OAI
