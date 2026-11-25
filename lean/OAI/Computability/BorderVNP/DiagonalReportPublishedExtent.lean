import OAI.Computability.BorderVNP.FiniteEvaluatorReportPublishedWidths
import OAI.Computability.BorderVNP.PackedRoutingOwnedArrays

/-! # The two report widths after private placement and demand publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open GeometryFrameEncoding ParseBatchSort DiagonalResidueRAM

/-- The complete tail after the private placement pairs survives the two
native writers. This includes every live pair, every private cell extent and
the word that points to the original site inside that cell. -/
theorem published_after_private_pairs {D : Directory.Layout} {frame origin cables cells next gap w : ℕ}
    (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
    (place : (privateLayout frame origin cables cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (a : ℕ) (above : (bases origin cables cells D.entries).livePairs ≤ a) :
    readings (Directory.ISA.publish placed frame next (D.directory pp lp)) a=readings profile a := by
  dsimp only [bases] at above
  have packed := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  have h := place.outside a (fun j hj => by dsimp only [privateLayout,bases]; omega)
    (.inr (by dsimp only [privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]; omega))
  exact (congrArg Fin.val (CableTriples.published_outside placed frame next (D.directory pp lp) a
    (by omega) (.inr (by omega)))).trans h

/-- The first appended column at a cell retains its entire private extent. -/
theorem published_private_extent {D : Directory.Layout} {frame origin cables cells next gap w ports : ℕ}
    (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
    (place : (privateLayout frame origin cables cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin) (c : Fin cells) :
    let a := (bases origin cables cells D.entries).livePairs+2*ports+c.val
    readings (Directory.ISA.publish placed frame next (D.directory pp lp)) a=readings profile a := by
  intro a
  exact published_after_private_pairs pp lp place low reserve a (by dsimp only [a]; omega)

variable {dim sites cables ports cells cb lb bits w frame origin next gap o : ℕ}
    {P σ : Type*} [Fintype P] [Fintype σ] {sizes : P → ℕ} (N : Network dim P sizes)
    (cell : N.Site → Fin cells) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin sites)
    (edgeID : N.Edge ↪ Fin cables) (portID : P ↪ Fin ports) (F : Fields sites cables ports cells cb lb bits σ)
    {x : σ → Bool} (D : Directory.Layout) (original : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
local notation "table" => bases origin cables cells D.entries
local notation3 (prettyPrint := false) "published" => readings (Directory.ISA.publish placed frame next (D.directory pp lp))

/-- The columns used by the report preparation are the supplied size and
the sum of the guessed wires and the private program sizes on this exact
network, including empty cells. -/
theorem Image.published_reportWidths
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings profile))
    (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (place : (privateLayout frame origin cables cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (rest : Frame σ (Outputs o bits)) (width : bits ≤ w)
    (words : ∀ i : Fin ((cells+(D.entries+cells))+o),
      profile (origin+cables*3+count cables cells D.entries (D.teams*D.sites)+i.val)=
        word w (value fun j => (withPrivateViews F (siteID ∘ original) rest).eval x (.inl (i,j))))
    (c : Fin cells) :
    published ((table).ends+2*cables+c.val)=suppliedSize N cell c ∧
      published ((table).livePairs+2*(D.teams*D.sites)+c.val)=guessedSize N cell c+siteSize N cell c aux := by
  refine ⟨image.published_supplied N cell aux siteID edgeID portID F D original live pp lp net codes fit place low reserve c,
    (published_private_extent pp lp place low reserve c).trans ?_⟩
  exact (owned_words N cell aux siteID edgeID portID F net fit original rest origin profile width words).1 c

/-- At each originally present site ordinal, the published pointer is the
actual start of that site's private program bank in its receiving cell. -/
theorem published_original_siteBase
    (net : Represents N cell aux siteID edgeID portID F x)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (place : (privateLayout frame origin cables cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (rest : Frame σ (Outputs o bits)) (width : bits ≤ w)
    (words : ∀ i : Fin ((cells+(D.entries+cells))+o),
      profile (origin+cables*3+count cables cells D.entries (D.teams*D.sites)+i.val)=
        word w (value fun j => (withPrivateViews F (siteID ∘ original) rest).eval x (.inl (i,j))))
    (i : Fin D.entries) :
    published ((table).livePairs+2*(D.teams*D.sites)+cells+i.val)=
      siteBase N cell (cell (original i)) siteID aux ⟨original i,rfl⟩ := by
  exact (published_after_private_pairs pp lp place low reserve _ (by omega)).trans
    ((owned_words N cell aux siteID edgeID portID F net fit original rest origin profile width words).2.1 i)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
