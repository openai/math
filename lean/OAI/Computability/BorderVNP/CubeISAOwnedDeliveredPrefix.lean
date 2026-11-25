import OAI.Computability.BorderVNP.CubeISAOwnedDeliveredView
import OAI.Computability.BorderVNP.CubeISAOwnedRawPacketStage

/-! # The raw prefix observed at an actual unvalidated receiver view -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRowSources

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {a q blocks K h : ℕ} {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ}
variable {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- The common raw prefix of a genuinely transmitted row is resident in either
directed owner view at the actual current cursor. Only the advertised frame and
the fixed prefix width are used, so this also applies to malformed cut lengths
and to prefixes which the selector reader will reject. -/
theorem SharedWriters.raw_prefix (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) (p : Symbols q) (high : Bool)
    (power : ℕ) (m : Memory w) :
    let u := if high then group p.val.2 else group p.val.1
    let l := TeamRowPrepare.Layout.ofShared g u.val
    let k := key (oriented p high)
    let width := rowSelectorBits a q blocks K h decl.1 (Sym2.mk p.val.1 p.val.2)
    let raw := (f.receivedRows g group p).take width
    (∀ j ∈ source l power a, m j = (H u).history.val.2.2 j) →
      raw.length = 2*blocks*(q.choose 2)^a*Tally.selectorWidth a K h ∧
      Resident (source l power a) m (l.view k) raw := by
  intro u l k width raw previous
  let base := if high then g.view p.val.2 p.val.1 else g.view p.val.1 p.val.2
  obtain ⟨_,_,size,lower,upper⟩ := writer.declaredRows frame p
  have resident : Resident (pairRegion g) (H u).history.val.2.2 base (f.receivedRows g group p) := by
    cases high
    · exact lower
    · exact upper
  have ptr : l.view k = base := by
    rw [TeamRowPrepare.Layout.ofShared_view,frame.groups,(key_digits (oriented p high)).1,(key_digits (oriented p high)).2]
    cases high <;> rfl
  have region : Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d)) = pairRegion g := by
    simp only [l,TeamRowPrepare.Layout.ofShared,pairRegion,pow_two]
  have widthFit : width ≤ (f.receivedRows g group p).length := size ▸ Nat.le_add_right ..
  have spelling : raw.length = width := by simp only [raw,List.length_take,Nat.min_eq_left widthFit]
  have lifted : Resident (source l power a) (H u).history.val.2.2 (l.view k) (f.receivedRows g group p) :=
    resident_views (region ▸ ptr ▸ resident)
  refine ⟨spelling.trans ?_,?_⟩
  · rw [show width = _ from Physical.Owned.strict_rowSelectorBits K h decl.1 p]
    simp [Tally.selectorWidth,VPVNP.MotifWidths.selectorBits,Selector]
  · simpa only [rawChunk,List.drop_zero,Nat.add_zero,raw] using
      ((lifted.congr previous).chunk 0 width (Nat.zero_le _))

end TeamContraction

end BorderVNP
end Computability
end OAI
