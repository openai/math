import OAI.Hierarchy.ProbeFixedCatalystBirth

namespace OAI
/-! # The three original outer socket banks in the physical calendar arena -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit
open BoughtSockets CatalogueRows PurchaseFrozen
open scoped Classical Fin.CommRing

/-- The two archived row lookup banks occupy a whole binary span, including
the padding beyond the last actual row. The priced area past the verdict
contains a further row column and a nonempty pad. -/
theorem Format.paddedSocketColumns {z d k q g : ℕ} (f : Format z d k q g) :
    f.board.purchaseOut+ProtocolRAMPurchaseSampler.span f.market.rows≤f.pricedArea.stop ∧
    f.board.boughtFields 6+ProtocolRAMPurchaseSampler.span f.market.rows≤f.pricedArea.stop := by
  have afterColumn (i : ℕ) (small : i<17) :
      PostLayout.column f.maskStart f.indexBits f.market.rows i+f.market.rows≤f.board.verdict := by
    change PostLayout.column _ _ _ i+f.market.rows≤
      PostLayout.column f.maskStart f.indexBits f.market.rows (17+3*g+f.checkedBoard.batch.quotes.length)
    have bound:=Nat.mul_le_mul_right f.market.rows
      (show i+1≤17+3*g+f.checkedBoard.batch.quotes.length by omega)
    rw [Nat.succ_mul] at bound
    unfold PostLayout.column
    omega
  have tail : f.pricedArea.start+f.pricedArea.pad+f.pricedArea.rows≤f.pricedArea.stop := by
    unfold Area.stop Area.output Area.excess Area.clip Area.src Area.broadcast Area.direct
    omega
  change f.board.verdict+1+f.occurrences+f.pricedArea.pad+f.market.rows≤f.pricedArea.stop at tail
  have pad : 0<f.pricedArea.pad := Nat.two_pow_pos _
  have cap:=ProtocolRAMPurchaseSampler.span_le f.market.rows
  have kept : f.board.purchaseOut+f.market.rows≤f.board.verdict := afterColumn 1 (by decide)
  have menu : f.board.boughtFields 6+f.market.rows≤f.board.verdict := afterColumn 16 (by decide)
  constructor <;> omega

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- The joined catalogue reads the original paid shelf, kept flag and menu
code. Each real outer event allocates all three padded banks inside its slab. -/
theorem catalyst_original_socket_bounds (P : v.Placement) (z width phase trial : ℕ)
    (occurs : Event.attempt (.outer phase trial)∈events v.mesh) :
    let s:=v.nativeBoards P z width
    let f:=v.nativeFormats P z width (.outer phase trial)
    let sh:=(s.outer phase trial).market.shelf
    let cap:=ProtocolRAMPurchaseSampler.span (count z (2^v.W) k*paths z v.sampler.degree v.depth)
    let stop:=(v.privateArena P z width).endAddress v.mesh
    sh.firstBase+count z (2^v.W) k*blockSize z (2^v.W) v.sampler.degree v.depth ≤ stop ∧
    f.board.purchaseOut+cap ≤ stop ∧ f.board.boughtFields 6+cap ≤ stop := by
  intro s f sh cap stop
  let e:=Attempt.outer phase trial
  let A:=v.privateArena P z width
  have inside:=A.within v.mesh (.attempt e) occurs
  have flags:= (v.catalyst_birth_room P z width e).2.2
  have shelf : sh.firstBase+count z (2^v.W) k*blockSize z (2^v.W) v.sampler.degree v.depth≤
      f.market.flags := Nat.le_add_right _ _
  have extent : f.market.rows=count z (2^v.W) k*paths z v.sampler.degree v.depth :=
    StripChart.candidate_count F v.mesh A P.joint.initial s e
  have columns:=f.paddedSocketColumns
  rw [extent] at columns
  have ending: f.pricedArea.stop ≤ stop := (v.attempt_room P z width e).trans inside
  exact ⟨shelf.trans ((Nat.le_add_right _ _).trans (flags.trans inside)),
    columns.1.trans ending,columns.2.trans ending⟩

theorem catalyst_original_stage_bounds (P : v.Placement) (z width phase trial : ℕ)
    (occurs : Event.attempt (.outer phase trial)∈events v.mesh) (i : Key z (2^v.W) k) :
    let sh:=((v.nativeBoards P z width).outer phase trial).market.shelf
    (sh.L v.sampler v.depth i).endAddress≤(v.privateArena P z width).endAddress v.mesh := by
  intro sh
  exact (sh.end_le v.sampler v.depth i Nat.one_le_two_pow).trans
    ((sh.final_after v.sampler v.depth i).trans (v.catalyst_original_socket_bounds P z width phase trial occurs).1)


end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar

end
end OAI
