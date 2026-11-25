import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentRootTableEvaluation

namespace OAI
/-! # Every installed reset root retains its true packed input and output -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local.Gather
open DescentSixParty.Chronology DescentPackedZip DescentSharedBookScan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "groups" => 2^c
local notation "slots" => H*chunks groups M
local notation "A" => RootTemplates.arena (a.headerEnd b) H groups M r n D
local notation "Page" => RootPage r (2^n)
variable (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n))
local notation "rid" => (rootIndex r (2^n) p).val
local notation "start" => b.atPage a.projectionEnd H groups M p
local notation "input" => b.target a.projectionEnd H groups M p
local notation "tbl" => (b.table p).2
local notation "act" => ((tbl).terms start H groups M input)

/-- The exceptional root runs its scalar rank program before assembling its gather.
A good root starts directly from the common mounted memory. -/
def rootInputState : Memory w := match p.2 with
  | .inl _ => a.preparedMid b space m
  | .inr _ => ProtocolRAM.image ((A).first rid) (A).counters (record (b.common a.projectionEnd H) H D (2^Ht) (Ht+2))
      (a.preparedMid b space m)

theorem gatheredImage (z : ℕ) (lo : (A).middle rid≤ z) (hi : z<(A).output rid+slots) :
    a.preparedImage b space m z=
      imageBank H groups M ((A).output rid) (act).menu
        (ProtocolRAM.image ((A).middle rid) slots (assembly (act).tables (tbl).reads) (a.rootInputState b space m p)) z := by
  rcases p with ⟨s,(⟨root,j⟩|root)⟩
  · apply a.prepared_root b space m (s,.inl (root,j)) z
    · exact (min_le_left ..).trans lo
    · exact hi.trans_le (le_max_right ..)
  · apply a.prepared_root b space m (s,.inr root) z
    · exact (min_le_right ..).trans ((min_le_left ..).trans lo)
    · exact hi.trans_le ((le_max_right ..).trans (le_max_right ..))

theorem rootInput_tables :
    ((tbl).literals start H groups M w).Resident (a.rootInputState b space m p) := by
  have loaded:=(b.installed a.projectionEnd H groups M (a.prefixImage space.toPrefixFits m) space.literals).2.2.2.2.1 p
  have head:=b.bounds a.projectionEnd H groups M w p
  have name:=(rootIndex r (2^n) p).isLt
  have prior : (tbl).stop start H groups M≤ a.headerEnd b:=
    head.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  cases kind:p.2 with
  | inl u=> simpa only [rootInputState,kind,RootBook.pageImage,preparedMid,headerImage] using loaded
  | inr u=>
    intro z lo hi
    have ceiling:=hi.trans_le prior
    have away:z<(A).first rid:=ceiling.trans_le (Nat.le_add_right ..)
    simp only [rootInputState,kind]
    apply (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl away)).trans
    exact loaded z lo hi

include space in
/-- Numeric checks for the previous data operands imply the gather and final
lookup fit the concrete root's two slots. The banks of the compiled binary gates
and of the final rotor/fallback lookup come from the dated book itself. -/
theorem prepared_root_bounds
    (prior : ∀i,((tbl).reads i).Fits w ((A).middle rid))
    (packed : M*max ((tbl).field*(b.table p).1) (tbl).outputBits≤ w/2) :
    Bounds (w:=w) (d:=(tbl).field) (M:=M) (act).tables (tbl).reads ((A).middle rid) := by
  have name:=(rootIndex r (2^n) p).isLt
  have printed: (tbl).stop start H groups M≤ a.headerEnd b:=
    (b.bounds a.projectionEnd H groups M w p).2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  have mid:a.headerEnd b≤(A).middle rid:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ((tbl).geometry_at start _ _ input rfl rfl (printed.trans mid) prior le_rfl (space.rows p).2 packed).1

/-- Full packed-word read at the gather's real intermediate address, simultaneously
with the final root output. This includes the last partially occupied word at each host. -/
theorem prepared_root_input (value : Fin H→Fin groups→Fin (b.table p).1→Cell (tbl).field)
    (bounds : Bounds (w:=w) (d:=(tbl).field) (M:=M) (act).tables (tbl).reads ((A).middle rid))
    (source : ∀i,Source ((tbl).reads i) (fun v g=> value v g i) M (a.rootInputState b space m p))
    (q : Row H groups M) :
    a.preparedImage b space m ((A).middle rid+(row H groups M q).val)=
      ((data (fun v g=> encode (tbl).field (b.table p).1 (value v g)) q).val:Word w) := by
  have address:=(row H groups M q).isLt
  have head:=b.bounds a.projectionEnd H groups M w p
  have name:=(rootIndex r (2^n) p).isLt
  have past : (tbl).stop start H groups M≤ a.headerEnd b:=
    head.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  have low: (A).middle rid+slots≤(A).output rid:=Nat.add_le_add_left (RootArena.le_span _) _
  have bound:(A).middle rid+(row H groups M q).val<(A).output rid:=(Nat.add_lt_add_left address _).trans_le low
  rw [a.gatheredImage b space m p _ (Nat.le_add_right ..) (bound.trans_le (Nat.le_add_right ..))]
  have tables:=(tbl).resident_at start input _ (past.trans_lt space.literals) (a.rootInput_tables b space m p)
  exact (tbl).middle_words start _ _ input _ value bounds tables.1 source low q

/-- A direct native operand for the saved input of any selected or absent root. -/
def gatheredOperand : Expr:=.lookup input .row

include space in
theorem gathered_fits : (a.gatheredOperand b p).Fits w (a.preparedEnd b) := by
  have ends:(A).output rid+RootArena.span slots=(A).first (rid+1):=RootArena.end_row ..
  have top:(A).first (rid+1)≤ a.preparedEnd b:=Nat.add_le_add_left (Nat.mul_le_mul_left _ (rootIndex r (2^n) p).isLt) _
  have run:=(space.rows p).2
  have banks:(A).middle rid+RootArena.span slots=(A).output rid:=rfl
  have cap:0< RootArena.span slots:=Nat.two_pow_pos _
  refine ⟨⟨cap,?_,?_⟩,trivial⟩
  · change RootArena.span slots<2^w
    change (A).output rid+slots<2^w at run
    omega
  · change (A).middle rid+RootArena.span slots≤ a.preparedEnd b
    omega

theorem gathered_source (value : Fin H→Fin groups→Fin (b.table p).1→Cell (tbl).field)
    (prior : ∀i,((tbl).reads i).Fits w ((A).middle rid))
    (packed : M*max ((tbl).field*(b.table p).1) (tbl).outputBits≤ w/2)
    (source : ∀i,Source ((tbl).reads i) (fun v g=> value v g i) M (a.rootInputState b space m p)) :
    Source (a.gatheredOperand b p) (fun v g=> encode (tbl).field (b.table p).1 (value v g)) M
      (a.preparedImage b space m) :=
  source_column input (a.preparedEnd b) (a.gathered_fits b space p).1 (a.preparedImage b space m) _ (RootArena.le_span _)
    (a.prepared_root_input b space m p value (a.prepared_root_bounds b space p prior packed) source)

/-- Output digit computed by the official public law of this very root and the same
arrived operand vector. -/
theorem prepared_root_value (value : Fin H→Fin groups→Fin (b.table p).1→Cell (tbl).field)
    (prior : ∀i,((tbl).reads i).Fits w ((A).middle rid))
    (packed : M*max ((tbl).field*(b.table p).1) (tbl).outputBits≤ w/2)
    (source : ∀i,Source ((tbl).reads i) (fun v g=> value v g i) M (a.rootInputState b space m p))
    (positive : 0< M) (v : Fin H) (g : Fin groups) :
    digit (tbl).outputBits (lane g positive).val
      (a.preparedImage b space m ((A).output rid+(row H groups M (position v g positive)).val)).val=
      ((tbl).law (encode (tbl).field (b.table p).1 (value v g))).val := by
  have name:=(rootIndex r (2^n) p).isLt
  have head:=b.bounds a.projectionEnd H groups M w p
  have past : (tbl).stop start H groups M≤ a.headerEnd b:=
    head.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ name) _)
  have word:=(space.rows p).2
  have mid:a.headerEnd b≤(A).middle rid:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have lower:(A).middle rid≤(A).output rid:=Nat.le_add_right ..
  have range:=(row H groups M (position v g positive)).isLt
  rw [a.gatheredImage b space m p _ (lower.trans (Nat.le_add_right ..)) (Nat.add_lt_add_left range _)]
  exact (tbl).evaluated start _ _ input rfl rfl (past.trans mid) prior le_rfl word packed positive _
    (a.rootInput_tables b space m p) value source v g

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
