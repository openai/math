import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentPreparedMatrixFrame

namespace OAI
/-! # Reading a permanently stored root operand from the final dated window -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local.Gather
open DescentSixParty.Chronology DescentPackedZip DescentSharedBookScan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 4000
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "groups" => 2^c
local notation "slots" => H*chunks groups M
local notation "A" => RootTemplates.arena (a.headerEnd b) H groups M r n D
local notation "Page" => RootPage r (2^n)
variable (space : a.PreparedFits b) (m : Memory w) (p : Page)
local notation "rid" => (rootIndex r (2^n) p).val
local notation "start" => b.atPage a.projectionEnd H groups M p
local notation "input" => b.target a.projectionEnd H groups M p
local notation "tbl" => (b.table p).2
local notation "act" => ((tbl).terms start H groups M input)

/-- An exceptional page may have written local counters. Both its input state
and the completed catalogue retain the genuinely mounted prefix below the header. -/
theorem root_input_before (x : ℕ) (lo : x<a.headerEnd b) :
    a.rootInputState b space m p x=a.preparedImage b space m x :=by
  rw [a.before_header b space m x lo]
  cases kind:p.2 with
  | inl _=>simp [rootInputState,kind]
  | inr _=>
    simp only [rootInputState,kind]
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (lo.trans_le (Nat.le_add_right ..)))

theorem gathered_source_from_final (value : Fin H→Fin groups→Fin (b.table p).1→Cell (tbl).field)
    (prior : ∀i,((tbl).reads i).Fits w ((A).middle rid))
    (packed : M*max ((tbl).field*(b.table p).1) (tbl).outputBits≤ w/2)
    (earlier : ∀i,((tbl).reads i).Fits w (a.headerEnd b))
    (source : ∀i,Source ((tbl).reads i) (fun v g=>value v g i) M (a.preparedImage b space m)) :
    Source (a.gatheredOperand b p) (fun v g=>encode (tbl).field (b.table p).1 (value v g)) M
      (a.preparedImage b space m) :=by
  apply a.gathered_source b space m p value prior packed
  intro i row
  exact (eval_below _ _ (a.preparedImage b space m) (a.rootInputState b space m p)
    (earlier i) (a.root_input_before b space m p)).trans (source i row)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
