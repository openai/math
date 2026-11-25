import OAI.Hierarchy.DescentGatheredLookupWords
import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # The shared packed presence, endpoint and grain mask for reset candidates -/
namespace Hierarchy.DescentCandidateMaskRAM
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentIssuedGoodHeaders DescentResetFieldAssembler
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {field H G M w : ℕ}

/-- The first four digits are the occupancy flag, both short endpoint codes,
and the receiving code. The following four are the two shared endpoint ranks,
the receiving rank, and the self-absence flag. The last digit is the physical
grain count. Both private and direct contact rows are core cables. -/
def visible (x : Fin 9→Cell field) : Prop :=
  (x 0).val≠0 ∧ 0<(x 8).val ∧ ((x 1).val=(x 3).val ∨ (x 2).val=(x 3).val)

def render (x : Fin 9→Cell field) : Cell (field*7) :=
  raw field (if visible x then
    ⟨true,(x 4).val,(x 5).val,(x 6).val,decide ((x 7).val≠0),true,(x 8).val⟩
    else Meta.blank)

theorem masked (x : Fin 9→Cell field) (hidden : ¬visible x) :
    render x=raw field Meta.blank := by simp [render,hidden]

theorem vacant_or_empty (x : Fin 9→Cell field) (dead : (x 0).val=0 ∨ (x 8).val=0) :
    render x=raw field Meta.blank := by
  apply masked
  rintro ⟨present,paid,_⟩
  exact dead.elim present (fun z=>Nat.ne_of_gt paid z)

theorem missed (x : Fin 9→Cell field) (source : (x 1).val≠(x 3).val)
    (target : (x 2).val≠(x 3).val) : render x=raw field Meta.blank :=
  masked x (fun h=>h.2.2.elim source target)

theorem issue
    (tables : Fin 9→Tables) (reads : Fin 9→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 9→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*9) (field*7) M H G w out.base)
    (rom : resident (render ∘ (encode field 9).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*9)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>render (x a g)) M dst ∧
    ∀addr,(addr < mid ∨ mid+rows≤addr)→(addr < out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words render tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentCandidateMaskRAM

end OAI
