import OAI.Hierarchy.DescentRelativeRank
import OAI.Hierarchy.DescentCandidateMaskRAM
import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Ranking packed relative shapes against four short public peer thresholds -/
namespace Hierarchy.DescentRelativeClassChip
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentIssuedGoodHeaders DescentSortedRoster DescentFallbackLeafScan
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {field H G M w : ℕ}

theorem first_indexed {pitch : ℕ} (input : Fin pitch→Fin 4→Option (Fin pitch))
    (v : Fin pitch) (j : Fin 4) :
    first (indexed input) v j=indexed input v j := by
  unfold first
  split
  next dup=>
    obtain ⟨i,lt,same⟩:=dup
    cases atJ : indexed input v j with
    | none=>rfl
    | some key=>
      have left:=(indexed_iff input v i key).1 (same.trans atJ)
      have right:=(indexed_iff input v j key).1 atJ
      have eqn:=left.2.symm.trans right.2
      omega
  next _=>rfl

theorem rank_read {pitch : ℕ} (peer : Fin pitch→Fin 4→Option (Fin pitch))
    (receiver target : Fin pitch) (x : Fin 5→Cell field) (width root shape : ℕ)
    (positive : 0<width) (small : shape<width) (absolute : target.val=shape+width*root)
    (size : 4<2^field) (shapeRead : (x 4).val=shape)
    (read : ∀j : Fin 4,(x j.castSucc).val=threshold width root ((first peer receiver j).map Fin.val)) :
    (rank x).val=before peer receiver target := by
  let kept:=Finset.univ.filter (fun j : Fin 4=>earlier (x j.castSucc).val (x 4).val)
  have count : kept.card<2^field := (Finset.card_le_univ kept).trans_lt (by simpa using size)
  change ((kept.card:Cell field)).val=_
  rw [Fin.val_cast_of_lt count,←order_count]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  change earlier (x j.castSucc).val (x 4).val=true ↔
    (first peer receiver j).any (fun p=>decide (p<target))=true
  rw [read j,shapeRead,threshold_read width root shape positive small]
  cases first peer receiver j with
  | none=>rfl
  | some b=>
    change decide (b.val<shape+width*root)=true ↔ decide (b.val<target.val)=true
    rw [absolute]

theorem issue
    (tables : Fin 5→Tables) (reads : Fin 5→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 5→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*5) (field) M H G w out.base)
    (rom : resident (rank ∘ (encode field 5).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*5)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>rank (x a g)) M dst ∧
    ∀addr,(addr < mid ∨ mid+rows≤addr)→(addr < out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words rank tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentRelativeClassChip

end OAI
