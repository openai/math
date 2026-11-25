import OAI.Hierarchy.DescentDenseHostOrder
import OAI.Hierarchy.DescentStageEdgeReceipt

namespace OAI
/-! # Executing the survivor prefix of the bounded reset-host slot table -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "pool" => DescentDenseHostOrder.roster Z.graph (Z.k-T.commonDepth) Ht
variable {H : ℕ} (vertex : Z.V↪Fin H)

def hostTape : DescentStageEdgeReceipt.Tape ↥(commonNames Z T) where
  Parent:=↥(commonNames Z T)
  order:=denseHostRank Z T vertex
  slots:=H*(pool).card
  rank:=(rawHostRank Z T vertex).trans ⟨Fin.val,Fin.val_injective⟩
  inSlots x:=(rawHostRank Z T vertex x).isLt
  span _:=1
  owner:=id
  offset _:=0
  offsetFits _:=by decide
  read x:=by
    rw [denseHostRank_read]
    simp [ProtocolRAMPortRanks.«prefix»]

/-- A single pass over the old-host × local-position bitmap publishes the
new dense ordinals. Each surviving host reads its own true prior sparse row. -/
theorem hostTape_native {w flags ids : ℕ} (mem : Memory w) (sep : flags+H*(pool).card≤ ids)
    (fit : ids+H*(pool).card+1<2^w)
    (flagsRead : ∀j<H*(pool).card,mem (flags+j)=
      (DescentEdgeTapePrefix.row (fun _ : ↥(commonNames Z T)=>1) (fun x=>(rawHostRank Z T vertex x).val) j:Word w)) :
    let tape:=hostTape Z T vertex
    let result:=ProtocolRAMEndpointPrefix.image ids (DescentEdgeTapePrefix.before tape.span tape.rank) mem tape.slots
    (ProtocolRAMEndpointPrefix.exclusive w flags ids tape.slots).Exec mem result (10+(3+12*tape.slots)) ∧
      ∀x:↥(commonNames Z T),result (ids+(rawHostRank Z T vertex x).val)=((denseHostRank Z T vertex x).val:Word w) := by
  obtain ⟨runs,idsRead⟩:=(hostTape Z T vertex).native mem sep fit flagsRead
  refine ⟨runs,fun x=>?_⟩
  let tape := hostTape Z T vertex
  have address : tape.rank (tape.owner x) = (rawHostRank Z T vertex x).val := rfl
  have offset : (tape.offset x : Word w) = 0 := Nat.cast_zero
  have order : tape.order x = denseHostRank Z T vertex x := rfl
  have read := idsRead x
  change ProtocolRAMEndpointPrefix.image ids (DescentEdgeTapePrefix.before tape.span tape.rank)
    mem tape.slots (ids + tape.rank (tape.owner x)) + (tape.offset x : Word w) =
    ((tape.order x).val : Word w) at read
  rw [address, offset, add_zero, order] at read
  exact read

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
