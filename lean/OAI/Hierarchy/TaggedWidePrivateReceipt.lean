import OAI.Hierarchy.TaggedWideTerminalPrivateBits
import OAI.Hierarchy.TaggedWideCalendarFrame

namespace OAI
/-! # Evaluation of the private part under a purchased branch’s common pin numbering -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM
open ProbeStage ProbeStage.CoreBoard PhysicalTerm Tagged WideStack WideStack.Leaf WideControlJoin
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {S : PurchaseSampler} {h W k width : ℕ}
  (board : Board) (order : Fin board.coreRows ≃ Edges S h (2^W) k)
  {E Se Pos Hist Output B : Type} [Fintype E] [Fintype Se] [Fintype Pos] [Fintype Hist] [Fintype Output]
  (G : Gate) (dst : ℕ) (room : dst+9*board.rows≤G.u)
  (narrow : WideParent.columnBits width≤G.W+1)
local notation "Priv" => board.Private order
local notation "Data" => fun P:Type=>Pos⊕((Bool×((_:P)×Fin width))⊕(Hist⊕Output))
local notation "V" => SitePins E Se (Data Priv) G
set_option quotPrecheck false in
local notation "pin" => fun (side:Bool) (r:Priv) (j:Fin width)=>(Sum.inr (Sum.inr (Sum.inl (Sum.inr (Sum.inl (side,⟨r,j⟩))))) : V)

def Board.privateLeaf := board.privatePaired (F:=F) order G dst room narrow pin

private def renumber (ord:B≃Priv) : Data B≃Data Priv :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr
    (Equiv.prodCongr (Equiv.refl _) (Equiv.sigmaCongrLeft (β:=fun _ : Priv=>Fin width) ord)) (Equiv.refl _))

theorem Board.privateLeaf_read [Fintype B] (ord:B≃Priv) (raw : Fin board.rows→ProtocolRAMEmit.Row)
    (initial final : Memory G.W) (ex:E→Bool) (sel:Se→Bool)
    (positive : Pos→Bool) (y:Bool→B→Fin width→Bool) (time:Hist→Bool) (out:Output→Bool)
    (addresses : ∀i,(G.addr (board.privateWidthRow G dst room i)).val=dst+3*board.rows+3*i.val+1)
    (frame : ∀a,dst≤a→a<dst+9*board.rows→final a=ProtocolRAMEmit.emitted dst raw initial a)
    (maxWidth : ∀i:Priv,(raw i.val).width≤width) (fits : ∀i:Priv,(raw i.val).width<2^G.W) :
    let input : Data B→Bool:=Sum.elim positive (Sum.elim (fun i=>y i.1 i.2.1 i.2.2) (Sum.elim time out))
    TypedWiring.value (board.privateLeaf (F:=F) (E:=E) (Se:=Se) (Pos:=Pos) (Hist:=Hist) (Output:=Output)
      order G dst room narrow)
      (CalendarTerms.readPins (renumber board order (Pos:=Pos) (Hist:=Hist) (Output:=Output) ord) ex sel (G.terminal final) input) =
      if EndsPadded (fun r=>(raw (ord r).val).width) (fun _ : B=>width) y then
        ∏r:B,if ∀j:Fin width,j.val<(raw (ord r).val).width→y false r j=y true r j then 1 else 0 else 0 := by
  intro input
  let volts:=CalendarTerms.readPins (renumber board order (Pos:=Pos) (Hist:=Hist) (Output:=Output) ord)
    ex sel (G.terminal final) input
  rw [Board.privateLeaf,board.privatePaired_read order G dst room narrow pin raw initial final volts
    addresses frame (fun _ _=>rfl) maxWidth fits]
  have observed (side : Bool) (r : Priv) (j : Fin width) :
      volts (pin side r j) = y side (ord.symm r) j := by
    obtain ⟨i,rfl⟩ := ord.surjective r
    let source : Data B := .inr (.inl (side,⟨i,j⟩))
    let numbering : Data B ≃ Data Priv :=
      renumber board order (B:=B) (Pos:=Pos) (Hist:=Hist) (Output:=Output) (width:=width) ord
    calc
      volts (pin side (ord i) j) = input (numbering.symm (numbering source)) := rfl
      _ = input source := congrArg input (numbering.symm_apply_apply source)
      _ = y side (ord.symm (ord i)) j :=
        (congrArg (fun row : B => y side row j) (ord.symm_apply_apply i)).symm
  simp_rw [observed]
  have padded : EndsPadded (fun r=>(raw r.val).width) (fun _ : Priv=>width) (fun side r=>y side (ord.symm r)) ↔
      EndsPadded (fun r=>(raw (ord r).val).width) (fun _ : B=>width) y := by
    constructor
    · intro has side r j off
      simpa only [Equiv.symm_apply_apply] using has side (ord r) j off
    · intro has side r j off
      exact has side (ord.symm r) j (by simpa only [Equiv.apply_symm_apply] using off)
  rw [propext padded]
  split_ifs
  · symm
    refine Fintype.prod_equiv ord _ _ (fun i=>?_)
    simp only [Equiv.symm_apply_apply]
  · rfl


end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
