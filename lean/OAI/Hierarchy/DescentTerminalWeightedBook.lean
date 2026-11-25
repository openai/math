import OAI.Hierarchy.DescentTerminalWeightShelf
import OAI.Hierarchy.DescentTerminalBookNative

namespace OAI
/-! # Printing all six book fields with their physically installed weight dictionaries -/
namespace Hierarchy.DescentTerminalLocalPortBook.Print.Layout
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalRecipeRows ProtocolRAM Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {L V A w : ℕ} (P : Layout L) (decode : (Fin L→Cell P.bits)→Directory 4 V A)
variable (base : ℕ) (m : Memory w)
local notation "M" => V*A
local notation "weights" => Book.WeightShelf.banks V A base
local notation "installed" => Book.WeightShelf.memory V A base m
local notation "mounted" => Book.WeightShelf.program V A base w
local notation "after" => P.memory decode M installed 6 le_rfl

/-- All six source fields and their weight functions are emitted by one
static two-phase procedure. Its only semantic input is the original reached
geometry as decoded from the pre-existing unmodified incoming row banks. -/
theorem weighted_issued (source : ∀j,(P.source j).Fits w base)
    (ahead : Book.WeightShelf.finish V A base≤P.start) (offset : 2^P.bits<2^w) (space : P.stop<2^w)
    (t : Fin P.homes→Site) (room : ∀i,Room (t i) 4 V M A)
    (geometry : ∀i,Aligned (t i) (decode (Gather.values P.source m i))) :
    ((mounted).seq (P.prefix decode M w 6 le_rfl)).Exec m after ((4+10*Book.WeightShelf.words V A)+P.time 6 le_rfl) ∧
    CheapCode ((mounted).seq (P.prefix decode M w 6 le_rfl)) ∧
    Book.Issued (P.parts weights) (fun i : Fin P.homes =>
      issue (t i) (room i) (rowName (t i) (room i)) (refName (t i) (room i))) after ∧
    ∀a,a<base→after a=m a := by
  have low : P.start≤P.stop:=Nat.le_add_right ..
  have enter : base≤Book.WeightShelf.finish V A base:=Nat.le_add_right ..
  have cap:=ahead.trans_lt (low.trans_lt space)
  have put:=Book.WeightShelf.execute V A base m cap
  have keep : Below base installed m:=fun a h=>put.2.2 a (.inl h)
  have fits (j : Fin L) : (P.source j).Fits w P.start:=
    ProtocolRAMGeneratedWrite.fits_mono _ (enter.trans ahead) (source j)
  have same (i : Fin P.homes) : Gather.values (d:=P.bits) P.source installed i=Gather.values P.source m i := by
    funext j
    unfold Gather.values
    rw [keep.expr (P.source j) _ (source j) le_rfl]
  have here (i : Fin P.homes) : Aligned (t i) (decode (Gather.values P.source installed i)) := by
    rw [same]
    exact geometry i
  have native:=P.native decode M installed fits offset space 6 le_rfl
  refine ⟨?_,?_,P.issued decode M installed fits offset space t room here weights (fun j=>?_) put.2.1,?_⟩
  · exact @Procedure.Exec.then w mounted (P.prefix decode M w 6 le_rfl)
      m installed after (4+10*Book.WeightShelf.words V A) (P.time 6 le_rfl) put.1 native.1
  · exact @ProtocolRAM.cheap_seq w mounted (P.prefix decode M w 6 le_rfl)
      (DescentStaticWordColumn.cheap w base (Book.WeightShelf.data V A) (Book.WeightShelf.words V A)) native.2.1
  · exact (Book.WeightShelf.room V A base P.start w ahead (low.trans_lt space) j).2.2
  · intro a h
    exact (native.2.2.1 a (h.trans_le (enter.trans ahead))).trans (keep a h)

end
end Hierarchy.DescentTerminalLocalPortBook.Print.Layout

end OAI
