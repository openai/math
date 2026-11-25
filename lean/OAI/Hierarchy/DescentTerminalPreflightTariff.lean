import OAI.Hierarchy.DescentTerminalGeometryTariff
import OAI.Hierarchy.DescentTerminalPrimitiveNames
import OAI.Hierarchy.DescentTerminalHeaderDraftPrice
import OAI.Hierarchy.DescentTerminalControlTariff
import OAI.Hierarchy.DescentTerminalWeightShelf

namespace OAI
/-! # Terminal preprocessing fee from the emitted instructions and their clocks -/
namespace Hierarchy.DescentTerminalPreflightTariff
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalLocalPortBook DescentTerminalGrainProfiles
open DescentTerminalCombinedRole DescentTerminalControlProgram
open DescentStaticWordColumn (names names_seq)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section

def cost {w:ℕ} (code:Procedure w) (clocks bw:ℕ) := (names code+clocks)*(bw+1)
def budget (h H factor paid bw:ℕ) := (2^(h/2)+H*factor)*(bw+1)+paid*(bw+1)

theorem chain {w:ℕ} (first second:Procedure w) (a b bw:ℕ) :
    cost (first.seq second) (a+b) bw=cost first a bw+cost second b bw := by
  simp only [cost,names_seq];ring

section Scalars
variable {L blocks d u v:ℕ} (w:ℕ) (one two:Shelf) (atRole start H:ℕ)
    (chart:Fin L→Fin blocks→Gather.Address) (f0:(Fin L→Cell d)→Cell u) (f7:(Fin L→Cell d)→Cell v)
    (source:Fin 3→Bank) (dc cc cw q hidden N A groups p:ℕ)
local notation "bits" => DescentTerminalPrimitiveNames.program w one two atRole start H chart f0 f7 source dc cc cw q hidden N A groups p
local notation "ticks" => DescentTerminalPrimitiveNames.clocks d dc start H chart
theorem primitive (h factor paid bw:ℕ)
    (ptr:DescentTerminalPointerFrame.size L d≤2^(h/2))
    (count:DescentTerminalPointerFrame.size 3 dc≤2^(h/2))
    (scans:(H+1)*(L+1)*(blocks+1)≤H*factor) :
    cost bits ticks bw≤3000*budget h H factor paid bw := by
  have a:=DescentTerminalPrimitiveNames.names_le w one two atRole start H chart f0 f7 source dc cc cw q hidden N A groups p
  have b:=DescentTerminalPrimitiveNames.clocks_le (d:=d) (dc:=dc) (origin:=start) (shops:=H) (chart:=chart)
  have positive:=Nat.two_pow_pos (h/2)
  have raw:names bits+ticks≤3000*(2^(h/2)+H*factor+paid):=by
    ring_nf at scans a b ⊢
    omega
  calc
    cost bits ticks bw≤(3000*(2^(h/2)+H*factor+paid))*(bw+1):=Nat.mul_le_mul_right _ raw
    _=_:=by unfold budget;ring
end Scalars

theorem controls (x:Plan) (w h H factor paid bw:ℕ) (values:ℕ→ℕ) (parts:Book.Parts)
    (books:x.codeWords≤2^(h/2)) (shelf:x.shape.limit≤2^(h/2)) (room:x.sites≤H*factor) :
    cost (x.program w values (Book.expression parts)) (x.time (Book.expression parts)) bw≤13000*budget h H factor paid bw := by
  have core:=fees x w values parts
  have positive:=Nat.two_pow_pos (h/2)
  have raw : names (x.program w values (Book.expression parts))+x.time (Book.expression parts)≤
      13000*(2^(h/2)+H*factor+paid):=by omega
  calc
    _≤(13000*(2^(h/2)+H*factor+paid))*(bw+1):=Nat.mul_le_mul_right _ raw
    _=_:=by unfold budget;ring

theorem weights (V A base h H factor paid bw w:ℕ) (room:Book.WeightShelf.words V A≤6*2^(h/2)) :
    cost (Book.WeightShelf.program V A base w) (4+10*Book.WeightShelf.words V A) bw≤230*budget h H factor paid bw := by
  have tariff:=(Book.WeightShelf.tariff V A 1 1 base w).2.1
  have positive:=Nat.two_pow_pos (h/2)
  have raw : names (Book.WeightShelf.program V A base w)+(4+10*Book.WeightShelf.words V A)≤
      230*(2^(h/2)+H*factor+paid):=by omega
  calc
    _≤(230*(2^(h/2)+H*factor+paid))*(bw+1):=Nat.mul_le_mul_right _ raw
    _=_:=by unfold budget;ring

/-- The measured geometry passes run in the middle of the other stages. Their
bill is additive even when the paid actor census precedes the primitive issue
and the public width scan follows it. -/
theorem assembled {w:ℕ} (pop actors scalar weights book control cable «public» literals draft:Procedure w)
    (cp ca cs cw cb cc ce cx cl cd h H factor paid bw:ℕ)
    (early:cost ((((pop.seq actors).seq «public»).seq literals).seq draft) (cp+ca+cx+cl+cd) bw≤6000000*budget h H factor paid bw)
    (registered:cost scalar cs bw≤3000*budget h H factor paid bw)
    (dictionary:cost weights cw bw≤230*budget h H factor paid bw)
    (geometry:(names book+cb+names cable+ce)*(bw+1)≤30000*budget h H factor paid bw)
    (routes:cost control cc bw≤13000*budget h H factor paid bw) :
    cost ((((((((pop.seq actors).seq scalar).seq weights).seq book).seq control).seq cable).seq «public»).seq literals |>.seq draft)
      (cp+ca+cs+cw+cb+cc+ce+cx+cl+cd) bw≤6050000*budget h H factor paid bw := by
  simp only [chain] at early ⊢
  have both:cost book cb bw+cost cable ce bw=(names book+cb+names cable+ce)*(bw+1):=by simp only [cost];ring
  rw [←both] at geometry
  omega

end
end Hierarchy.DescentTerminalPreflightTariff

end OAI
