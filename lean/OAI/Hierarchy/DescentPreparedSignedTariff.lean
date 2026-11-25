import OAI.Hierarchy.DescentPreparedPageTariff
import OAI.Hierarchy.DescentPackedMatchedAll
import OAI.Hierarchy.DescentPackedColumnHardware

namespace OAI
/-! Costs of all original-port retile reads and all signed matrix passes before root extraction. -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields DescentGLNielsen
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentStaticWordColumn
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t field Ht w : ℕ} (a : Receiver D cap N n r c H G K R M h l t field Ht w)
local notation "b" => DescentSignedCableCodec.width D cap
local notation "slots" => 2*cap
local notation "C" => a.signedChart
local notation "d" => h+l
local notation "depth" => (schedule d).length
local notation "views" => 2*(H*chunks G M)+R*Subwords.stride b R M
local notation "shifted" => (2*cap)*N
local notation "joins" => N*(2*2^(joinWidth b N*M))

def retileBill (D cap N H G R M : ℕ) :=
  let digitWidth:=DescentSignedCableCodec.width D cap
  let qty:=2*(H*chunks G M)+R*Subwords.stride digitWidth R M
  let fieldCount:=2*cap*N
  (8+10*qty+fieldCount*(4+(H*chunks G M)*(2*48+4)))+
    7*(15*(qty+1)+(15+fieldCount*(11+4*48)))

theorem retile_price :
    a.retileClock+7*names a.retileCPU ≤ retileBill D cap N H G R M := by
  let xs:=incoming a.old
  have time:=Retile.tariff a.origin H b a.slots a.ratio a.positive xs
  have body:=DescentOperandVectorArena.names_passes (Subwords.destination a.origin b H G R M)
    (H*chunks G M) (Retile.pitch H G M) w 48 (Retile.field a.origin b H G R M xs) 0 shifted
    (fun i _ ih=>by have fit:i < shifted:=by simpa using ih
                    simp [Retile.field,fit,Subwords.term,Expr.work])
  let sheet:=Subwords.literals (w:=w) a.origin H b a.slots a.ratio a.positive
  have text:=sheet.hardware.2
  have len:=Subwords.length_eq (w:=w) a.origin H b a.slots a.ratio a.positive
  change sheet.length=views at len
  change _+7*names (sheet.program.seq (ProtocolRAM.program w (Retile.scans a.origin b H G R M xs)))≤_
  rw [names_seq,text,len]
  dsimp only [retileBill,retileClock,Retile.scans,xs] at *
  omega

private theorem change_names (A : DescentGLPacked.Layout) (host lanes steps₀ offset bits : ℕ) :
    names (ProtocolRAM.program bits (steps A host lanes offset steps₀))≤15+steps₀*(11+4*110) := by
  induction steps₀ generalizing offset with
  | zero=>rw [steps,ProtocolRAM.program,names_scan];rfl
  | succ n ih=>
    have upper:=DescentGLPacked.work (A.board offset) (A.bank offset) (A.flag offset)
    have later:=ih (offset+1)
    rw [steps,ProtocolRAM.program,names_seq,Nat.succ_mul]
    simp only [single,Pass.procedure,names_scan]
    omega

def chipBill (D cap N H M h l printed : ℕ) :=
  let count:=2*cap
  let sum:=N*(2*2^(joinWidth (DescentSignedCableCodec.width D cap) N*M))
  let source:=1+18*N
  let rows:=H*2^h
  let stepCount:=(schedule (h+l)).length
  (4+10*sum)+((8+10*printed)+(4+count*(4+rows*(2*source+4)))+
    ((4+stepCount*(2*19+4))+(4+stepCount*(4+(count*H)*2^h*(2*110+4)))))+
  7*(15*(sum+1)+15*(printed+2)+(15+count*(11+4*source))+((11+4*19)+(15+stepCount*(11+4*110))))

def printed := (controlSheet a.signedOrigin d w).length+(Dated.routes (C) (slots*H) h l b w).length

theorem chip_price : a.chipClock+7*names a.chipCPU ≤ chipBill D cap N H M h l a.printed := by
  let I:=controlSheet a.signedOrigin d w
  let J:=Dated.routes (C) (slots*H) h l b w
  let X:=a.signedOp
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes (C).input.base rows rows X 0 slots
  let ps:=steps ((C).chosen d) (slots*H) (2^h) 0 depth
  let flag:=(controlBanks a.signedOrigin d).expr (.lookup a.saved (.lit 0))
  have fw (i : ℕ) (hi:i < slots) : (X i).work≤1+18*N := by
    simp only [X,signedOp,joinOp,dite_eq_left hi]
    simpa [Gather.assembly,Nat.mul_comm 18] using Gather.collect_work _ (fun x=>Expr.lookup (a.tiles ⟨i,hi⟩ x) .row)
      (List.finRange N) 7 (fun _=>le_rfl)
  have it:=DescentPackedFlowBatch.tariff (C).input.base rows rows slots X (1+18*N) fw
  have ic:=DescentOperandVectorArena.names_passes (C).input.base rows rows w (1+18*N) X 0 slots
    (fun i _ ih=>fw i (by simpa using ih))
  have mt:=DescentGLPacked.tariff ((C).chosen d) (slots*H) h 0 depth
  have mc:=change_names ((C).chosen d) (slots*H) (2^h) depth 0 w
  have op:flag.work=19:=rfl
  unfold chipCPU SignedFields.program
  simp only [names_seq,Book.names,names_scan]
  change ((4+10*joins)+((8+10*(I.length+J.length))+(ProtocolRAM.clock gs+((4+depth*(2*flag.work+4))+ProtocolRAM.clock ps))))+
    7*(15*(joins+1)+(names I.program+names J.program+(names (ProtocolRAM.program w gs)+
      ((11+4*flag.work)+names (ProtocolRAM.program w ps)))))≤_
  rw [I.hardware.2,J.hardware.2,op]
  dsimp only [chipBill,printed,I,J,gs,ps,rows] at *
  omega

def wholeBill (book : RootBook n r D (2^r) cap field) :=
  retileBill D cap N H G R M+chipBill D cap N H M h l a.printed+a.projectionsBill+
    ((4+10*a.rootROMWords book)+7*(15*(a.rootROMWords book+1)))+a.rootCatalogBill book

theorem whole_price (book : RootBook n r D (2^r) cap field) (space : a.PreparedFits book) :
    a.preparedTicks book space+7*names (a.preparedRoots book space) ≤ a.wholeBill book :=
  (a.prepared_price book space).trans <| by
    have old:=a.retile_price
    have matrix:=a.chip_price
    dsimp only [wholeBill]
    omega

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
