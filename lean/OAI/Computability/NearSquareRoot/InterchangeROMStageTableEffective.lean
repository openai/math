import OAI.Computability.NearSquareRoot.InterchangeROMStageTableGenerate
import OAI.Computability.NearSquareRoot.InterchangeROMStageTablePhysical

/-! # Computable command quotation for the five numbered rectangle tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable
open InterchangeROMStage GeneratorSyntax

variable {X : Type} [Primcodable X]

theorem effective_command {c : X → Parameters} {t : X → Frame.Table} (hc : Computable c)
    (ht : Computable t) : Effective ltr (fun x => command (c x) (t x)) := by
  have hd : Computable fun x => (c x).2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hc))
  have hin : Computable fun x => (expandRoles (t x).2.1 (c x).2.2.1).length :=
    Computable.list_length.comp
      (primrec_expandRoles.to_comp.comp (Computable.fst.comp (Computable.snd.comp ht)) hd)
  have hout : Computable fun x => (expandRoles (t x).2.2 (c x).2.2.1).length :=
    Computable.list_length.comp
      (primrec_expandRoles.to_comp.comp (Computable.snd.comp (Computable.snd.comp ht)) hd)
  exact LoomRegisters.effective_romMatrix (Computable.fst.comp (Computable.snd.comp hc)) hin hout
    (Computable.const 0) (primrec_gateMatrix.to_comp.comp hc ht)

theorem primrec_bytes : Primrec₂ bytes := by
  have hp : Primrec (fun z : Parameters × Frame.Table => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun z : Parameters × Frame.Table => z.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hin : Primrec (fun z : Parameters × Frame.Table => (expandRoles z.2.2.1 z.1.2.2.1).length) :=
    Primrec.list_length.comp (primrec_expandRoles.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hd)
  exact InterchangeROMTable.primrec_spelled_matrixTable hp hin primrec_gateMatrix

theorem primrec_factor : Primrec fun z : Parameters × Frame.Table =>
    LoomRegisters.romPayloadFactor (z.2.2.1.length*z.1.2.2.1) (z.2.2.2.length*z.1.2.2.1) (bytes z.1 z.2) := by
  have hd : Primrec (fun z : Parameters × Frame.Table => z.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  apply LoomRegisters.primrec_romPayloadFactor _ _ primrec_bytes
  · exact Primrec.nat_mul.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) hd
  · exact Primrec.nat_mul.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hd

theorem computable_charge {c : X → Parameters} {t : X → Frame.Table} {n w : X → ℕ}
    (hc : Computable c) (ht : Computable t) (hn : Computable n) (hw : Computable w) :
    Computable fun x => charge (c x) (t x) (n x) (w x) := by
  let pair (x : X) := (c x,t x)
  have factor := Computable.comp (g:=pair) primrec_factor.to_comp (hc.pair ht)
  have mass : Computable (fun x => n x*(w x+1)+1) :=
    Computable.succ.comp (Primrec.nat_mul.to_comp.comp hn (Computable.succ.comp hw))
  exact Primrec.nat_mul.to_comp.comp factor mass

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
