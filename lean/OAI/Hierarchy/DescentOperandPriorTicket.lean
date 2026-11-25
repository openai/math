import OAI.Hierarchy.DescentOperandSignedSearch
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # Constructing the old signed-grain search key from the reached operand's four stored fields -/
namespace Hierarchy.DescentOperandPriorTicket
open DescentOperandStateBanks DescentSIMDLookup DescentTerminalSignedGrainWord DescentOperandSignedSearch
open DescentSharedCableNames DescentIssuedGoodHeaders DescentPackedZip DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Gather
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {b H G w M : ℕ}

def key (D cap units : ℕ) (x : Fin 4→Cell b) : Cell (keyBits D cap) :=
  if active : (x 0).val=1 ∧ (x 1).val<D ∧ (x 2).val<cap ∧ (x 3).val/units<cap then
    let peer : Fin D :=⟨_,active.2.1⟩
    let first : Fin cap :=⟨_,active.2.2.1⟩
    let within : Fin cap :=⟨_,active.2.2.2⟩
    Packed.token (some (finProdFinEquiv (finProdFinEquiv (peer,first),within)))
  else 0

theorem cable (D cap units peer name chunk : ℕ) (x : Fin 4→Cell b)
    (read : ∀j,(x j).val=(Pointer.cable peer name chunk).header j)
    (endpoints : peer<D) (first : name<cap) (aligned : chunk/units<cap) :
    key D cap units x=Packed.token (some (finProdFinEquiv (finProdFinEquiv
      ((⟨peer,endpoints⟩:Fin D),(⟨name,first⟩:Fin cap)),(⟨chunk/units,aligned⟩:Fin cap)))) := by
  have tag : (x 0).val=1 := read 0
  have left : (x 1).val=peer := read 1
  have right : (x 2).val=name := read 2
  have sub : (x 3).val=chunk := read 3
  simp [key,tag,left,right,sub,endpoints,first,aligned]
  rfl

theorem pin_or_private (D cap units : ℕ) (x : Fin 4→Cell b) (inactive : (x 0).val≠1) :
    key D cap units x=0 := by simp [key,inactive]

/-- The same four physically fetched words determine each lane independently.
No candidate or edge handle is read from a global table. -/
theorem issue (D cap units : ℕ)
    (tables : Fin 4→Tables) (reads : Fin 4→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 4→Cell b) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=b) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=b) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (b*4) (keyBits D cap) M H G w out.base)
    (rom : resident (key D cap units ∘ (encode b 4).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((b*4)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>key D cap units (x a g)) M dst ∧
    ∀a,(a< mid ∨ mid+rows≤a)→(a<out.base ∨ out.base+rows≤a)→dst a=mem a := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (key D cap units) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

theorem point_eq {D cap : ℕ} {a c : Option (Fin (D*cap*cap))} :
    point D cap (Packed.token a)=point D cap (Packed.token c) ↔ a=c := by
  constructor
  · intro same
    simp only [point,Packed.token_back] at same
    cases a with
    | none => cases c <;> simp_all
    | some i =>
      cases c with
      | none => simp at same
      | some j =>
        simp only [Option.map_some,Option.some.injEq] at same ⊢
        apply (finProdFinEquiv.symm : Fin (D*cap*cap) ≃ Fin (D*cap)×Fin cap).injective
        exact Prod.ext (Fin.ext (congrArg Prod.fst same)) (Fin.ext (congrArg Prod.snd same))
  · rintro rfl;rfl

theorem signal {D cap : ℕ} (row : Cell (DescentSignedCableCodec.width D cap)) (wanted : Fin (D*cap*cap)) :
    project D cap row=Packed.token (some wanted) ↔
      point D cap (project D cap row)=point D cap (Packed.token (some wanted)) := by
  constructor
  · intro same;rw [same]
  · intro same
    exact congrArg Packed.token (point_eq.mp same)

end
end Hierarchy.DescentOperandPriorTicket

end OAI
