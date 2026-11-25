import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # A shared rectangular unary ROM with zero padding -/
namespace Hierarchy.DescentStaticUnary
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def tables {a b : ℕ} (law : Cell b→Cell 0→Cell a) (M root : ℕ) : Tables:=joined (binary law M) (b*M) root id
def query {a b : ℕ} (law : Cell b→Cell 0→Cell a) (M root : ℕ) (src : Expr):=(tables law M root).read src (.lit 0)

theorem read {H G M w a b : ℕ} (law : Cell b→Cell 0→Cell a) (empty : law 0 0=0) (root : ℕ) (m : Memory w) (room : root+2*2^(b*M)<2^w) :
    let P:=binary law M
    let dst:=after P (b*M) root m
    let top:=root+2*2^(b*M)
    (mount P (b*M) w root).Exec m dst (4+10*(2*2^(b*M))) ∧
      (∀src : Expr,∀v : Fin H→Fin G→Cell b,src.Fits w root→Source src v M m→
        (query law M root src).Fits w top ∧ Source (query law M root src) (fun h g=>law (v h g) 0) M dst) ∧
      (∀u,u<root ∨ top≤u→dst u=m u) ∧ CheapCode (mount P (b*M) w root):=by
  intro P dst top
  have size (i : Fin 2):(P i).bits≤b*M:=by fin_cases i <;>simp [P,binary]
  have installed:=binary_mounted law M P _ root m size id (fun _=>rfl)
  have old:=frame P (b*M) root m
  refine ⟨(DescentOrdinaryAtomFieldRAM.ROM.run P _ root m room).1,?_,old,DescentOrdinaryAtomFieldRAM.ROM.cheap P (b*M) w root⟩
  intro src v early source
  let C:=tables law M root
  have bancos (t : Fin 2) : (bank P (b*M) root t).Fits w top:=bank_room P _ root top t (size t) le_rfl room
  have fit : Fits C src (.lit 0) b 0 M top w:=⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) early,trivial,
    bancos 0,bancos 1,rfl,rfl⟩
  have keep : Source src v M dst:=fun p=>(ProtocolRAM.eval_below _ _ m dst early (fun z lo=>old z (.inl lo))).trans (source p)
  have none_ : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M dst:=by
    intro p
    have eqn : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p=0:=by
      apply Fin.ext
      let x:=data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p
      change x.val=0
      have bound : x.val<2^(0*M):=x.isLt
      have small : x.val<1:=bound.trans_le (show (2:ℕ)^(0*M)≤1 by simp)
      omega
    rw [eqn];rfl
  exact ⟨⟨fit.apply,fit.right,fit.shift,fit.left⟩,read_data C _ _ top fit law empty dst installed _ _ keep none_⟩

end
end Hierarchy.DescentStaticUnary

end OAI
