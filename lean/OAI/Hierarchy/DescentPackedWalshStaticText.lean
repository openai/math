import OAI.Hierarchy.DescentPackedWalshStatePrice
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Exact cheap opcode and register/label tariffs of the packed measurement routines -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w u l : ℕ}

/-- The high and low lookup butterflies have exactly the same short native code. -/
theorem pass_text (root first H b w z : ℕ) (axes : List (Fin (u+l))) :
    CheapCode (code w root first H u l b z axes) ∧
      names (code w root first H u l b z axes)≤19+183*axes.length := by
  induction axes generalizing z with
  | nil=>
    refine ⟨@scan_cheap _ _ _ _,?_⟩
    rw [code,names_scan]
    simp [Expr.work]
  | cons i is ih=>
    obtain ⟨small,tariff⟩:=ih (z+1)
    refine ⟨cheap_seq (@scan_cheap _ _ _ _) small,?_⟩
    rw [code,names_seq,layerProgram,names_scan,List.length_cons,Nat.mul_add]
    change (11+4*43)+_≤_
    omega

theorem spectrum_text (root first table H u l b w : ℕ) :
    CheapCode (numeratorCode root first table H u l b w) ∧
    names (numeratorCode root first table H u l b w)≤97+366*(u+l) := by
  obtain ⟨firstCode,firstBill⟩:=pass_text root first H b w 0 (axesList u l)
  obtain ⟨lastCode,lastBill⟩:=pass_text root (sqOffset first H u l) H b w 0 (axesList u l)
  refine ⟨cheap_seq (cheap_seq firstCode (@scan_cheap _ _ _ _)) lastCode,?_⟩
  have length : (axesList u l).length=u+l:=by simp [axesList]
  rw [length] at firstBill lastBill
  rw [numeratorCode,names_seq,names_seq,names_scan]
  change _+(11+4*12)+_≤_
  omega

theorem depth_text (D : DepthShelf) (P : Plan) (w H u j : ℕ) :
    CheapCode (D.code P w H u j) ∧ names (D.code P w H u j)≤351+183*P.depth := by
  constructor
  · unfold DepthShelf.code Column.publishCode
    exact @cheap_seq w _ _ (@scan_cheap w _ _ _)
      (@cheap_seq w _ _ (@Plan.cheap P D.reduce D.first w) (@scan_cheap w _ _ _))
  · have recurrent:=P.program_text w D.reduce D.first
    unfold DepthShelf.code Column.publishCode
    rw [names_seq,names_scan,names_seq,names_scan]
    let B:=Column.banks D.extract P.axis (P.chunks P.depth) (P.bits+P.depth) (P.laneBits P.depth)
      (Column.input P D.first)
    have surcharge:=Column.clock B (P.laneBits P.depth)
    have gain:=Weight.tariff D.weights j
    change 11+4*(Weight.expr D.weights j).work+(names _+(11+4*(Column.scanRow B _).work))≤_
    omega

theorem calendar_text (C : Calendar (u+l)) (P : Plan) (w H n : ℕ) :
    CheapCode (C.code P w H n) ∧ names (C.code P w H n)≤19+n*(351+183*P.depth) := by
  induction n with
  | zero=>
    refine ⟨@scan_cheap _ _ _ _,?_⟩
    rw [Calendar.code,names_scan]
    simp [Expr.work]
  | succ n ih=>
    obtain ⟨old,price⟩:=ih
    obtain ⟨stage,tall⟩:=depth_text (C.atDepth n) P w H u n
    refine ⟨@cheap_seq w (C.code P w H n) ((C.atDepth n).code P w H u n) @old @stage,?_⟩
    rw [Calendar.code,names_seq,Nat.succ_mul]
    omega

end
end Hierarchy.DescentPackedWalsh

end OAI
