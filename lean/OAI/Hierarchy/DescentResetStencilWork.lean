import OAI.Hierarchy.DescentResetMeasuredReturn

namespace OAI
/-! # Operation count of the selected reset stencil, including every prior matrix bit plane -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSixParty.PackedFlow DescentPackedWalsh DescentIssuedFallbackPanel DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM
noncomputable section

theorem plane_work {m : ℕ} (tbl : Fin m→Tables) (field : Fin m→Expr)
    (each : ∀i,(field i).work≤12) : (Gather.assembly tbl field).work≤1+23*m := by
  have aux (is : List (Fin m)) : (Gather.collect tbl field is).work≤1+23*is.length := by
    induction is with
    | nil=>rfl
    | cons i is ih=>
      have bound:=each i
      simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.mul_succ] at *
      omega
  simpa only [Gather.assembly,List.length_finRange] using aux (List.finRange m)

def readWork (S : StencilBook) (X : Sources) := 200+X.count.work+23*S.m

theorem read_work (S : StencilBook) (X : Sources) (base out g : ℕ) (slot : Stencil.Slot S.r (S.degree+S.degree)) :
    (((S.readers base).inputs (S.inputs X base out g)).field slot).work≤S.readWork X := by
  let P:=(S.readers base).inputs (S.inputs X base out g)
  have head (j : Fin 3) : (P.header j).work≤50+X.count.work := by
    dsimp [P,Stencil.ReaderTables.Chart.inputs,inputs,Sources.head,Padded.Heads.field,PortLevels.AddressBook.host]
    split_ifs <;> simp only [PortLevels.relative,PortLevels.AddressBook.levelAt,Expr.work] <;> omega
  have paid (j : Fin (S.degree+S.degree)) (option : Fin 2) : (P.portHeader j option).work≤160 := by
    dsimp [P,Stencil.ReaderTables.Chart.inputs,inputs,Sources.paid,Padded.Paid.field]
    split_ifs <;> simp only [PortLevels.relative,PortLevels.protect,PortLevels.AddressBook.host,
      PortLevels.AddressBook.levelAt,PortLevels.AddressBook.zeroAt,firstTotal,Cutoff.term,Cutoff.level,neighborID,Expr.work] <;> decide
  have planes:=plane_work P.planeTables P.planes (fun _=>by rfl)
  change (Gather.assembly P.planeTables P.planes).work ≤ 1 + 23*S.m at planes
  change (P.field slot).work≤_
  rcases slot with j|((x|⟨z,x⟩)|(⟨i,x⟩|⟨j,s|x⟩))
  · have :=head j
    simp only [Stencil.Inputs.field,Readers.broadcast,Expr.work,readWork];omega
  · change 12≤_;unfold readWork;omega
  · change 12≤_;unfold readWork;omega
  · change (Gather.assembly P.planeTables P.planes).work+5≤_
    unfold readWork;omega
  · have :=paid j s
    simp only [Stencil.Inputs.field,Readers.broadcast,Expr.work,readWork];omega
  · change 12≤_;unfold readWork;omega

/-- The total length of the literal intervals used along the CPU. Zero-initialized space is not charged as a literal. -/
def literalWords (S : StencilBook) (base out : ℕ) (X : Sources) (D cap : ℕ) :=
  (splitImage (S.layer base out X.roster) S.degree S.hosts S.c S.r S.b S.M D cap 0).length+
  ((S.narrow base).base-(S.header base).origin)+(S.castImage (w:=0) base).length+
  ((S.readers base).stop-(S.readers base).origin)+((S.last base).scratch-(S.last base).base)

def operationCount (S : StencilBook) (X : Sources) :=
  64+4*S.r+S.r*(2*(25+56*S.degree)+4)+2*Stencil.count S.r (S.degree+S.degree)*(S.readWork X+11)

theorem paid_time (S : StencilBook) (X : Sources) (base out f B g : ℕ) :
    Padded.paidTime S X base out f B g≤10*S.literalWords base out X (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)+
      (1+S.rows)*S.operationCount X := by
  let T:=(S.last base).tabs
  let field:=((S.readers base).inputs (S.inputs X base out g)).field
  let p:=S.chosen base out X.roster
  have op:=Stencil.assembly_work T field (S.readWork X) (S.read_work X base out g)
  change (Stencil.assembly T field).work ≤ 1 + Stencil.count S.r (S.degree+S.degree) * (S.readWork X+11) at op
  have pass:=clock_price p S.hosts (2^S.c) S.M S.r
  have n:=Nat.mul_le_mul_left (S.rows*2) op
  dsimp only [Padded.paidTime,splitTime,scalarTime,Stencil.time,Stencil.cost,operationCount,literalWords]
  change _+clock (passes p S.hosts (2^S.c) S.M S.r)+_+(_+_+(4+S.rows*(2*(Stencil.assembly T field).work+4)+(4+44*S.rows)))≤_
  change clock (passes p S.hosts (2^S.c) S.M S.r)≤4+S.r*(4+S.rows*(2*(25+56*S.degree)+4)) at pass
  have lastChart : Stencil.lastChart (S.readers base) (S.degree+S.degree) S.t = S.last base := rfl
  rw [lastChart]
  nlinarith only [pass,n,Nat.zero_le ((S.r*(2*(25+56*S.degree)+4))),Nat.zero_le (4*S.r*S.rows),
    Nat.zero_le (2*Stencil.count S.r (S.degree+S.degree)*(S.readWork X+11))]

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

end OAI
