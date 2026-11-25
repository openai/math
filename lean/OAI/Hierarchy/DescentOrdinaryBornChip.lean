import OAI.Hierarchy.DescentDonorEncodedBits
import OAI.Hierarchy.DescentOrdinaryBornChart

namespace OAI
/-! # Reading the measured donor from the packed original chip -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentRawCablePanel DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable (s : DepotRAM.Shape)
def chipDonor (c : Cell (DepotRAM.outputBits s)) (xt : Fin (s.blocks*s.cap)) : Donor 3 s.names s.widths :=
  unpackDonor (((encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm c) xt)

private theorem blankDigits (a n : ℕ) : (encode a n).symm (0:Cell (a*n))=fun _=>0 :=by
  apply (encode a n).symm_apply_eq.mpr
  apply Fin.ext
  simp [encode]

private theorem blankPair (a b : ℕ) : (pair a b).symm 0=(0,0) :=by
  apply (pair a b).symm_apply_eq.mpr
  apply Fin.ext
  simp [pair,finProdFinEquiv_apply_val]

private theorem zeroFlag (l a c : ℕ) :
    (unpackDonor (loc:=l) (a:=a) (c:=c) (0 : Cell (bundleBits l a c))).first=false :=by
  have castZero : (finCongr (congrArg (2^·) (shapeWidth l a c))).symm (0:Cell (bundleBits l a c))=
      (0:Cell (4+(l+1+a)*5+c*10)):=Fin.ext rfl
  simp only [unpackDonor,castZero,blankPair,blankDigits]
  decide

theorem first_zero (xt : Fin (s.blocks*s.cap)) : (chipDonor s 0 xt).first=false :=by
  let width:=bundleBits 3 s.names s.widths
  let count:=s.blocks*s.cap
  have empty : ((encode width count).symm (0:Cell (width*count))) xt=0:=
    congrFun (blankDigits width count) xt
  change (unpackDonor (loc:=3) (a:=s.names) (c:=s.widths) (((encode width count).symm 0) xt)).first=false
  exact (congrArg (fun q : Cell width=>(unpackDonor (loc:=3) (a:=s.names) (c:=s.widths) q).first) empty).trans
    (zeroFlag 3 s.names s.widths)

theorem donor_at (c : Cell (DepotRAM.outputBits s)) (xt : Fin (s.blocks*s.cap)) (d : Donor 3 s.names s.widths)
    (printed : ((encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm c) xt=packDonor d) :
    chipDonor s c xt=d:=by simp [chipDonor,printed]


namespace Chart
variable (B : Chart)
def format : DepotRAM.Shape:=⟨B.blocks,0,B.cap,0,B.names,B.widths⟩
end Chart
end
end Hierarchy.DescentOrdinaryBorn

end OAI
