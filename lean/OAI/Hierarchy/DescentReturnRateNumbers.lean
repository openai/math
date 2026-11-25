import OAI.Hierarchy.DescentSignedReturnPopulation
import OAI.Hierarchy.DescentSelectedMaterialRates
import OAI.Hierarchy.DescentSignedRateNumbers

namespace OAI
/-! # Branch-independent rates for the material, peer, mark and signed prefix -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentHostDegree DescentHaloWalkRAM
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

def markPrice (D blocks cap : ℕ) := 131072*(breadth D+2)*(blocks*cap*11+1)*(blocks+1)

def publicPeerFee (op degree growth nextDegree : ℕ) :=
  7*(15000*3*(degree+12)^50+300*(growth*nextDegree)+100+800)+
  (4+10*(2*(2*growth+1)))+7*(15*(2*(2*growth+1)+1))+
  (4+growth*(2*op+4))+7*(11+4*op)

def returnPriceWith (op D blocks cap growth oldUnit newUnit mat signed : ℕ) :=
  let common:=MaterialProgram.returnFactor growth oldUnit newUnit
  let ink:=markPrice D blocks cap
  11*mat*common + publicPeerFee op D growth (ordinaryDegree D) +
    (ink*(4*blocks+12)*common+2*ink) + signed*common

theorem return_rates_with (op : ℕ) (G : PoweredGadget F) (t f gain reset : ℕ) :
    ∃rate : ℕ,∀J D cap : ℕ,D≤ maximumDegree t →
      cap≤2^(8+capRate G t gain*((t+1)*J)) →
      let k:=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)
      let growth:=2*(2^hostRate t reset*2^k)
      let oldUnit:=scale J (donorRates G t f gain reset).amount
      let newUnit:=scale J (signedRates G t f gain reset).amount
      returnPriceWith op D (2^k) cap growth oldUnit newUnit (scale J (materialRate G t f gain reset))
        (scale J (signedRates G t f gain reset).controls) ≤ scale J rate := by
  let I:=MaterialPoint t (capRate G t gain) (maximumDegree t)
  let age : I→ℕ:=MaterialPoint.age
  let num:=AgeBound.const age
  have table (func : ℕ→ℕ) : AgeBound age (fun x:I=>func x.degree) := by
    apply (num (∑j : Fin (maximumDegree t+1),func j.val)).mono
    intro x
    let j:Fin (maximumDegree t+1):=⟨x.degree,Nat.lt_succ_of_le x.deg⟩
    exact Finset.single_le_sum (f:=fun j:Fin (maximumDegree t+1)=>func j.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have rate (r : ℕ) : AgeBound age (fun x=>scale (age x) r):=⟨r,fun _=>le_rfl⟩
  have rad:=AgeBound.radix (age:=age) t (hostRate t reset) (capRate G t gain) (cutRate t f gain)
  have caps : AgeBound age (fun x:I=>x.cap):=AgeBound.dated_cap (i:=fun x=>(t+1)*age x)
    (fun _=>le_rfl) (fun x=>x.capacity)
  have growth := (num 2).mul ((num (2^hostRate t reset)).mul rad)
  have u:=rate (donorRates G t f gain reset).amount
  have v:=rate (signedRates G t f gain reset).amount
  have z:=((num 2).add ((num 2).mul ((num 2).add growth))).add
    (((((num 4).mul ((num 2).add growth)).mul (num 2))).mul (u.add v))
  have ink:=(((num 131072).mul ((table breadth).add (num 2))).mul
    (((rad.mul caps).mul (num 11)).add (num 1))).mul (rad.add (num 1))
  have peer₁:=(num 7).mul (((((table (fun d=>15000*3*(d+12)^50)).add
    ((num 300).mul (growth.mul (table ordinaryDegree)))).add (num 100))).add (num 800))
  have edges:=(num 2).mul (((num 2).mul growth).add (num 1))
  have peer:=((peer₁.add ((num 4).add ((num 10).mul edges))).add
    ((num 7).mul ((num 15).mul (edges.add (num 1))))).add ((num 4).add (growth.mul (num (2*op+4))))
  have peers:=peer.add (num (7*(11+4*op)))
  have inks:=((ink.mul (((num 4).mul rad).add (num 12))).mul z).add ((num 2).mul ink)
  have final:=(((((num 11).mul (rate (materialRate G t f gain reset))).mul z).add peers).add inks).add
    ((rate (signedRates G t f gain reset).controls).mul z)
  obtain ⟨r,hr⟩:=final
  exact ⟨r,fun J D cap hd hc=>hr (⟨J,D,cap,hd,hc⟩:I)⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
