import OAI.Hierarchy.DescentMaterialTariffNumbers
import OAI.Hierarchy.DescentSelectedDonorRateNumbers

namespace OAI
/-! # An age rate for the fifteen-field emitter, independent of its host and group populations -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentHostDegree DescentHaloWalkRAM
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

structure MaterialPoint (t g Dmax : ℕ) where
  age : ℕ
  degree : ℕ
  cap : ℕ
  deg : degree≤Dmax
  capacity : cap≤2^(8+g*((t+1)*age))

theorem material_rates (G : PoweredGadget F) (t f gain reset : ℕ) :
    ∃rate : ℕ,∀J D cap : ℕ,D≤ maximumDegree t →
      cap≤2^(8+capRate G t gain*((t+1)*J)) →
      let k:=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)
      MaterialProgram.materialFactor D (2^k) (15*(2^k*cap*11)) (donorAmount k D cap G.b G.C G.k) ≤ scale J rate := by
  let I:=MaterialPoint t (capRate G t gain) (maximumDegree t)
  let age : I→ℕ:=MaterialPoint.age
  let k:=fun x:I=>groupBits t (age x) (hostRate t reset) (capRate G t gain) (cutRate t f gain)
  let num:=AgeBound.const age
  have table (func : ℕ→ℕ) : AgeBound age (fun x:I=>func x.degree) := by
    apply (num (∑v : Fin (maximumDegree t+1),func v.val)).mono
    intro x
    let j : Fin (maximumDegree t+1):=⟨x.degree,Nat.lt_succ_of_le x.deg⟩
    exact Finset.single_le_sum (f:=fun v:Fin (maximumDegree t+1)=>func v.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
  have radix : AgeBound age (fun x=>2^(k x)):=AgeBound.radix t (hostRate t reset) (capRate G t gain) (cutRate t f gain)
  have caps : AgeBound age (fun x:I=>x.cap):=AgeBound.dated_cap (i:=fun x=>(t+1)*age x)
    (fun _=>le_rfl) (fun x=>x.capacity)
  have sheets:= (num 15).mul ((radix.mul caps).mul (num 11))
  let rates:=donorRates G t f gain reset
  have units : AgeBound age (fun x:I=>donorAmount (k x) x.degree x.cap G.b G.C G.k):=
    ⟨rates.amount,fun x=>(rates.bounds (age x) x.degree x.cap x.deg x.capacity).2⟩
  let col {f : I→ℕ} (c : AgeBound age f) : AgeBound age (fun x=>4+10*f x+7*(15*(f x+1))) :=
    ((num 4).add ((num 10).mul c)).add ((num 7).mul ((num 15).mul (c.add (num 1))))
  have maps:=((col (((num 2).mul radix).mul (num 2))).add (col (num 1))).add (col ((table breadth).add (num 1)))
  have pages:=sheets.mul (num (1+(2*1+1)))
  have installs:=((num 4).add ((num 10).mul pages)).add ((num 4).add (sheets.mul (num (4+44))))
  have sheetPrice:=installs.add ((num 7).mul (((num 15).mul (pages.add (num 1))).add
    ((num 15).add (sheets.mul (num (11+4*20))))))
  have overlap:=(num 2048).mul ((((((num 4).mul units).mul radix).add (num 3)).add sheets).add sheets |>.add (num 1))
  have h:=(((((table MaterialProgram.priorFactor).add (table MaterialProgram.chartFactor)).add
    (table MaterialProgram.joinFactor)).add sheetPrice).add maps).add overlap
  obtain ⟨r,hr⟩:=h
  exact ⟨r,fun J D cap hd hc=>hr (⟨J,D,cap,hd,hc⟩:I)⟩

def materialRate (G : PoweredGadget F) (t f g reset : ℕ) := (material_rates G t f g reset).choose

end
end Hierarchy.DescentSixParty.Chronology

end OAI
