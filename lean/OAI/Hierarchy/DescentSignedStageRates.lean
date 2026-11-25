import OAI.Hierarchy.DescentSignedStageFormat
import OAI.Hierarchy.DescentSignedFeedPolynomial
import OAI.Hierarchy.DescentDonorExponentBounds

namespace OAI
/-! # Uniform packing and signed instruction rates at every ordinary date -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree DescentHaloWalkRAM
open scoped BigOperators

/-- Apply a fixed finite table to the old degree. Its entire cost is independent of the age. -/
private theorem finite_degree {ι : Type*} (age degree : ι→ℕ) (D : ℕ)
    (bounded : ∀x,degree x≤D) (f : ℕ→ℕ) : AgeBound age (fun x=>f (degree x)) := by
  apply (AgeBound.const age (∑j : Fin (D+1),f j.val)).mono
  intro x
  let j : Fin (D+1):=⟨degree x,Nat.lt_succ_of_le (bounded x)⟩
  exact Finset.single_le_sum (f := fun i : Fin (D + 1) => f i.val)
    (fun i _ => Nat.zero_le (f i.val)) (Finset.mem_univ j)

private structure Point (t gain Dmax work : ℕ) where
  age : ℕ
  degree : ℕ
  cap : ℕ
  snippets : ℕ
  priorHosts : ℕ
  hosts : ℕ
  groups : ℕ
  payload : ℕ
  degree_bound : degree≤Dmax
  cap_bound : cap≤2^(8+gain*((t+1)*age))
  snippet_bound : snippets ≤ scale age work

/-- All the uniform constants are chosen before the precision, the physical rows, and the path. -/
theorem uniform (t host gain cut Dmax b C pad work : ℕ) :
    ∃ a e : ℕ, ∀ J D cap K H H' groups payload : ℕ,
      D≤Dmax → cap≤2^(8+gain*((t+1)*J)) → K ≤ scale J work →
      let k:=groupBits t J host gain cut
      let q : SignedStage:=⟨k,D,cap,ordinaryDegree D,2^gainExponent 20 D*b*cap,H,H',groups,b,C,pad⟩
      q.unit ≤ scale J a ∧ (q.format payload).feedFactor K ≤ scale J e := by
  let I:=Point t gain Dmax work
  let age : I→ℕ:=Point.age
  let k:=fun x:I=>groupBits t (age x) host gain cut
  let q:=fun x:I=>(⟨k x,x.degree,x.cap,ordinaryDegree x.degree,2^gainExponent 20 x.degree*b*x.cap,
    x.priorHosts,x.hosts,x.groups,b,C,pad⟩ : SignedStage)
  let numeral:=AgeBound.const age
  have rad : AgeBound age (fun x=>2^(k x)):=AgeBound.radix t host gain cut
  have old : AgeBound age (fun x:I=>x.cap):=AgeBound.dated_cap (i:=fun x=>(t+1)*age x)
    (fun _=>le_rfl) (fun x=>x.cap_bound)
  have table:=finite_degree age (fun x:I=>x.degree) Dmax (fun x=>x.degree_bound)
  have newCap : AgeBound age (fun x=>(q x).newCap):=
    ((table (fun d=>2^gainExponent 20 d)).mul (numeral b)).mul old
  have reach:=table breadth
  have slots:=table (fun d=>2^packExponent 20 d+2)
  have blocks2 : AgeBound age (fun x=>2^(k x+1)):=by simpa only [pow_succ] using rad.mul (numeral 2)
  have low : AgeBound age (fun x=>(q x).lowSites):=blocks2.mul slots
  have resident : AgeBound age (fun x=>(q x).residentSlots):=(rad.mul old).mul (numeral 11)
  have tickets : AgeBound age (fun x=>(q x).tickets):=(reach.add (numeral 1)).mul resident
  have raw : AgeBound age (fun x=>(q x).rawAlphabet):=
    (((((reach.add (numeral 1)).add low).add ((reach.mul reach).mul low)).add tickets).add
      (newCap.add (numeral 1))).add (numeral 2)
  have donors : AgeBound age (fun x=>(q x).donorUnits):=
    (old.mul (numeral b)).maximum (numeral (C+1+pad))
  have width : AgeBound age (fun x=>(q x).fieldBits):=
    (((raw.add ((table ordinaryDegree).add (numeral 2))).add (((numeral 2).mul newCap).add (numeral 2))).add
      (donors.add (numeral 1))).clog
  have totalWords:=(((((numeral 1).add reach).add low).add tickets).add newCap).add width
  have book : AgeBound age (fun x=>(q x).template.feedUnit):=
    ((numeral 128).mul (totalWords.pow 4)).mono
      (fun x=>(q x).template.feedUnit_polynomial)
  have amount : AgeBound age (fun x=>(q x).unit):=book.maximum ((width.mul rad).add width)
  have expr : AgeBound age (fun x:I=>x.snippets):=⟨work,fun x=>x.snippet_bound⟩
  have degree:=table id
  have totalWork:=((((((numeral 1).add rad).add degree).add resident).add low).add newCap).add expr
  have factor : AgeBound age (fun x=>((q x).format x.payload).feedFactor x.snippets):=
    ((numeral (10^12)).mul (totalWork.pow 48)).mono (fun x=>((q x).format x.payload).feedFactor_polynomial x.snippets)
  obtain ⟨a,packing⟩:=amount
  obtain ⟨e,price⟩:=factor
  refine ⟨a,e,?_⟩
  intro J D cap K H H' groups payload hd hc hw
  let x : I:=⟨J,D,cap,K,H,H',groups,payload,hd,hc,hw⟩
  exact ⟨packing x,price x⟩

end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
