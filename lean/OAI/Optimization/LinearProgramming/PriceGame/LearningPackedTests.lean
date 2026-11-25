import OAI.Optimization.LinearProgramming.PriceGame.LearningAddressMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlWire

/-! # Reading the observations from packed trial data

Duplicate goods may have different prices and the same original-variable address. The
feature retains the original addresses; the prices are always taken from the indicated
level of the probe. Ancestor prices are used only for a nonempty pivot.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram Control Control.Wire States.Mass
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

/-- Root addresses of the positive and optional negative variables, and the price threshold. -/
abbrev PackedTest := (ℕ × Option ℕ) × ℚ

def packedTestCode : PackedTest → List Bool :=
  prodCode (prodCode Nat.bits (optionCode Nat.bits)) ratCode

def packTest {N} (t : Test N) : PackedTest :=
  ((t.feature.1.val,t.feature.2.map Fin.val),t.threshold)

def atAddress {α : Type} (d : α) (xs : List α) (i : ℕ) := (xs.drop i).headD d

def priceAt (p : PackedProbe) (i : ℕ) := atAddress 0 p.prices i

def ancestorAt (p : PackedProbe) (k i : ℕ) := atAddress 0 (atAddress [] p.history k) i

def oriented (b : Bool) (q : ℚ) : ℚ := if b then q else -q

def pairPacked (e : PackedExpert) (p : PackedProbe) (i j : ℕ) : PackedTest :=
  ((i >>> e.level,some (j >>> e.level)),oriented e.positive (priceAt p i - priceAt p j))

def outsidePacked (e : PackedExpert) (p : PackedProbe) (i : ℕ) : PackedTest :=
  match e.pivot with
  | none => ((i >>> e.level,none),oriented e.positive (priceAt p i))
  | some (k,j) => ((i >>> e.level,some (j >>> k)),oriented e.positive (priceAt p i - ancestorAt p k j))

def packedTests (e : PackedExpert) (p : PackedProbe) : List PackedTest :=
  if p.level = e.level then
    (e.tuple.map fun i => outsidePacked e p i :: e.tuple.map (pairPacked e p i)).flatten
  else []

private theorem atAddress_pack {α : Type} [Inhabited α] (N k : ℕ) (f : Vertex N k → α) (i : Vertex N k) :
    atAddress default (packTable N k f) (vertexEquivFin N k i).val = f i := by
  simpa [atAddress,lookupTable,List.head?_drop] using lookupTable_pack N k f i

private theorem priceAt_pack {N} (p : Probe N) (i : Vertex N p.level) :
    priceAt (packProbe p) (vertexEquivFin N p.level i).val = p.prices i :=
  atAddress_pack _ _ _ _

private theorem ancestorAt_pack {N} (p : Probe N) {k : ℕ} (hk : k < p.level) (j : Vertex N k) :
    ancestorAt (packProbe p) k (vertexEquivFin N k j).val = p.history k j := by
  simp only [ancestorAt,packProbe,packHistory,atAddress,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_ofFn,hk,↓reduceDIte,Option.getD_some]
  exact lookupTable_pack _ _ _ _

private theorem pairPacked_pack {N} (e : Expert N) (p : Probe N) (h : p.level = e.skeleton.level)
    (j j' : Fin 64) :
    pairPacked (packExpert e) (packProbe p) (vertexEquivFin N _ (e.skeleton.tuple j)).val
      (vertexEquivFin N _ (e.skeleton.tuple j')).val = packTest (e.skeleton.pairTest (h ▸ p.prices) j j') := by
  obtain ⟨l,y,hist⟩ := p
  change l = e.skeleton.level at h; subst l
  simp only [pairPacked, packExpert, root_address, packTest, Skeleton.pairTest,Skeleton.origin,
    Option.map, Prod.mk.injEq,true_and]
  rw [priceAt_pack,priceAt_pack]; rfl

private theorem outsidePacked_pack {N} (e : Expert N) (p : Probe N) (h : p.level = e.skeleton.level)
    (j : Fin 64) :
    outsidePacked (packExpert e) (packProbe p) (vertexEquivFin N _ (e.skeleton.tuple j)).val =
      packTest (e.skeleton.outsideTest p.history (h ▸ p.prices) j) := by
  obtain ⟨l,y,hist⟩ := p
  change l = e.skeleton.level at h; subst l
  let probe : Probe N := ⟨e.skeleton.level,y,hist⟩
  have hprice := priceAt_pack probe (e.skeleton.tuple j)
  change priceAt (packProbe ⟨e.skeleton.level,y,hist⟩)
    (vertexEquivFin N e.skeleton.level (e.skeleton.tuple j)).val = y (e.skeleton.tuple j) at hprice
  cases hp : e.skeleton.pivot with
  | none => simp [outsidePacked,packExpert,hp,root_address,hprice,packTest,Skeleton.outsideTest,Skeleton.origin,oriented,Skeleton.signed]
  | some v =>
    obtain ⟨k,i⟩ := v
    have hanc := ancestorAt_pack probe k.isLt i
    change ancestorAt (packProbe ⟨e.skeleton.level,y,hist⟩) _ _ = hist k i at hanc
    simp [outsidePacked,packExpert,hp,root_address,hprice,hanc,
      packTest,Skeleton.outsideTest,Skeleton.origin,oriented,Skeleton.signed]

/-- The wire extractor recovers the source test list in its original order. -/
theorem packedTests_correct {N} (e : Expert N) (p : Probe N) :
    packedTests (packExpert e) (packProbe p) = (e.skeleton.testsAt p).map packTest := by
  by_cases h : p.level = e.skeleton.level
  · have hh : (packProbe p).level = (packExpert e).level := h
    rw [packedTests,ite_eq_left hh,Skeleton.testsAt,dite_eq_left h,List.map_flatten]
    let addr (j : Fin 64) := (vertexEquivFin N e.skeleton.level (e.skeleton.tuple j)).val
    change ((List.ofFn addr).map (fun i => outsidePacked (packExpert e) (packProbe p) i ::
      (List.ofFn addr).map (pairPacked (packExpert e) (packProbe p) i))).flatten = _
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply congrArg List.ofFn; funext j
    simp only [Function.comp_apply,List.map_cons,List.map_ofFn,addr]
    rw [outsidePacked_pack e p h j]
    apply congrArg (List.cons _)
    apply congrArg List.ofFn; funext j'
    exact pairPacked_pack e p h j j'
  · simp [packedTests,Skeleton.testsAt,packExpert,packProbe,h]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
