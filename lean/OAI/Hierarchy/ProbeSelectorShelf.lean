import OAI.Hierarchy.ProbeVariableHistogram
import OAI.Hierarchy.ProbeVariableUnary

namespace OAI
/-! # A fixed selector controller with external binary histogram fields -/

noncomputable section
namespace Hierarchy.Probe.SelectorShelf
open ThreeFlat Diagonal TraceCircuit MotifOuterTerms MotifSelectorChecks Routing
open scoped BigOperators Classical

variable {F : Type*} [CommRing F] {r H b d : ℕ}

def counterWires (a : Fin H) : Fin (Fintype.card (VariableUnary.Pins r d)) → BitSource (H*r) (r*b+H*d) :=
  fun j=>match (Fintype.equivFin (VariableUnary.Pins r d)).symm j with
    | .inl i=>.hidden (finProdFinEquiv (a,i))
    | .inr t=>.pin (Fin.natAdd _ (finProdFinEquiv (a,t)))

def rootWires : Fin (r*b+H*r) → BitSource (H*r) (r*b+H*d) :=
  Fin.append (fun i=>.pin (i.castAdd _)) (fun j=>.hidden j)

def part (F : Type*) [CommRing F] (positive : 0<H) (r b d : ℕ) : Option (Fin H) → Component F (H*r) (r*b+H*d)
  | none=>⟨_,VariableHistogram.network F positive r b,rootWires⟩
  | some a=>⟨_,VariableUnary.network F r d,counterWires a⟩

def network (F : Type*) [CommRing F] (positive : 0<H) (r b d : ℕ) : BitNetwork F (r*b+H*d) :=
  BitNetwork.glue (fun i=>(part F positive r b d i).net) (fun i=>(part F positive r b d i).wire)

def pins (z : Fin r→Fin b → Bool) (fields : Fin H→Fin d → Bool) :=
  Fin.append (blocks r b z) (blocks H d fields)

private theorem root_at (z : Fin r→Fin b → Bool) (fields : Fin H→Fin d → Bool) (y : Fin H→Fin r → Bool) :
    (fun j=>(rootWires j).read (blocks H r y) (pins z fields))=VariableHistogram.pins z y := by
  funext j
  refine Fin.addCases (fun _=>?_) (fun _=>?_) j <;>
    simp [rootWires,pins,VariableHistogram.pins,BitSource.read,-Fin.natAdd_eq_addNat]

private theorem counter_at (z : Fin r→Fin b → Bool) (fields : Fin H→Fin d → Bool) (y : Fin H→Fin r → Bool)
    (a : Fin H) :
    (fun j=>(counterWires a j).read (blocks H r y) (pins z fields))=
      (Sum.elim (y a) (fields a)) ∘ (Fintype.equivFin _).symm := by
  funext j
  cases eqn:(Fintype.equivFin (VariableUnary.Pins r d)).symm j with
  | inl i=>simp [counterWires,eqn,BitSource.read,blocks_at]
  | inr t=>simp [counterWires,eqn,BitSource.read,pins,blocks_at,-Fin.natAdd_eq_addNat]

def bits (hist : Histogram (Fin H) r) (d : ℕ) (a : Fin H) (i : Fin d) := (hist.val a).val.testBit i.val

/-- No unary target, counter, or inactive branch is supplied as advice. All
unary bits are ordinary hidden wires of the same one fixed network. -/
theorem eval (positive : 0<H) (z : Fin r→Fin b → Bool) (fields : Fin H→Fin d → Bool) :
    (network F positive r b d).eval (pins z fields)=
      if (∀i,NativeHistogram.valid H (z i)) ∧ fields=bits (histogram (fun i=>NativeHistogram.letter positive (z i))) d
        then 1 else 0 := by
  let hist:=histogram (fun i=>NativeHistogram.letter positive (z i))
  let check (y : Fin H→Fin r → Bool) := ∏a,TypedWiring.value (VariableUnary.network F r d) (Sum.elim (y a) (fields a))
  rw [network,BitNetwork.glue_eval,←(blocks H r).sum_comp]
  have each (y : Fin H→Fin r → Bool) :
      (∏i,((part F positive r b d i).net).eval (fun t=>((part F positive r b d i).wire t).read
        (blocks H r y) (pins z fields)))=
      (if (∀i,NativeHistogram.valid H (z i)) ∧ y=VariableHistogram.stream hist then (1:F) else 0)*check y := by
    rw [Fintype.prod_option]
    apply congrArg₂ (·*·)
    · change (VariableHistogram.network F positive r b).eval
        (fun t => (rootWires t).read (blocks H r y) (pins z fields)) = _
      rw [root_at,VariableHistogram.eval]
    · apply Finset.prod_congr rfl
      intro a _
      exact congrArg (VariableUnary.network F r d).eval (counter_at z fields y a)
  simp only [each]
  rw [Fintype.sum_eq_single (VariableHistogram.stream hist)]
  · have output : check (VariableHistogram.stream hist)=if fields=bits hist d then 1 else 0 := by
      simp only [check,VariableHistogram.stream,VariableUnary.eval_count,Fintype.prod_boole]
      congr 1
      exact propext ⟨fun s=>funext s,fun s a=>congrFun s a⟩
    rw [output]
    by_cases ok : ∀ i, NativeHistogram.valid H (z i) <;> simp [hist,ok]
  · intro y diff
    simp [diff]

theorem cost (positive : 0<H) :
    (network F positive r b d).cells+(network F positive r b d).internal ≤
      (r*(2^(b+H)*(b+H+1))+r*H+r*2^(b+H)+128000*H*(r+1)*(Nat.log 2 (r+1)+2)^3)+
        H*r+H*((r+1)*d) := by
  have base := VariableHistogram.cost (F:=F) (r:=r) (b:=b) positive
  calc
    _ = ((VariableHistogram.network F positive r b).cells +
          (VariableHistogram.network F positive r b).internal) + H*r +
        H*((VariableUnary.network F r d).cells+(VariableUnary.network F r d).internal) := by
      simp [network,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_option,
        part]; ring
    _ ≤ _ := by
      rw [VariableUnary.size]
      exact Nat.add_le_add_right (Nat.add_le_add_right base (H*r)) (H*((r+1)*d))

private theorem bits_inj (a b : Histogram (Fin H) r) (d : ℕ) (room : r<2^d)
    (agree : bits a d=bits b d) : a=b := by
  apply Subtype.ext
  funext h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases small : j<d
  · exact congrFun (congrFun agree h) ⟨j,small⟩
  · have cap:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt small)
    have left := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (a.val h).isLt) (room.trans_le cap)
    have right := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (b.val h).isLt) (room.trans_le cap)
    rw [Nat.testBit_eq_false_of_lt left,Nat.testBit_eq_false_of_lt right]

/-- One fixed circuit per batch capacity and finite alphabet agrees with the
earlier per-histogram network on the target's actual observed binary pins. -/
theorem fixed_target (positive : 0<H) (z : Fin r→Fin b → Bool) (target : Histogram (Fin H) r)
    (room : r<2^d) :
    (network F positive r b d).eval (pins z (bits target d))=
      (NativeHistogram.network F positive b target).eval (blocks r b z) := by
  rw [eval,NativeHistogram.eval]
  congr 1
  apply propext
  refine and_congr_right fun _=>⟨bits_inj _ _ d room,fun e=>congrArg (fun t=>bits t d) e⟩

end Hierarchy.Probe.SelectorShelf
end

end OAI
