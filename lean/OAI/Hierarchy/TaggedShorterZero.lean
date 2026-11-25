import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket
import OAI.ThreeFlat.Diagonal.TraceLocalNetwork
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Ordinary switches for a bounded zero-scale group

Compare the reported global endpoints to the physical slots once per candidate.
Each payload column reads the resulting two flags and the low-width address
comparison. Vacancies carry width zero, so their data have no restrictions.
-/

noncomputable section
namespace Hierarchy.TaggedShorterZero
open ThreeFlat Routing Diagonal TraceWords TracePair
open Computability.VPVNP.BurstRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open scoped Classical BigOperators

variable {L D b d w : ℕ} {F : Type*}

abbrev MatchPins (L D : ℕ) := Fin L × Bool × Fin D
abbrev Checks (L D w : ℕ) := Fin L × Fin D × Fin D × Fin w
abbrev Pin (L D b d w : ℕ) :=
  (Fin L × ((Bool × Fin d) ⊕ Fin b)) ⊕ (Bool × Fin D × Fin w)
abbrev All (L D b d w : ℕ) := Pin L D b d w ⊕ MatchPins L D
abbrev Gates (L D w : ℕ) := MatchPins L D ⊕ Checks L D w

def pins (ends : Fin L → Bool → Word d) (width : Fin L → Word b)
    (data : Bool → Fin D → Fin w → Bool) : Pin L D b d w → Bool :=
  Sum.elim (fun x => x.2.elim (fun t=>bits (ends x.1 t.1) t.2) (bits (width x.1)))
    (fun t => data t.1 t.2.1 t.2.2)

private def matchTest (labels : Bool → Fin D → Word d) (k : MatchPins L D) : Expr (All L D b d w) :=
  same (.input (.inr k)) (sameWord (fun i => .input (.inl (.inl (k.1,.inl (k.2.1,i)))))
    (fun i => .const (bits (labels k.2.1 k.2.2) i)))

private def dataTest (hw : w≤2^b) (k : Checks L D w) : Expr (All L D b d w) :=
  let i:=k.1
  let src:=k.2.1
  let dst:=k.2.2.1
  let j:=k.2.2.2
  let used := lessWord (fun n=>.const (bits (j.castLE hw) n)) (fun n=>.input (.inl (.inl (i,.inr n))))
  .or (.not (.and (.input (.inr (i,false,src))) (.and (.input (.inr (i,true,dst))) used)))
    (same (.input (.inl (.inr (false,src,j)))) (.input (.inl (.inr (true,dst,j)))))

def expression (labels : Bool → Fin D → Word d) (hw : w≤2^b) : Gates L D w → Expr (All L D b d w) :=
  Sum.elim (matchTest labels) (dataTest hw)

private def part [Zero F] [One F] (labels : Bool → Fin D → Word d) (hw : w≤2^b) (g : Gates L D w) :
    BitNetwork F (Fintype.card (All L D b d w)) :=
  TraceCircuit.localNetwork (fun _ : Fin 1 => formulaPacket (expression labels hw g)) (Fintype.equivFin _)
    (fun _ z=> if z then 1 else 0)

def network [Zero F] [One F] (labels : Bool → Fin D → Word d) (hw : w≤2^b) :
    BitNetwork F (Fintype.card (Pin L D b d w)) := TypedWiring.glue (part labels hw) (fun _ i=>i)

private def matchBits (labels : Bool → Fin D → Word d) (ends : Fin L → Bool → Word d) :
    MatchPins L D → Bool := fun k => decide (ends k.1 k.2.1=labels k.2.1 k.2.2)

private theorem match_at (labels : Bool → Fin D → Word d) (ends : Fin L → Bool → Word d)
    (width : Fin L → Word b) (data : Bool → Fin D → Fin w → Bool) (y : MatchPins L D → Bool) (k : MatchPins L D) :
    (matchTest labels k).eval (Sum.elim (pins ends width data) y) = true ↔ y k=matchBits labels ends k := by
  have seen := sameWord_at (a:=ends k.1 k.2.1) (b:=labels k.2.1 k.2.2)
    (fun i => Expr.input (.inl (.inl (k.1,.inl (k.2.1,i))) : All L D b d w))
    (fun i => Expr.const (bits (labels k.2.1 k.2.2) i)) (Sum.elim (pins ends width data) y)
    (fun _ => rfl) (fun _ => rfl)
  rw [matchTest,same_true]
  cases seenBool : (sameWord _ _).eval (Sum.elim (pins ends width data) y) <;>
    simp_all [matchBits,Expr.eval]

private theorem data_at (labels : Bool → Fin D → Word d) (hw : w≤2^b) (ends : Fin L → Bool → Word d)
    (width : Fin L → Word b) (data : Bool → Fin D → Fin w → Bool) (k : Checks L D w) :
    (dataTest (d:=d) hw k).eval (Sum.elim (pins ends width data) (matchBits labels ends)) = true ↔
      ends k.1 false=labels false k.2.1 → ends k.1 true=labels true k.2.2.1 →
      k.2.2.2.val<(width k.1).val → data false k.2.1 k.2.2.2=data true k.2.2.1 k.2.2.2 := by
  have used := lessWord_at (fun n=>Expr.const (bits (k.2.2.2.castLE hw) n))
    (fun n=>Expr.input (.inl (.inl (k.1,.inr n)) : All L D b d w))
    (Sum.elim (pins ends width data) (matchBits labels ends)) (k.2.2.2.castLE hw) (width k.1)
    (fun _ => rfl) (fun _ => rfl)
  let pin := Sum.elim (pins ends width data) (matchBits labels ends)
  let live : Expr (All L D b d w) := lessWord (fun n=>.const (bits (k.2.2.2.castLE hw) n))
    (fun n=>.input (.inl (.inl (k.1,.inr n))))
  let equal : Expr (All L D b d w) := same (.input (.inl (.inr (false,k.2.1,k.2.2.2))))
    (.input (.inl (.inr (true,k.2.2.1,k.2.2.2))))
  have widthAt : live.eval pin=decide (k.2.2.2.val<(width k.1).val) := used
  have equalAt : equal.eval pin=true ↔ data false k.2.1 k.2.2.2=data true k.2.2.1 k.2.2.2 := by
    exact same_true _ _ pin
  change ((!((decide (ends k.1 false=labels false k.2.1)) &&
    ((decide (ends k.1 true=labels true k.2.2.1)) && live.eval pin))) || equal.eval pin)=true ↔ _
  rw [widthAt]
  by_cases h₁ : ends k.1 false=labels false k.2.1 <;> by_cases h₂ : ends k.1 true=labels true k.2.2.1 <;>
    by_cases h₃ : k.2.2.2.val<(width k.1).val <;> simp [h₁,h₂,h₃,equalAt]

/-- This relation is exactly word equality on every active prefix. Repeated
payload values and repeated uses of a site remain distinct pin reads. -/
def Connected (labels : Bool → Fin D → Word d) (ends : Fin L → Bool → Word d) (width : Fin L → Word b)
    (data : Bool → Fin D → Fin w → Bool) :=
  ∀ i src dst j, ends i false=labels false src → ends i true=labels true dst → j.val<(width i).val →
    data false src j=data true dst j

theorem checks [CommRing F] (labels : Bool → Fin D → Word d) (hw : w≤2^b) (ends : Fin L → Bool → Word d)
    (width : Fin L → Word b) (data : Bool → Fin D → Fin w → Bool) :
    TypedWiring.value (network (F:=F) labels hw) (pins ends width data) =
      if Connected labels ends width data then 1 else 0 := by
  have selected (y : MatchPins L D → Bool) :
      (∀ g, (expression labels hw g).eval (Sum.elim (pins ends width data) y)=true) ↔
        y=matchBits labels ends ∧ Connected labels ends width data := by
    constructor
    · intro h
      have hy : y=matchBits labels ends := funext fun k => (match_at ..).mp (h (.inl k))
      refine ⟨hy,?_⟩
      subst y
      intro i s t j
      exact (data_at labels hw ends width data (i,s,t,j)).mp (h (.inr (i,s,t,j)))
    · rintro ⟨rfl,connected⟩ (k|⟨i,s,t,j⟩)
      · exact (match_at ..).mpr rfl
      · exact (data_at ..).mpr (connected i s t j)
  have piece (g : Gates L D w) (x : All L D b d w → Bool) :
      TypedWiring.value (part (F:=F) labels hw g) x = if (expression labels hw g).eval x then 1 else 0 := by
    simp [part,TypedWiring.value,TraceCircuit.localNetwork_eval,formulaPacket_eval,Function.comp_def]
  rw [network,TypedWiring.glue_value]
  simp_rw [piece,Fintype.prod_boole,selected,ite_and]
  simp

theorem cells [Zero F] [One F] (labels : Bool → Fin D → Word d) (hw : w≤2^b) :
    (network (F:=F) (L:=L) labels hw).cells ≤
      (2*L*D)*(100*d+100) + (L*D*D*w)*(100*b+100) := by
  have matchBound (k : MatchPins L D) : (part (F:=F) (b:=b) (w:=w) labels hw (.inl k)).cells ≤ 100*d+100 := by
    have ord := sameWord_size_le (fun i : Fin d => Expr.input (.inl (.inl (k.1,.inl (k.2.1,i))) : All L D b d w))
      (fun i=>Expr.const (bits (labels k.2.1 k.2.2) i)) (s:=1) (t:=1) (fun _=>le_rfl) (fun _=>le_rfl)
    have packet := formulaPacket_size_le (matchTest (b:=b) (w:=w) labels k)
    simp only [matchTest,same_size,Expr.size] at packet
    simp only [part,TraceCircuit.localNetwork_cells,Fin.sum_univ_one,expression,Sum.elim_inl,matchTest]
    omega
  have dataBound (k : Checks L D w) : (part (F:=F) labels hw (.inr k)).cells ≤ 100*b+100 := by
    have ord := lessWord_size (fun n : Fin b => Expr.const (bits (k.2.2.2.castLE hw) n))
      (fun n=>Expr.input (.inl (.inl (k.1,.inr n)) : All L D b d w)) (s:=1) (fun _=>le_rfl) (fun _=>le_rfl)
    have packet := formulaPacket_size_le (dataTest (d:=d) hw k)
    simp only [dataTest,same_size,Expr.size] at packet
    simp only [part,TraceCircuit.localNetwork_cells,Fin.sum_univ_one,expression,Sum.elim_inr,dataTest]
    omega
  rw [network,TypedWiring.glue_cells,Fintype.sum_sum_type]
  apply Nat.add_le_add
  · simpa [MatchPins,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using
      Finset.sum_le_sum (s:=Finset.univ) (fun k _=>matchBound k)
  · simpa [Checks,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using
      Finset.sum_le_sum (s:=Finset.univ) (fun k _=>dataBound k)


/-- Local formula packets allocate one internal wire for each formula gate.
The scalar output check adds a cell. The only other internal wires are the
two endpoint match tables shared by the payload checks. -/
theorem internal [Zero F] [One F] (labels : Bool → Fin D → Word d) (hw : w≤2^b) :
    (network (F:=F) (L:=L) labels hw).internal ≤ 2*L*D+(network (F:=F) (L:=L) labels hw).cells := by
  have each (g : Gates L D w) : (part (F:=F) labels hw g).internal ≤ (part (F:=F) labels hw g).cells := by
    apply Nat.le_add_right
  rw [network,TypedWiring.glue_internal,TypedWiring.glue_cells]
  have count : Fintype.card (MatchPins L D)=2*L*D := by
    simp [MatchPins,Nat.mul_comm,Nat.mul_left_comm]
  rw [count]
  exact Nat.add_le_add_left (Finset.sum_le_sum (fun g _=>each g)) _

end Hierarchy.TaggedShorterZero

end
end OAI
