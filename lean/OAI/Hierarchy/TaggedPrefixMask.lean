import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.Routing.CompareWord
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Computing the live prefix mask from a binary width -/

noncomputable section
namespace Hierarchy.Tagged.PrefixMask
open ThreeFlat Routing
open scoped Classical BigOperators

abbrev Pin (d w : ℕ) := Fin d ⊕ Fin w
private abbrev Trace (d w : ℕ) := Fin w × Fin (d+1)
private abbrev Gate (d w : ℕ) := Fin w × Option (Option (Fin d))

private def columns {d w : ℕ} (room : w ≤ 2^d) (j : Fin w) : Bits d :=
  (addressEquiv d).symm ⟨j.val,j.isLt.trans_le room⟩

private def wires {d w : ℕ} (g : Gate d w) : Fin 3 → Pin d w ⊕ Trace d w :=
  match g with
  | (j,none) => fun _ => .inr (j,0)
  | (j,some none) => ![.inl (.inr j),.inr (j,Fin.last d),.inr (j,Fin.last d)]
  | (j,some (some i)) => ![.inr (j,i.castSucc),.inl (.inl i),.inr (j,i.succ)]

private def test {d w : ℕ} (room : w ≤ 2^d) (g : Gate d w) (b : Fin 3 → Bool) : Prop :=
  match g with
  | (_,none) => b 0 = false
  | (_,some none) => b 0 = b 1
  | (j,some (some i)) => b 2 = if columns room j i = b 1 then b 0 else b 1

/-- Each cell has one fixed comparator digit. Two read bits and the next
comparison bit therefore suffice for the whole transition. -/
def network (F : Type*) [Zero F] [One F] {d w : ℕ} (room : w ≤ 2^d) :
    BitNetwork F (Fintype.card (Pin d w)) :=
  TypedWiring.glue (fun g : Gate d w => TypedWiring.localTable (P:=Fin 3)
    (fun b => if test room g b then (1:F) else 0)) wires

private def trajectory {d w : ℕ} (room : w ≤ 2^d) (live : Bits d) (u : Trace d w) :=
  prefixLT (columns room u.1) live u.2

def mask {d : ℕ} (w : ℕ) (live : Bits d) : Bits w :=
  fun j => decide (j.val < wordValue live)

private theorem last {d w : ℕ} (room : w ≤ 2^d) (live : Bits d) (j : Fin w) :
    trajectory room live (j,Fin.last d) = mask w live j := by
  change decide (wordValue (columns room j) < wordValue live) = _
  simp [wordValue_addressEquiv,columns,mask]

private theorem valid {d w : ℕ} (room : w ≤ 2^d) (live : Bits d) (flag : Bits w)
    (t : Trace d w → Bool) :
    (∀ g, test room g (fun k => Sum.elim (Sum.elim live flag) t (wires g k))) ↔
      t=trajectory room live ∧ flag=mask w live := by
  constructor
  · intro all
    have unique : t=trajectory room live := by
      funext ⟨j,i⟩
      induction i using Fin.induction with
      | zero => simpa [test,wires,trajectory,prefixLT,prefixValue] using all (j,none)
      | succ i ih =>
        change t (j,i.succ) = prefixLT (columns room j) live i.succ
        rw [prefixLT_step]
        have v := all (j,some (some i))
        change t (j,i.succ) = (if columns room j i = live i then t (j,i.castSucc) else live i) at v
        simpa only [ih,trajectory] using v
    refine ⟨unique,?_⟩
    funext j
    have b := all (j,some none)
    change flag j = t (j,Fin.last d) at b
    rw [b,unique,last]
  · rintro ⟨rfl,rfl⟩ ⟨j,(_ | (_ | i))⟩
    · simp [test,wires,trajectory,prefixLT,prefixValue]
    · change mask w live j = trajectory room live (j,Fin.last d)
      exact (last room live j).symm
    · exact prefixLT_step (columns room j) live i

theorem value {F : Type*} [CommSemiring F] {d w : ℕ} (room : w ≤ 2^d)
    (live : Bits d) (flag : Bits w) :
    TypedWiring.value (network F room) (Sum.elim live flag) =
      if flag=mask w live then 1 else 0 := by
  rw [network,TypedWiring.glue_value]
  simp only [TypedWiring.localTable_value,Fintype.prod_boole,valid,ite_and]
  simp

theorem size (F : Type*) [Zero F] [One F] {d w : ℕ} (room : w ≤ 2^d) :
    (network F room).cells+(network F room).internal ≤ 256*w*(d+1) := by
  simp only [network,TypedWiring.glue_cells,TypedWiring.glue_internal,TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells,TableCompiler.localTableNetwork_internal,
    Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
    Gate,Trace,Fintype.card_prod,Fintype.card_option]
  nlinarith

end Hierarchy.Tagged.PrefixMask

end
end OAI
