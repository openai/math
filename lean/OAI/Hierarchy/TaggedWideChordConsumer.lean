import OAI.Hierarchy.TaggedWideChordAperture
import OAI.Hierarchy.TaggedWidePadding

namespace OAI
/-! # The unique contiguous physical word shared by signed and routing gates -/

noncomputable section
namespace Hierarchy.Tagged.ChordAperture
open ThreeFlat Routing Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM
open PassiveWindow
open scoped Classical BigOperators Fin.CommRing

variable {F V I P : Type} [Field F] [Fintype I] [Fintype V] {W b : ℕ} {t : P → ℕ}
local notation "HS" => I × Fin W
local notation "Socket" => V ⊕ HS
local notation "Net" => BitNetwork F (Fintype.card Socket)
local notation "Pin" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits W) (BinaryBarrelTurns.digits W) W

private def pads (bits : I → Fin b → V) (q : I) : WidePadding.Ports (Socket ⊕ Bool) W b where
  col j := (j.val : Word b)
  live _ := .inr true
  width _ j := .inl (.inl (bits q j))
  payload j := .inl (.inr (q,j))

def padding (bits : I → Fin b → V) : Net :=
  WideHost.localFamily (fun q=>(pads (W:=W) bits q).network (F:=F)) idWire
where
  idWire (_ : I) : Socket ⊕ Bool → Socket ⊕ Bool := id

variable (o : Parts P I W t)

theorem padding_value (bits : I → Fin b → V) (v : V → Bool) (d : HS → Bool)
    (columns : W ≤ 2^b) (roomFit : ∀q,room o q<2^b)
    (read : ∀q j,v (bits q j)=TraceWords.bits (⟨room o q,roomFit q⟩ : Word b) j) :
    TypedWiring.value (padding (F:=F) (W:=W) bits) (Sum.elim v d)=
      if padded o (Function.curry d) then 1 else 0 := by
  rw [padding,WideHost.localFamily_eval]
  have each (q : I) : TypedWiring.value ((pads (W:=W) bits q).network (F:=F))
      ((Sum.elim (Sum.elim v d) id) ∘ padding.idWire q)=
      if ∀j : Fin W,room o q ≤ j.val → d (q,j)=false then 1 else 0 := by
    rw [WidePadding.Ports.eval _ _ (fun _=>⟨room o q,roomFit q⟩) (fun _ j=>read q j)]
    have val (i : Fin W) : ((i.val:Word b)).val=i.val := Fin.val_cast_of_lt (i.isLt.trans_le columns)
    have check :
        (∀i : Fin W,d (q,i)=true → true=true ∧ (i.val:Word b)<⟨room o q,roomFit q⟩) ↔
          ∀j : Fin W,room o q ≤ j.val → d (q,j)=false := by
      simp only [true_and,Fin.lt_def,val]
      constructor
      · intro l j high
        cases h : d (q,j) with
        | false=>rfl
        | true=>exact (Nat.not_lt_of_ge high (l j h)).elim
      · intro l j hit
        by_contra h
        have zero := l j (Nat.le_of_not_gt h)
        simp [hit] at zero
    split
    · rename_i good
      exact (ite_eq_left (check.mp good)).symm
    · rename_i bad
      exact (ite_eq_right (fun h => bad (check.mpr h))).symm
  simp_rw [each]
  rw [Fintype.prod_boole]
  split
  · rename_i good
    exact (ite_eq_left (show padded o (Function.curry d) from good)).symm
  · rename_i bad
    exact (ite_eq_right (show ¬padded o (Function.curry d) from bad)).symm

private def merged (cut : I×I → Pin → Socket ⊕ Bool) (bits : I → Fin b → V) : Net :=
  WideHost.localFamily (fun side : Bool=>if side then pairsNet (F:=F) cut else padding bits) (fun _=>Sum.inl)

def attach (cut : I×I → Pin → Socket ⊕ Bool) (bits : I → Fin b → V) (consumer : Net) :
    BitNetwork F (Fintype.card V) :=
  TypedWiring.glue (fun z : Bool=>if z then consumer else merged cut bits) (fun _ i=>i)

theorem fee (cut : I×I → Pin → Socket ⊕ Bool) (bits : I → Fin b → V) (consumer : Net) :
    (attach cut bits consumer).cells+(attach cut bits consumer).internal=
      Fintype.card HS+((padding (F:=F) (W:=W) bits).cells+(padding (F:=F) (W:=W) bits).internal)+
      ((pairsNet (F:=F) cut).cells+(pairsNet (F:=F) cut).internal)+(consumer.cells+consumer.internal) := by
  have ribbon : (merged (F:=F) cut bits).cells+(merged (F:=F) cut bits).internal=
      ((padding (F:=F) (W:=W) bits).cells+(padding (F:=F) (W:=W) bits).internal)+
      ((pairsNet (F:=F) cut).cells+(pairsNet (F:=F) cut).internal) := by
    rw [merged,WideHost.localFamily_size,Fintype.sum_bool]
    exact Nat.add_comm _ _
  simp only [attach,TypedWiring.glue_cells,TypedWiring.glue_internal,Fintype.sum_bool,
    Bool.false_eq_true,ite_false,ite_true] at *
  omega

theorem attach_value (fits : ∀p,t p ≤ W) (cut : I×I → Pin → Socket ⊕ Bool) (bits : I → Fin b → V)
    (consumer : Net) (v : V → Bool) (state : P→ℕ → Bool) (data : I → Bits W)
    (prior : ∀i p,o.owner i=some p → ∀u : Fin (o.width i),
      data i (u.castLE (o.within i))=state p (o.base i+u.val))
    (columns : W ≤ 2^b) (roomFit : ∀q,room o q<2^b)
    (widthRead : ∀q j,v (bits q j)=TraceWords.bits (⟨room o q,roomFit q⟩ : Word b) j)
    (read : ∀(d : HS → Bool) i q,Sum.elim (Sum.elim v d) id ∘cut (i,q)=
      BinaryBarrelTurns.pins ((addressEquiv _).symm (BinaryBarrelTurns.address (sizeAt o i q)))
        (fun s=>(addressEquiv _).symm (BinaryBarrelTurns.address (head o i s)))
        (PassiveWindow.data (data i) (fun j=>d (q,j)))) :
    TypedWiring.value (attach cut bits consumer) v=TypedWiring.value consumer (Sum.elim v (Function.uncurry (canonical o state))) := by
  rw [attach,TypedWiring.glue_value]
  let real := Function.uncurry (canonical o state)
  have per (d : HS → Bool) : TypedWiring.value (merged cut bits) (Sum.elim v d)=if d=real then (1:F) else 0 := by
    rw [merged,WideHost.localFamily_eval,Fintype.prod_bool]
    change TypedWiring.value (pairsNet cut) (Sum.elim v d)*TypedWiring.value (padding bits) (Sum.elim v d)=_
    rw [mul_comm (TypedWiring.value (pairsNet cut) (Sum.elim v d))]
    rw [padding_value o bits v d columns roomFit widthRead,eval o fits cut (Sum.elim v d) data (Function.curry d) (read d)]
    have h := unique o state data (Function.curry d) prior
    have rev : Function.curry d=canonical o state ↔ d=real := by
      constructor
      · intro eqn
        funext a
        exact congrFun (congrFun eqn a.1) a.2
      · rintro rfl
        rfl
    by_cases pad : padded o (Function.curry d) <;>
      by_cases ok : ∀i q,agrees o data (Function.curry d) i q <;> simp_all
  trans ∑d : HS → Bool,∏z : Bool,TypedWiring.value (if z then consumer else merged cut bits) (Sum.elim v d)
  · apply Finset.sum_congr (Finset.ext (fun _ => by simp))
    intro d _
    rfl
  simp only [Fintype.prod_bool,Bool.false_eq_true,ite_false,ite_true,per,mul_ite,mul_one,mul_zero]
  simp [real]

end Hierarchy.Tagged.ChordAperture

end
end OAI
