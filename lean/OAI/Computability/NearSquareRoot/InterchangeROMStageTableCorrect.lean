import OAI.Computability.NearSquareRoot.InterchangeROMStageTable
import OAI.Computability.NearSquareRoot.InterchangeROMRepairStage

/-! # Correctness of the natural rectangle-gate matrices -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable
open Interchange StageLedger StageRoute

variable {p : ℕ}

@[simp] theorem value_nil (x : Ground → ZMod p) : value x [] = 0 := rfl

@[simp] theorem value_cons (x : Ground → ZMod p) (u : Role) (k c : ℕ) (ts : List Term) :
    value x (term u k c :: ts) = (c : ZMod p) * x (u,k) + value x ts := rfl

@[simp] theorem value_append (x : Ground → ZMod p) (a b : List Term) :
    value x (a++b) = value x a + value x b := by simp [value]

@[simp] theorem value_ite (x : Ground → ZMod p) (P : Prop) [Decidable P] (a b : List Term) :
    value x (if P then a else b) = if P then value x a else value x b := by split <;> rfl

@[simp] theorem value_across (x : Ground → ZMod p) (n : ℕ) (f : ℕ → List Term) :
    value x (across n f) = ∑ i : Fin n, value x (f i) := by
  have eq : (List.range n).map (fun i => value x (f i)) = List.ofFn (fun i : Fin n => value x (f i)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp
  have flatten (l : List ℕ) : value x (l.flatMap f) = (l.map fun i => value x (f i)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [ih]
  exact (flatten _).trans ((congrArg List.sum eq).trans List.sum_ofFn)

variable (g : Data)

abbrev L := Fin g.labels
abbrev B := Fin g.rectangles
abbrev H := Fin g.ranks
abbrev Q := Fin g.queries
abbrev D := Fin g.lanes

structure FrameOK (r : B g → Rectangle (L g)) (I J : H g → L g) : Prop where
  src : ∀ (b : B g) (v : L g), g.src b v = decide (v ∈ (r b).sources)
  dst : ∀ (b : B g) (v : L g), g.dst b v = decide (v ∈ (r b).destinations)
  row : ∀ (i : H g), g.row i = I i
  col : ∀ (i : H g), g.col i = J i

variable {g} {r : B g → Rectangle (L g)} {I J : H g → L g}

def eRole {side : Bool} (e : Endpoint r side) : Role := reserve e.1 e.2.1
def qeRole {side : Bool} (z : Q g × Endpoint r side) : Role := active z.1 z.2.1 z.2.2.1
def rRole (z : Q g × B g) : Role := rect z.1 z.2
def mRole (z : Q g × H g) : Role := mixed z.1 z.2
def lRole (z : Q g × L g) : Role := label z.1 z.2
def tRole {side : Bool} {s : H g → L g} (z : Q g × RankTerm r side s) : Role :=
  rankTerm z.1 z.2.1 (z.2.2.elim 0 fun b => b.1.1+1)

abbrev native {g : Data} (v : L g) : Role := plain v

private theorem sum_mem {A : Type} [Fintype A] (u : Finset A) (f : A → ZMod p) [DecidableEq A] :
    (∑ a, if a ∈ u then f a else 0) = ∑ a : u, f a.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

theorem partial_correct (ok : FrameOK g r I J) (x : Ground → ZMod p)
    (o : L g ⊕ (Q g × B g)) (d : ℕ) :
    value x (partials g (Sum.elim native rRole o) d) =
      partialTable r (fun a => x (Sum.elim native qeRole a,d)) o := by
  rcases o with v | ⟨j,b⟩
  · simp [partials,native,plain,partialTable]
  · simp only [partials,rRole,rect,OfNat.ofNat_ne_zero,ite_false,value_across,
      ok.src,decide_eq_true_eq,value_ite,value_cons,value_nil,Nat.cast_one,one_mul,add_zero,
      partialTable,Sum.elim_inr,qeRole]
    exact sum_mem ((r b).sources) (fun v => x (active j v b,d))

theorem finish_correct (ok : FrameOK g r I J) (x : Ground → ZMod p) (v : L g) (d : ℕ) :
    value x (finish g (native v) d) =
      finishTable r (fun a => x (Sum.elim native eRole a,d)) v := by
  simp only [finish,native,plain,finishTable,eRole,Sum.elim_inl,Sum.elim_inr,value_across,
    value_cons,value_nil,value_ite,Nat.cast_one,one_mul,add_zero,ok.dst,decide_eq_true_eq]
  apply congrArg (x (native v,d) + ·)
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) (fun b : B g => x (reserve v b,d))

theorem mix_correct [Fact p.Prime] (ok : FrameOK g r I J) (x : Ground → ZMod p)
    (o : (L g ⊕ (Q g × B g)) ⊕ (Q g × H g)) (d : ℕ) :
    value x (mix g (Sum.elim (Sum.elim native rRole) mRole o) d) =
      mixTable r I (fun i k : H g => (g.minor i k : ZMod p))
        (fun a => x (Sum.elim (Sum.elim native rRole) tRole a,d)) o := by
  rcases o with (v | ⟨j,b⟩) | ⟨j,i⟩
  · simp [mix,native,plain,mixTable]
  · simp [mix,rRole,rect,mixTable]
  · simp only [mix,mRole,mixed,Sum.elim_inr,ite_true,value_across,value_cons,value_nil,
      value_ite,add_zero,ok.row,ok.dst,decide_eq_true_eq,mixTable,applyRows,smul_eq_mul,tRole,
      Option.elim_none,Option.elim_some,mul_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply congrArg ((g.minor i k : ZMod p) * x (rankTerm j k 0,d) + ·)
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun b : B g =>
      (g.minor i k : ZMod p) * x (rankTerm j k (b.1+1),d))

theorem scatter_correct [NeZero p] (hp : g.p = p) (ok : FrameOK g r I J) (x : Ground → ZMod p)
    (o : (L g ⊕ (Q g × L g)) ⊕ (Q g × B g)) (d : ℕ) :
    value x (scatter g (Sum.elim (Sum.elim native lRole) rRole o) d) =
      scatterTable r J (fun a => x (Sum.elim (Sum.elim native rRole) tRole a,d)) o := by
  rcases o with (v | ⟨j,v⟩) | ⟨j,b⟩
  · simp [scatter,native,plain,scatterTable]
  · simp [scatter,lRole,label,scatterTable,ok.col,tRole,Fin.val_inj]
  · have neg : ((g.p-1 : ℕ) : ZMod p) = -1 := by rw [hp,Nat.cast_pred (NeZero.pos p),ZMod.natCast_self,zero_sub]
    simp [rRole,rect,scatter,neg,ok.col,ok.src,scatterTable,tRole,sub_eq_add_neg,add_comm]

theorem collect_correct [Fact p.Prime] (x : Ground → ZMod p) (o : L g ⊕ Endpoint r true) (d : D g) :
    value x (collect g (Sum.elim native eRole o) d) =
      sumQueries r
        (InterchangeROMRepair.mixerMap (fun i k : D g => (g.base i k : ZMod p)))
        (fun j : Q g => InterchangeROMRepair.mixerMap (fun i k : D g => (g.query j i k : ZMod p)))
        (fun a (k : D g) => x (Sum.elim (Sum.elim native lRole) qeRole a,k)) o d := by
  rcases o with v | ⟨v,b⟩
  · simp [collect,native,plain,sumQueries,lRole,InterchangeROMRepair.mixerMap,Matrix.mulVec,dotProduct,
      Pi.add_apply,Finset.sum_apply]
  · simp [collect,eRole,reserve,sumQueries,qeRole,InterchangeROMRepair.mixerMap,Matrix.mulVec,dotProduct,
      Finset.sum_apply]

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
