import OAI.Hierarchy.ProbeCoreWalkMount
import OAI.Hierarchy.ProbeRouteOccurrences
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Permutation-independent order of the physical core and return walk occurrences -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open AdaptiveProbe ProbeStage CoreBoard LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
variable {h d k edges K : ℕ} {S : PurchaseSampler}

theorem prefix_length (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    (prefixWalk (S:=S) (k:=k) π p j).length=2*j.val := by
  induction j using Fin.induction with
  | zero => simp [prefixWalk]
  | succ t ih => simpa [prefixWalk,Fin.induction_succ,Nat.mul_succ,Nat.add_assoc] using ih

theorem prefix_even (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1))
    (t : StageAt h d) (earlier : t.val < j.val) :
    (prefixWalk (S:=S) (k:=k) π p j)[2*t.val]'(by rw [prefix_length];omega)=jointEdge π p t.castSucc none := by
  induction j using Fin.induction with
  | zero => simp at earlier
  | succ i ih =>
    change t.val < i.val+1 at earlier
    change (prefixWalk (S:=S) π p i.castSucc ++ [jointEdge π p i.castSucc none,tileEdge p i none])[2*t.val]'(by
      simp only [List.length_append,prefix_length,Fin.val_castSucc,List.length_cons,List.length_nil]
      omega)=_
    by_cases lt : t.val < i.val
    · rw [List.getElem_append_left (by rw [prefix_length];change 2*t.val<2*i.val;omega)]
      exact ih lt
    · have eq : t=i := Fin.ext (by omega)
      subst t
      rw [List.getElem_append_right (by rw [prefix_length];exact le_rfl)]
      simp [prefix_length]

theorem prefix_odd (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1))
    (t : StageAt h d) (earlier : t.val < j.val) :
    (prefixWalk (S:=S) (k:=k) π p j)[2*t.val+1]'(by rw [prefix_length];omega)=tileEdge p t none := by
  induction j using Fin.induction with
  | zero => simp at earlier
  | succ i ih =>
    change t.val < i.val+1 at earlier
    change (prefixWalk (S:=S) π p i.castSucc ++ [jointEdge π p i.castSucc none,tileEdge p i none])[2*t.val+1]'(by
      simp only [List.length_append,prefix_length,Fin.val_castSucc,List.length_cons,List.length_nil]
      omega)=_
    by_cases lt : t.val < i.val
    · rw [List.getElem_append_left (by rw [prefix_length];change 2*t.val+1<2*i.val;omega)]
      exact ih lt
    · have eq : t=i := Fin.ext (by omega)
      subst t
      rw [List.getElem_append_right (by rw [prefix_length];change 2*i.val≤2*i.val+1;omega)]
      simp [prefix_length]

theorem payload_length (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) :
    (payloadWalk (S:=S) (k:=k) (d:=d) π p).length=2*Stages h d+1 := by simp [payloadWalk,prefix_length]

theorem payload_even (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    (payloadWalk (S:=S) (k:=k) π p)[2*j.val]'(by rw [payload_length];omega)=jointEdge π p j none := by
  unfold payloadWalk
  by_cases lt : j.val < Stages h d
  · rw [List.getElem_append_left (by rw [prefix_length];change 2*j.val<2*Stages h d;omega)]
    exact prefix_even π p (Fin.last _) ⟨j.val,lt⟩ lt
  · have eq : j=Fin.last _ := Fin.ext (by change j.val=Stages h d;omega)
    subst j
    rw [List.getElem_append_right (by rw [prefix_length])]
    simp [prefix_length]

theorem payload_odd (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : StageAt h d) :
    (payloadWalk (S:=S) (k:=k) π p)[2*j.val+1]'(by rw [payload_length];have bound : j.val < Stages h d:=j.isLt;omega)=tileEdge p j none := by
  unfold payloadWalk
  rw [List.getElem_append_left (by rw [prefix_length];change 2*j.val+1<2*Stages h d;have bound : j.val < Stages h d:=j.isLt;omega)]
  exact prefix_odd π p _ j j.isLt

abbrev Slots (h d k : ℕ) :=
  (Σ i : Commodity (Fin (2^h)) (Stages h d) k,Fin (Sum.elim (fun _=>2*Stages h d+1) (fun _=>2) i)) ⊕
  (Σ _ : Columns h d × Fin k,Fin 2)

abbrev Actions (n k : ℕ) := Fin (2*n+1) ⊕ Fin n ⊕ (Fin n × (Fin k × Bool)) ⊕ (Fin k × Bool)

def action : Slots h d k → Actions (Stages h d) k × ℕ
  | .inl ⟨.inl p,t⟩ => (.inl t,p.val)
  | .inl ⟨.inr ((p,j),l),t⟩ => (if t.val=0 then .inr (.inl j) else .inr (.inr (.inl (j,l))),p.val)
  | .inr ⟨(c,a),t⟩ => (.inr (.inr (.inr (a,decide (t.val=1)))),((Fintype.equivFin _) c).val)

def siteKind : Slots h d k → ℕ := Sum.elim (fun _=>1) (fun _=>2)
def siteResource (ci : Commodity (Fin (2^h)) (Stages h d) k→ℕ) (cj : Columns h d × Fin k→ℕ) : Slots h d k→ℕ :=
  Sum.elim (fun s=>ci s.1) (fun s=>cj s.1)

variable {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges)

def toOccurrence : Slots h d k ≃ RouteOccurrence B.ordinary B.centers :=
  Equiv.sumCongr (Equiv.sigmaCongrRight (fun i=>finCongr (by
    cases i with
    | inl p => simp [Mount.ordinary,commodityWalk,payload_length]
    | inr q => rcases q with ⟨⟨p,t⟩,l⟩;rfl)))
    (Equiv.sigmaCongrRight (fun c=>finCongr (by rcases c with ⟨c,l⟩;rfl)))

structure Orders (h d k : ℕ) where
  core : Commodity (Fin (2^h)) (Stages h d) k ≃ Fin (Fintype.card (Commodity (Fin (2^h)) (Stages h d) k))
  center : Columns h d × Fin k ≃ Fin (Fintype.card (Columns h d × Fin k))

def arity : Commodity (Fin (2^h)) (Stages h d) k→ℕ := Sum.elim (fun _=>2*Stages h d+1) (fun _=>2)

private def ranked {α : Type*} {n : ℕ} (ord : α≃Fin n) (f : α→ℕ) :
    (Σ i : α,Fin (f i)) ≃ Fin (∑i,f (ord.symm i)) :=
  (Equiv.sigmaCongr ord (fun i=>finCongr (by rw [ord.symm_apply_apply]))).trans finSigmaFinEquiv

def packed (o : Orders h d k) :=
  (Equiv.sumCongr (ranked o.core arity) (ranked o.center (fun _=>2))).trans finSumFinEquiv

private theorem ranked_val {α : Type*} {n : ℕ} (o : α ≃ Fin n) (f : α → ℕ) (a : α) (t : Fin (f a)) :
    ((ranked o f) ⟨a,t⟩).val=(∑ j : Fin (o a).val,f (o.symm (Fin.castLE (o a).isLt.le j)))+t.val := by
  let j : Fin (f (o.symm (o a))) := Fin.cast (congrArg f (o.symm_apply_apply a)).symm t
  exact finSigmaFinEquiv_apply (⟨o a,j⟩ : (i : Fin n) × Fin (f (o.symm i)))

def slotOrder (o : Orders h d k) : Slots h d k ≃ Fin (Fintype.card (Slots h d k)) := by
  let packed' : Slots h d k ≃ Fin ((∑j,arity (o.core.symm j))+∑_j : Fin (Fintype.card (Columns h d × Fin k)),2) := packed o
  exact packed'.trans (finCongr (by
    have same := (Fintype.card_congr packed').symm
    simpa only [Fintype.card_fin] using same))

/-- Position of each ordinary-good hop in the initial segment of the shared recipe. -/
def corePrefix (o : Orders h d k) := ranked o.core arity

theorem corePrefix_val (o : Orders h d k)
    (v : Σ i : Commodity (Fin (2^h)) (Stages h d) k,Fin (arity i)) :
    (slotOrder o (.inl v)).val=(corePrefix o v).val := rfl

def enum (o : Orders h d k) := (slotOrder o).symm.trans (toOccurrence B)

theorem slotOrder_core (o : Orders h d k) (i : Commodity (Fin (2^h)) (Stages h d) k)
    (t : Fin (arity i)) :
    (slotOrder o (.inl ⟨i,t⟩)).val=
      (∑j : Fin (o.core i).val,arity (o.core.symm (Fin.castLE (o.core i).isLt.le j)))+t.val := by
  exact ranked_val o.core arity i t

theorem slotOrder_center (o : Orders h d k) (c : Columns h d×Fin k) (t : Fin 2) :
    (slotOrder o (.inr ⟨c,t⟩)).val=(∑j,arity (o.core.symm j))+2*(o.center c).val+t.val := by
  change (∑j,arity (o.core.symm j))+((ranked o.center (fun _=>2)) ⟨c,t⟩).val=_
  rw [ranked_val]
  simp [Nat.mul_comm,Nat.add_assoc]

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
