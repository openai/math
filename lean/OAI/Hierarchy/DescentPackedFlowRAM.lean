import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Count paid directed neighbor incidences in place on packed old group sheets -/
namespace Hierarchy.DescentPackedFlowRAM
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {r c b d H J M w : ℕ}
abbrev Slot (r c : ℕ) := Fin r × Fin c

def chart (r c : ℕ) : List (Slot r c) := List.ofFn (finProdFinEquiv.symm : Fin (r*c)→Slot r c)

def insert (unit target : ℕ) (x : Fin r) (acc : Cell (b*r)) (tag : Cell d) : Cell (b*r) :=
  if tag.val=target+1 then
    encode b r (Function.update ((encode b r).symm acc) x (((encode b r).symm acc) x+unit)) else acc

theorem empty (unit target : ℕ) (x : Fin r) : insert (b:=b) (d:=d) unit target x 0 0=0 := by simp [insert]

def increment (x : Fin r) (q : Slot r c) (tag : Slot r c→Cell d) (unit target : ℕ) :=
  if x=q.1 ∧ (tag q).val=target+1 then unit else 0

theorem accumulated (qs : List (Slot r c)) (tag : Slot r c→Cell d) (unit target : ℕ)
    (acc : Cell (b*r)) (x : Fin r) :
    (encode b r).symm (qs.foldl (fun u i=>insert unit target i.1 u (tag i)) acc) x =
      (encode b r).symm acc x+((qs.map (fun q=>increment x q tag unit target)).sum:ℕ) := by
  induction qs generalizing acc with
  | nil=>simp
  | cons q qs ih=>
    simp only [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.cast_add]
    by_cases a:x=q.1 <;> by_cases t:(tag q).val=target+1 <;>
      simp [insert,increment,a,t,Function.update,add_assoc]

private theorem encodeZero (b r : ℕ) : encode b r (fun _=>0)=0 := by
  apply Fin.ext
  simp [encode]

def counts (tag : Slot r c→Cell d) (target : ℕ) (x : Fin r) :=
  Fintype.card {s : Fin c // (tag (x,s)).val=target+1}

theorem finish (tag : Slot r c→Cell d) (unit target : ℕ) :
    ((chart r c).foldl (fun u i=>insert unit target i.1 u (tag i)) (0:Cell (b*r))) =
      encode b r (fun x=>(unit*counts tag target x:ℕ)) := by
  apply (encode b r).symm.injective
  funext x
  rw [Equiv.symm_apply_apply,accumulated,←encodeZero b r,Equiv.symm_apply_apply,zero_add]
  apply congrArg (fun n : ℕ=>(n:Cell b))
  simp only [chart,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun q : Slot r c=>increment x q tag unit target)]
  simp only [Fintype.sum_prod_type,increment]
  have drop (i : Fin r) : (∑s : Fin c,if x=i ∧ (tag (i,s)).val=target+1 then unit else 0)=
      if x=i then ∑s : Fin c,if (tag (i,s)).val=target+1 then unit else 0 else 0 := by
    by_cases h:x=i <;> simp [h]
  simp only [drop,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [←Finset.sum_filter]
  simp [counts,Fintype.card_subtype,Nat.mul_comm]

def entry (B : Slot r c→Bank) (T : Fin r→DescentPackedZip.Tables) (acc : Expr) (q : Slot r c) :=
  (T q.1).read acc (.lookup (B q) .row)

def sumRow (B : Slot r c→Bank) (T : Fin r→DescentPackedZip.Tables) :=
  (chart r c).foldl (entry B T) (.lit 0)

theorem work (B : Slot r c→Bank) (T : Fin r→DescentPackedZip.Tables) :
    (sumRow B T).work=1+18*(r*c) := by
  have iter (qs : List (Slot r c)) (init : Expr) :
      (qs.foldl (entry B T) init).work=init.work+18*qs.length := by
    induction qs generalizing init with
    | nil=>simp
    | cons q qs ih=>
      simp only [List.foldl_cons,ih,List.length_cons,entry,DescentPackedZip.work]
      have read : (Expr.lookup (B q) .row).work=7:=rfl
      rw [read];omega
  simp [sumRow,iter,chart,Expr.work]

theorem native (B : Slot r c→Bank) (T : Fin r→DescentPackedZip.Tables) (out unit target : ℕ)
    (m : Memory w) (tags : Fin H→Fin J→Slot r c→Cell d)
    (size : out+H*chunks J M<2^w)
    (banks : ∀q,(B q).Fits w out ∧ H*chunks J M≤(B q).size)
    (spaces : ∀x,WordRoom (T x) (b*r) d M w out)
    (fixed : ∀x,DescentPackedZip.Static (T x) (insert (b:=b) (d:=d) unit target x) M m)
    (dataIn : ∀q,Reads (B q) (fun v g=>tags v g q) M m) :
    let expr:=sumRow B T
    let dst:=image out (H*chunks J M) expr m
    (scan w out (H*chunks J M) expr).Exec m dst (4+H*chunks J M*(2*expr.work+4)) ∧
      (∀p : Row H J M,dst (out+(row H J M p).val)=
        ((data (fun v g=>encode b r (fun x=>(unit*counts (tags v g) target x:ℕ))) p).val:Word w)) ∧
      CheapCode (scan w out (H*chunks J M) expr) := by
  intro expr dst
  have fold (qs : List (Slot r c)) (u : Expr) (acc : Fin H→Fin J→Cell (b*r)) (safe : u.Fits w out)
      (old : DescentPackedZip.Source u acc M m) :
      (qs.foldl (entry B T) u).Fits w out ∧ DescentPackedZip.Source (qs.foldl (entry B T) u)
        (fun v g=>qs.foldl (fun z q=>insert unit target q.1 z (tags v g q)) (acc v g)) M m := by
    induction qs generalizing u acc with
    | nil=>exact ⟨safe,old⟩
    | cons q qs ih=>
      have right : (Expr.lookup (B q) .row).Fits w out:=⟨(banks q).1,trivial⟩
      have rhs:=DescentPackedZip.source_column (B q) out (banks q).1 m _ (banks q).2 (dataIn q)
      exact ih _ _ ((spaces q.1).safe _ _ safe right) (DescentPackedZip.read_data _ _ _ out
        ((spaces q.1).issue _ _ safe right) _ (empty ..) m (fixed q.1) _ _ old rhs)
  have zero : DescentPackedZip.Source (.lit 0) (fun _ : Fin H=>fun _ : Fin J=>(0:Cell (b*r))) M m := by
    intro p
    change (0:Word w)=((encode _ M (fun i=>if _ : p.2.val*M+i.val<J then 0 else 0)).val:ℕ)
    simp [encodeZero]
  obtain ⟨fits,read⟩:=fold (chart r c) (.lit 0) _ trivial zero
  refine ⟨scan_exec _ _ _ _ fits size,?_,@scan_cheap _ _ _ _⟩
  intro p
  change image out (H*chunks J M) expr m (out+(row H J M p).val) = _
  rw [ProtocolRAMGeneratedWrite.read_image out _ expr m (row H J M p)]
  simpa only [expr,sumRow,finish] using read p

end
end Hierarchy.DescentPackedFlowRAM

end OAI
