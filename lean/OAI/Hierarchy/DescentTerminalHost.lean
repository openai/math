import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.CollapseOracle

namespace OAI
/-! # A single open host for a bank of homogeneous tagged calls -/

namespace Hierarchy.DescentTerminalHost
open Catalyst CatalystSubstitution Tagged ThreeFlat Routing
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {V H : Type} [Fintype V] [Fintype H] {k p : ℕ}

private def source (v : V ⊕ Bool) : BitSource 0 (Fintype.card V) :=
  v.elim (fun a=>.pin (Fintype.equivFin _ a)) BitSource.constant

private theorem source_read (u : V ⊕ Bool) (x : V → Bool) (empty : Fin 0 → Bool) :
    (source u).read empty (x ∘ (Fintype.equivFin _).symm) = Sum.elim x id u := by
  cases u <;> simp [source,BitSource.read]

def socket {q : ℕ} (F : Type*) [Field F] (read : Fin q → V ⊕ Bool) :
    BitNetwork F (Fintype.card (V ⊕ Fin q)) :=
  OracleCut.network (r:=fun _ : Empty=>0) (z:=0) (fun i=>nomatch i) (fun i=>nomatch i)
    (fun i=>source (read i))

theorem socket_value {q : ℕ} (read : Fin q → V ⊕ Bool) (x : V → Bool) (f : (Fin q → Bool) → F) :
    (∑ z,TypedWiring.value (socket F read) (Sum.elim x z)*f z)=f (Sum.elim x id ∘ read) := by
  unfold socket
  rw [OracleCut.contract,Fintype.sum_unique]
  simp [Function.comp_def]
  exact congrArg f (funext fun j => source_read (read j) x _)

theorem socket_size {q : ℕ} (read : Fin q → V ⊕ Bool) :
    (socket F read).cells+(socket F read).internal=28*q := by
  unfold socket
  rw [OracleCut.size]
  simp

def cuts (o : Occurrence F k) : (t : ℕ) → (Fin t → Fin o.arity → V ⊕ Bool) →
    WideHost.Parts F V (List.replicate t o)
  | 0,_=>PUnit.unit
  | t+1,read=>(socket F (read 0),cuts o t (fun i=>read i.succ))

theorem cuts_value (o : Occurrence F k) (localPart : BitNetwork F (Fintype.card V)) (v : V → Bool)
    (t : ℕ) (read : Fin t → Fin o.arity → V ⊕ Bool) :
    WideHost.closed localPart (List.replicate t o) (cuts o t read) v =
      (∏ i,o.target (Sum.elim v id ∘ read i))*TypedWiring.value localPart v := by
  induction t with
  | zero => simp [WideHost.closed,cuts]
  | succ t ih =>
    change (∑ z,TypedWiring.value (socket F (read 0)) (Sum.elim v z)*o.target z)*
      WideHost.closed localPart (List.replicate t o) (cuts o t (fun i=>read i.succ)) v=_
    rw [socket_value,ih,Fin.prod_univ_succ]
    rw [mul_assoc]

theorem cuts_size (o : Occurrence F k) (t : ℕ) (read : Fin t → Fin o.arity → V ⊕ Bool) :
    WideHost.partsCost (List.replicate t o) (cuts o t read)=t*(28*o.arity) := by
  induction t with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ t ih =>
    change (socket F (read 0)).cells+(socket F (read 0)).internal+
      WideHost.partsCost (List.replicate t o) (cuts o t (fun i=>read i.succ))=_
    rw [socket_size,ih]
    ring

def host (width : Fin k → ℕ) (o : Occurrence F k) (t : ℕ)
    (localPart : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (read : Fin t → Fin o.arity → (Catalyst.Port p width ⊕ H) ⊕ Bool) :
    Host F k p (Sockets (List.replicate t o)) :=
  WideHost.host width localPart (List.replicate t o) (cuts o t read)

theorem exact_host (width : Fin k → ℕ) (o : Occurrence F k) (t : ℕ)
    (localPart : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (read : Fin t → Fin o.arity → (Catalyst.Port p width ⊕ H) ⊕ Bool) (x : Catalyst.Port p width → Bool) :
    exactValue (List.replicate t o) (host width o t localPart read) x =
      ∑ a : H → Bool, (∏ i,o.target (Sum.elim (Sum.elim x a) id ∘ read i))*
        TypedWiring.value localPart (Sum.elim x a) := by
  calc
    _ = ∑ a : H → Bool, WideHost.closed localPart (List.replicate t o)
        (cuts o t read) (Sum.elim x a) :=
      WideHost.exactValue_host width localPart _ (cuts o t read) x
    _ = _ := Finset.sum_congr rfl fun a _=>cuts_value o localPart _ t read

theorem host_price (width : Fin k → ℕ) (o : Occurrence F k) (t : ℕ)
    (localPart : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (read : Fin t → Fin o.arity → (Catalyst.Port p width ⊕ H) ⊕ Bool) :
    hostSize (host width o t localPart read) =
      localPart.cells+localPart.internal+29*(t*o.arity)+Fintype.card H+Fintype.card (Catalyst.Port p width) := by
  rw [host,WideHost.host_size,cuts_size,
    Fintype.card_sum (α:=Catalyst.Port p width) (β:=Sockets (List.replicate t o))]
  have arities (j : ℕ) : Fintype.card (Sockets (List.replicate j o))=j*o.arity := by
    induction j with
    | zero => change Fintype.card Empty=_; simp
    | succ j ih =>
      change Fintype.card (Fin o.arity ⊕ Sockets (List.replicate j o))=_
      rw [Fintype.card_sum,Fintype.card_fin,ih,Nat.succ_mul j,Nat.add_comm]
  rw [arities]
  ring

end
end Hierarchy.DescentTerminalHost

end OAI
