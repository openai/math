import OAI.Hierarchy.ProtocolRAMSelectedRate
import OAI.Hierarchy.ProtocolRAMCommittedQuote
import OAI.Hierarchy.ProbeColumnAccounts

namespace OAI
/-! # Degree one and funded debit from actual named ports of committed strip rows -/

namespace Hierarchy.ProtocolRAM.SelectedRows
open AdaptiveProbe ColumnWires
open scoped BigOperators Classical
noncomputable section

variable {r n k : ℕ} {I R A C H B : Type*} [Fintype I]

omit [Fintype I] in
/-- The RAM has one public role field per option position, including any other
padded fields. On a positive ordinary write its address is read from its real
strip row. All strip rows and all ordinary roles within each row are distinct. -/
theorem Tape.native_unique (T : Tape r n I) (physical : Fin T.selected.card ↪ R)
    (addr : R×A ↪ I) (role : ∀j, Fin (T.ports (row T.selected j)) ↪ Role C H (A⊕B) k)
    (read : ∀j e i,T.activeKind ⟨j,e⟩=some i →
      account (fun a=>addr (physical j,a)) (role j e)=some i)
    {i : I} {e f : Σj, Fin (T.ports (row T.selected j))}
    (left : T.activeKind e=some i) (right : T.activeKind f=some i) : e=f := by
  obtain ⟨j,e⟩ := e
  obtain ⟨l,f⟩ := f
  obtain ⟨a,pa,ia⟩ := ordinary_of_some _ _ (read j e i left)
  obtain ⟨b,pb,ib⟩ := ordinary_of_some _ _ (read l f i right)
  have position := addr.injective (ia.trans ib.symm)
  have sameRow := physical.injective (congrArg Prod.fst position)
  have sameAddr : a=b := congrArg Prod.snd position
  subst l; subst b
  exact congrArg (Sigma.mk j) ((role j).injective (pa.trans pb.symm))

omit [Fintype I] in
/-- A common physical port count can exceed the typed menu's arity. Only an
actually occupied ordinary field needs a preimage among the authentic roles. -/
theorem Tape.native_unique_padded (T : Tape r n I) (physical : Fin T.selected.card ↪ R)
    (addr : R×A ↪ I) (port : ∀j, Role C H (A⊕B) k → Fin (T.ports (row T.selected j)))
    (read : ∀j e i,T.activeKind ⟨j,e⟩=some i → ∃v,port j v=e ∧
      account (fun a=>addr (physical j,a)) v=some i)
    {i : I} {e f : Σj, Fin (T.ports (row T.selected j))}
    (left : T.activeKind e=some i) (right : T.activeKind f=some i) : e=f := by
  obtain ⟨j,e⟩ := e
  obtain ⟨l,f⟩ := f
  obtain ⟨u,eu,paid⟩ := read j e i left
  obtain ⟨v,ev,spent⟩ := read l f i right
  obtain ⟨a,pa,ia⟩ := ordinary_of_some _ _ paid
  obtain ⟨b,pb,ib⟩ := ordinary_of_some _ _ spent
  have position := addr.injective (ia.trans ib.symm)
  have sameRow := physical.injective (congrArg Prod.fst position)
  have sameAddr : a=b := congrArg Prod.snd position
  subst l; subst b
  exact congrArg (Sigma.mk j) (eu.symm.trans ((congrArg (port j) (pa.trans pb.symm)).trans ev))

omit [Fintype I] in
theorem Tape.positive_debit_unique (T : Tape r n I)
    (one : ∀{i : I} {e f : Σj,Fin (T.ports (row T.selected j))},
      T.activeKind e=some i → T.activeKind f=some i → e=f) {i : I} {e f : Fin n}
    (left : T.kind e=some i) (right : T.kind f=some i) (paid : 0<T.take e) (paid' : 0<T.take f) : e=f := by
  classical
  have indexed (g : Fin n) (pos : 0<T.take g) : ∃ p,T.use p=g := by
    by_contra missing
    have off := T.off (e:=g) (fun p eq => missing ⟨p,eq⟩)
    omega
  obtain ⟨x,rfl⟩ := indexed e paid
  obtain ⟨y,rfl⟩ := indexed f paid'
  have first : T.activeKind x=some i := by
    rw [Tape.activeKind,ite_eq_right (by omega)]; exact left
  have last : T.activeKind y=some i := by
    rw [Tape.activeKind,ite_eq_right (by omega)]; exact right
  exact congrArg T.use (one first last)

omit [Fintype I] in
theorem Tape.ordinary_degree (T : Tape r n I)
    (one : ∀{i : I} {e f : Σj,Fin (T.ports (row T.selected j))},
      T.activeKind e=some i → T.activeKind f=some i → e=f) (i : I) :
    (Finset.univ.filter (fun e=>T.activeKind e=some i)).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  exact one (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

end
end Hierarchy.ProtocolRAM.SelectedRows

end OAI
