import OAI.Hierarchy.DescentOrderedRotorItems
import OAI.Hierarchy.DescentGoodBase

namespace OAI
/-! # Reading one public digit of a configured rotor packet row -/

namespace Hierarchy.DescentRotor.Ordered
open scoped Classical
noncomputable section
variable {E Q R V : Type*} {w u : ℕ} (addr : E→Q×Fin w) (slot : Q→R×V) (origin : E→V)
  (same : ∀e,(slot (addr e).1).2=origin e)

/-- A routed digit names its unique original occurrence, together with its
physical row. Both kinds of padding give a bit independent of all inputs. -/
def focus (r : R) (v : V) (j : Fin w) : Bool⊕{e:E // origin e=v} :=
  if row : ∃q,slot q=(r,v) then
    if used : ∃e,addr e=(row.choose,j) then
      .inr ⟨used.choose,(same _).symm.trans ((congrArg (fun q=>(slot q).2)
        (congrArg Prod.fst used.choose_spec)).trans (congrArg Prod.snd row.choose_spec))⟩
    else .inl false
  else .inl ((bitWord w).symm 0 j)

theorem focus_read [Fintype E] (r : R) (v : V) (j : Fin w) (x : E→Fin u→Bool) (k : Fin u) :
    (focus addr slot origin same r v j).elim id (fun e=>x e.val k) =
      (bitWord w).symm (fillRows 0 slot (packetWord addr x) (r,v) k) j := by
  classical
  by_cases row : ∃q,slot q=(r,v)
  · by_cases used : ∃e,addr e=(row.choose,j)
    · simp [focus,fillRows,row,used,packetWord]
    · simp [focus,fillRows,row,used,packetWord]
  · simp [focus,fillRows,row]

/-- On an occupied input the stored rank suffices to determine the output
digit in either direction, without any search among inactive records. -/
theorem focus_used (unique : Function.Injective addr) (uniqueSlot : Function.Injective slot) (e : E) :
    focus addr slot origin same (slot (addr e).1).1 (origin e) (addr e).2 = .inr ⟨e,rfl⟩ := by
  have hit : ∃q,slot q=((slot (addr e).1).1,origin e) := ⟨_,Prod.ext rfl (same e)⟩
  have name : hit.choose=(addr e).1 := uniqueSlot (hit.choose_spec.trans (Prod.ext rfl (same e).symm))
  have raw : ∃f,addr f=(hit.choose,(addr e).2) := ⟨e,by rw [name]⟩
  have orig : raw.choose=e := unique (raw.choose_spec.trans (by rw [name]))
  simp only [focus,dite_eq_left hit,dite_eq_left raw]
  exact congrArg Sum.inr (Subtype.ext orig)

end
end Hierarchy.DescentRotor.Ordered

end OAI
