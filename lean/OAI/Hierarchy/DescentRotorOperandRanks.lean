import OAI.Hierarchy.DescentFallbackItemSelect
import OAI.Hierarchy.DescentOrderedRotorItems

namespace OAI
/-! # Old grain order within the measured matrix cells and public sockets -/
namespace Hierarchy.DescentRotorOperandRanks
open DescentFallbackItemSelect DescentRotor
open scoped Classical
noncomputable section
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {K N : ℕ}
    (slot : E↪Fin K) (key : E↪Fin N) (items : Fin K→Item)
    (src dst : E→V) (ends : Fin K→Option (V×V))
    (read : ∀e,ends (slot e)=some (src e,dst e))
    (ghost : ∀j,(¬∃e,slot e=j)→ends j=none)
    (earlier : ∀u v,before items (slot u) (slot v) ↔ key u<key v)

def rows (ends : Fin K→Option (V×V)) (p : V×V→Prop) [DecidablePred p] : Finset (Fin K) :=
  Finset.univ.filter (fun j=>(ends j).any (fun t=>decide (p t)))

abbrev At (src dst : E→V) (p : V×V→Prop) := {e:E // p (src e,dst e)}

include read in
omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem slot_mem (p : V×V→Prop) [DecidablePred p] (e : E) :
    slot e ∈ rows ends p ↔ p (src e,dst e) := by simp [rows,read e]

include read ghost in
def coords (p : V×V→Prop) [DecidablePred p] : At src dst p≃↥(rows ends p) :=
  Equiv.ofBijective
    (fun e=>⟨slot e.val,(slot_mem slot src dst ends read p e.val).mpr e.property⟩)
    ⟨fun _ _ eqn=>Subtype.ext (slot.injective (congrArg Subtype.val eqn)),by
      rintro ⟨j,live⟩
      by_cases hit : ∃e,slot e=j
      · obtain ⟨e,rfl⟩:=hit
        exact ⟨⟨e,(slot_mem slot src dst ends read p e).mp live⟩,rfl⟩
      · simp [rows,ghost j hit] at live⟩

include read ghost earlier in
omit [Fintype V] [DecidableEq V] in
theorem rank_exact (p : V×V→Prop) [DecidablePred p] (e : At src dst p) :
    rank items (rows ends p) (slot e.val)=
      (Finset.univ.filter (fun i : At src dst p=>key i.val<key e.val)).card := by
  let coord:=coords slot src dst ends read ghost p
  apply rank_of_equiv items (rows ends p) coord ((Function.Embedding.subtype _).trans key) _ e
  intro a b
  exact earlier a.val b.val

include read ghost in
omit [Fintype V] [DecidableEq V] in
theorem count_exact (p : V×V→Prop) [DecidablePred p] :
    (rows ends p).card=Fintype.card (At src dst p) := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (coords slot src dst ends read ghost p)).symm

include read ghost earlier in
omit [Fintype V] [DecidableEq V] in
theorem socket_select (p : V×V→Prop) [DecidablePred p] (e : At src dst p) (m : ℕ) (batch : Fin m) :
    select items (rows ends p)
      (((Finset.univ.filter (fun i : At src dst p=>key i.val<key e.val)).card*m+batch.val)/m)=
      some (slot e.val) := by
  rw [←rank_exact slot key items src dst ends read ghost earlier p e]
  exact select_nth items _ ((slot_mem slot src dst ends read p _).mpr e.property) m batch

include read ghost earlier in
omit [Fintype V] in
theorem serial (e : E) :
    rank items (rows ends (·=(src e,dst e))) (slot e)=
      (Ordered.ordinal key src dst (src e,dst e) ((Ordered.cells src dst e).2)).val := by
  let q:=(src e,dst e)
  let point : Ordered.At src dst q := ⟨e,by simp [q,cell]⟩
  let c : Ordered.At src dst q ≃ At src dst (·=q) :=
    Equiv.subtypeEquivRight (fun a=>by simp [q,cell])
  let bins:=coords slot src dst ends read ghost (·=q)
  let qkey : Ordered.At src dst q↪Fin N:=(Function.Embedding.subtype _).trans key
  change rank items (rows ends (·=q)) (slot e) = (Ordered.ordinal key src dst q point).val
  have ranked := rank_of_equiv items _ (c.trans bins) qkey (fun a b=>earlier a.val b.val) point
  exact ranked.trans (Ordered.ordinal_value key src dst q point).symm

end
end Hierarchy.DescentRotorOperandRanks

end OAI
