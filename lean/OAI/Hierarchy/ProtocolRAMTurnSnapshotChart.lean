import OAI.Hierarchy.ProtocolRAMTurnSnapshot
import OAI.Hierarchy.ProtocolRAMTurnChart

namespace OAI
/-! # Orientation and width of every original row, including dormant records -/

namespace Hierarchy.ProtocolRAMTurnSnapshot
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMTurnItinerary ProtocolRAMTurnChart
open scoped Fin.CommRing
variable {W N : ℕ}

theorem direction_binary (item : Expr) (d : Data) (m : Memory W) (x : Word W) :
    (direction item d).eval m x=0 ∨ (direction item d).eval m x=1 := by
  change (if _ then ((0:ℕ):Word W) else ((1:ℕ):Word W))=0 ∨ _
  split <;> simp_all [direction,Expr.eval]

theorem position_within (base bits : ℕ) (d : Data) (m : Memory W) (u : Fin N→Geometry) (i : Fin N)
    (header : Loaded base bits u m) (shape : (u i).raw ≤ (u i).length) (small : (u i).length < 2^W) :
    let p := chart base bits d
    p.position.eval m (i.val:Word W) ≤ p.length.eval m (i.val:Word W) := by
  intro p
  have len : (get base bits 2).eval m (i.val:Word W)=((u i).length:Word W) := header 2 i
  have raw : (get base bits 3).eval m (i.val:Word W)=((u i).raw:Word W) := header 3 i
  change (if _ then (get base bits 3).eval m (i.val:Word W) else
    (get base bits 2).eval m (i.val:Word W)-(get base bits 3).eval m (i.val:Word W)) ≤ (get base bits 2).eval m (i.val:Word W)
  rw [len,raw]
  split
  · change ((u i).raw:Word W).val ≤ ((u i).length:Word W).val
    simpa only [Fin.val_cast_of_lt (shape.trans_lt small),Fin.val_cast_of_lt small] using shape
  · rw [←Nat.cast_sub shape]
    change (((u i).length-(u i).raw:ℕ):Word W).val ≤ ((u i).length:Word W).val
    rw [Fin.val_cast_of_lt ((Nat.sub_le ..).trans_lt small),Fin.val_cast_of_lt small]
    exact Nat.sub_le ..

theorem width (base bits : ℕ) (d : Data) (m : Memory W) (u : Fin N → Geometry) (i : Fin N)
    (header : Loaded base bits u m) :
    (turn (chart base bits d) m i).width=(d.oldWidth.read m ((u i).item:Word W)).val := by
  have item : (get base bits 0).eval m (i.val:Word W)=((u i).item:Word W) := header 0 i
  exact congrArg (fun z : Word W=>(d.oldWidth.read m z).val) item

theorem observed_chart (header bits out : ℕ) (d : Data) (u : Fin N→Geometry) (m : Memory W) (b : Banks)
    (loaded : Loaded header bits u m) (shape : ∀i,(u i).raw ≤ (u i).length)
    (small : ∀i,(u i).length < 2^W) (one : 1<2^W)
    (fit : ∀ f,(field (chart header bits d) b f).Fits W out) (room : out+7*N < 2^W) :
    let p := chart header bits d
    let r := fun i : Fin N=>turn p m i
    let v := values b m
    ∃ endMem,(program W out N p b).Exec m endMem (ticks out N p b) ∧
      (∀ (i : Fin N) (f : Fin 7), f=4 ∨ (r i).field v 4≠0 →
        endMem (out+f.val*N+i.val)=((r i).field v f:Word W)) ∧
      ∀ a,a<out ∨ out+7*N≤a → endMem a=m a := by
  exact observed out _ b m one fit room
    (fun i=>position_within header bits d m u i loaded (shape i) (small i))
    (fun i=>direction_binary _ d m _)

end Hierarchy.ProtocolRAMTurnSnapshot

end OAI
