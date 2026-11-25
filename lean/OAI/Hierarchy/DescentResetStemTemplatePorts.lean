import OAI.Hierarchy.DescentResetStemPortData
import OAI.Hierarchy.DescentExprScale
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Compile the public local endpoint templates of a closed reset to native row expressions -/
namespace Hierarchy.DescentResetStemTemplatePorts
open DescentResetStemIncidence ProtocolRAM
open DescentPackedColony (target)
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- The host and predecessor indices are stored once per physical dense actor.
The three adjacency columns keep their original order, multiplicity and sentinel. -/
structure Banks where
  here : Bank
  parent : Bank
  neighbors : Fin 3 → Bank
  hub : Bank

variable {K H oldH palette w : ℕ}

def pack (v : Fin oldH) (i : Fin palette) : Fin (oldH*palette) := finProdFinEquiv (v,i)

theorem pack_val (v : Fin oldH) (i : Fin palette) :
    (pack v i).val = i.val+palette*v.val := rfl

def scene (here : Fin H → Fin (oldH*palette)) (parent : Fin H → Fin oldH)
    (near : Fin (oldH*palette) → Fin 3 → Option (Fin (oldH*palette)))
    (hub : Fin oldH → Bool) (template : Fin K → Option (Fin palette × Fin palette)) :
    Scene K H (oldH*palette) where
  here := here
  near := near
  ends j r := (template j).map fun z => (pack (parent r) z.1,pack (parent r) z.2)
  oldHub _ r := hub (parent r)

/-- A shape-known missing candidate emits the pitch sentinel, and a live one emits
the template coordinate plus the public pitch times the runtime predecessor. -/
def endpoint (parent : Bank) (oldH palette : ℕ) (component : Fin palette × Fin palette → Fin palette) :
    Option (Fin palette × Fin palette) → Expr
  | none => .lit (oldH*palette)
  | some z => .op .add (.lit (component z).val) (DescentPortFlow.scale (.lookup parent .row) palette)

def ports (B : Banks) (oldH : ℕ) (template : Fin K → Option (Fin palette × Fin palette)) : DescentResetStemIncidence.Ports K where
  here := .lookup B.here .row
  near i := .lookup (B.neighbors i) (.lookup B.here .row)
  src j := endpoint B.parent oldH palette Prod.fst (template j)
  dst j := endpoint B.parent oldH palette Prod.snd (template j)
  oldHub _ := .lookup B.hub (.lookup B.parent .row)

structure Room (B : Banks) (H oldH palette w stop : ℕ) : Prop where
  here : B.here.Fits w stop
  here_size : H ≤ B.here.size
  parent : B.parent.Fits w stop
  parent_size : H ≤ B.parent.size
  near : ∀ i, (B.neighbors i).Fits w stop
  near_size : ∀ i, oldH*palette ≤ (B.neighbors i).size
  hub : B.hub.Fits w stop
  hub_size : oldH ≤ B.hub.size

structure Stored (B : Banks) (here : Fin H → Fin (oldH*palette)) (parent : Fin H → Fin oldH)
    (near : Fin (oldH*palette) → Fin 3 → Option (Fin (oldH*palette)))
    (hub : Fin oldH → Bool) (m : Memory w) : Prop where
  here_word : ∀ r, m (B.here.base+r.val) = ((here r).val : Word w)
  parent_word : ∀ r, m (B.parent.base+r.val) = ((parent r).val : Word w)
  neighbor_word : ∀ i v, m ((B.neighbors i).base+v.val) = (target (near v i) : Word w)
  hub_word : ∀ v, m (B.hub.base+v.val) = ((hub v).toNat : Word w)

theorem endpoint_read (bank : Bank) (parent : Fin oldH) (rowWord : Word w) (m : Memory w)
    (loaded : bank.read m rowWord=(parent.val : Word w)) (pick : Fin palette × Fin palette → Fin palette)
    (entry : Option (Fin palette × Fin palette)) :
    (endpoint bank oldH palette pick entry).eval m rowWord =
      (target (entry.map fun z => pack parent (pick z)) : Word w) := by
  cases entry with
  | none => rfl
  | some pair =>
    simp only [endpoint, Expr.eval, DescentPortFlow.scale_eval, loaded, RowOp.opcode, BinaryOp.eval,
      target, Option.map_some, Option.elim_some, pack_val, Nat.cast_add, Nat.cast_mul]

theorem endpoint_fits (B : Bank) (pitch size : ℕ) (pick : Fin size × Fin size → Fin size)
    (entry : Option (Fin size × Fin size)) {stop : ℕ} (fit : B.Fits w stop) :
    (endpoint B pitch size pick entry).Fits w stop := by
  cases entry with
  | none => trivial
  | some z => exact ⟨trivial,DescentPortFlow.scale_fits (.lookup B .row) size ⟨fit,trivial⟩⟩

/-- Construct the incidence reader directly from its four physically loaded tables. -/
theorem read (B : Banks) (here : Fin H → Fin (oldH*palette)) (parent : Fin H → Fin oldH)
    (near : Fin (oldH*palette) → Fin 3 → Option (Fin (oldH*palette))) (hub : Fin oldH→Bool)
    (template : Fin K→Option (Fin palette×Fin palette)) (m : Memory w) {stop : ℕ}
    (room : Room B H oldH palette w stop) (live : Stored B here parent near hub m) :
    DescentResetStemIncidence.Reads (ports B oldH template) (scene here parent near hub template) m := by
  have current (r : Fin H) : B.here.read m (r.val : Word w)=((here r).val : Word w) :=
    (DescentPackedZip.bank_read B.here m (r.isLt.trans_le room.here_size) room.here).trans (live.here_word r)
  have prev (r : Fin H) : B.parent.read m (r.val : Word w)=((parent r).val : Word w) :=
    (DescentPackedZip.bank_read B.parent m (r.isLt.trans_le room.parent_size) room.parent).trans (live.parent_word r)
  constructor
  · exact current
  · intro r i
    change (B.neighbors i).read m (B.here.read m (r.val : Word w))=_
    rw [current]
    exact (DescentPackedZip.bank_read _ m ((here r).isLt.trans_le (room.near_size i)) (room.near i)).trans
      (live.neighbor_word i (here r))
  · intro j r
    have h := endpoint_read B.parent (parent r) (r.val : Word w) m (prev r) Prod.fst (template j)
    simpa only [ports, scene, Option.map_map, Function.comp_def] using h
  · intro j r
    have h := endpoint_read B.parent (parent r) (r.val : Word w) m (prev r) Prod.snd (template j)
    simpa only [ports, scene, Option.map_map, Function.comp_def] using h
  · intro j r
    change B.hub.read m (B.parent.read m (r.val : Word w))=_
    rw [prev]
    exact (DescentPackedZip.bank_read B.hub m ((parent r).isLt.trans_le room.hub_size) room.hub).trans
      (live.hub_word (parent r))

theorem fits (B : Banks) (oldH : ℕ) (template : Fin K→Option (Fin palette×Fin palette)) {stop : ℕ}
    (room : Room B H oldH palette w stop) : (ports B oldH template).All (Expr.Fits w stop) :=
  ⟨⟨room.here,trivial⟩, fun i=>⟨room.near i,room.here,trivial⟩,
   fun _=>endpoint_fits _ _ _ _ _ room.parent,fun _=>endpoint_fits _ _ _ _ _ room.parent,
   fun _=>⟨room.hub,room.parent,trivial⟩⟩

theorem endpoint_work (B : Bank) (pitch size : ℕ) (pick : Fin size × Fin size → Fin size)
    (entry : Option (Fin size × Fin size)) : (endpoint B pitch size pick entry).work ≤ 12+8*size := by
  cases entry with
  | none => change 1 ≤ 12+8*size;omega
  | some z =>
    simp only [endpoint,Expr.work,DescentPortFlow.scale_work]
    omega

/-- Literal endpoints use bounded local-size arithmetic. The bill has no factor
depending on the number of world vertices or groups. -/
theorem work (B : Banks) (oldH : ℕ) (template : Fin K→Option (Fin palette×Fin palette)) :
    (ports B oldH template).All (fun e => e.work ≤ 12+8*palette) := by
  refine ⟨?_,fun _ => ?_,fun _ => endpoint_work ..,fun _ => endpoint_work ..,fun _ => ?_⟩
  · change 7 ≤ 12+8*palette; omega
  · change 12 ≤ 12+8*palette; omega
  · change 12 ≤ 12+8*palette; omega

end
end Hierarchy.DescentResetStemTemplatePorts

end OAI
