import OAI.ThreeFlat.Diagonal.CompressorGreedyColumns

namespace OAI
/-! # Each real color or tag row selects the prescribed least free value -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {B H : Type} [AddCommGroup H] {w N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {p : Pointers} {cell : Word w} {m : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ}
set_option quotPrecheck false
local notation "d" => S.degree
local notation "code" => fun v : B=>((b v).val:Word w)
variable (pub : Fin 1→Word w)

omit [AddCommGroup H] in
theorem Old.colorStep (h : Old S P b p cell prior m) (v : B) (colors : B → Fin (2*d+1))
    (palette : 2*d+1≤2^w) (one : (1:Word w)≠0)
    (range : p.colors+N≤2^w) (tab : ∀y,m (p.colors+(b y).val)=((colors y).val:Word w)) :
    let a:=vertexAddress (w:=w) b p.colors v
    (Template.emit cell (Template.color d)).eval pub m (fun _=>a) =
      ((Ordered.pick (Ordered.colorBan P.slots v colors) 0 (List.ofFn (Equiv.refl (Fin (2*d+1))))).val:Word w) := by
  let a:=vertexAddress (w:=w) b p.colors v
  let vs:=fun _ : Fin 1=>a
  let tabBase:=Template.emit cell (Template.f ShrinkStage.colors)
  have initial : tabBase.eval pub m vs=(p.colors:Word w) := by
    rw [Template.program_value]
    exact h.header.field vs 18
  have native : Template.emit cell (Template.color d)=colorRow d tabBase
      (Template.emit cell Template.g.dst) (Template.emit cell Template.g.src) := by
    rw [Template.emit_color]
    simp [ShrinkStage.color,tabBase,Template.g,oldColumns,column,Demand.formulaOps,termOps,
      Template.ptr,termField,oldGraph,oldSlots,atField,Template.emit,Template.bindCurrent,Formula.compile,terms]
  rw [native]
  apply color_val (G:=P.slots) v colors palette one pub m a tabBase (Template.emit cell Template.g.dst)
    (Template.emit cell Template.g.src) code
  · change a-tabBase.eval pub m vs=_
    rw [initial]
    change ((p.colors+(b v).val:ℕ):Word w)-(p.colors:Word w)=_
    rw [Nat.cast_add]; abel
  · intro y
    change m (tabBase.eval pub m vs+((b y).val:Word w)).val=_
    rw [initial,←Nat.cast_add,Fin.val_cast_of_lt ((Nat.add_lt_add_left (b y).isLt _).trans_le range)]
    exact tab y
  · exact h.neighbor pub vs false v
  · exact h.neighbor pub vs true v

omit [AddCommGroup H] in
theorem Sliced.tagStep (h : Sliced S P b p cell prior m) (v : B) (offsets : B → BitWord t)
    (tw : t≤w) (one : (1:Word w)≠0)
    (range : p.offsets+N≤2^w) (tab : ∀y,m (p.offsets+(b y).val)=tagWord tw (offsets y)) :
    let a:=vertexAddress (w:=w) b p.offsets v
    (Template.emit cell (Template.offset d t)).eval pub m (fun _=>a) =
      tagWord tw (Ordered.pick (Ordered.tagBan P.slots (shift P) v offsets) 0 (List.ofFn (tagOrdinal t).symm)) := by
  let a:=vertexAddress (w:=w) b p.offsets v
  let vs:=fun _ : Fin 1=>a
  let T:=Template.tagColumns cell
  have initial : T.offsets.eval pub m vs=(p.offsets:Word w) := by
    change (Template.emit cell (Template.f ShrinkStage.offsets)).eval pub m vs=_
    rw [Template.program_value]
    exact h.header.field vs 19
  have reads : TagReads T P.slots (shift P) offsets tw (fun y : B=>((b y).val:Word w)) pub m vs := by
    refine ⟨h.toOld.neighbor pub vs false,h.toOld.neighbor pub vs true,h.tag pub vs tw false,
      h.tag pub vs tw true,?_⟩
    intro y
    rw [initial,←Nat.cast_add,Fin.val_cast_of_lt ((Nat.add_lt_add_left (b y).isLt _).trans_le range)]
    exact tab y
  have addr : a-T.offsets.eval pub m vs=((b v).val:Word w) := by
    rw [initial]
    change ((p.offsets+(b v).val:ℕ):Word w)-(p.offsets:Word w)=_
    rw [Nat.cast_add]; abel
  rw [Template.emit_offset]
  exact offset_val reads v addr one


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
