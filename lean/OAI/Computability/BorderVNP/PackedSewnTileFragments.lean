import OAI.Computability.BorderVNP.PackedSewnFragmentSource
import OAI.Computability.BorderVNP.PackedInheritedLayerCircuit
import OAI.Computability.BorderVNP.DiagonalExternalTileRows
import OAI.Computability.BorderVNP.DiagonalExternalGridHosts

/-! # Six typed public fragment slots per original team and tile

The static descriptors use the original grouped port, the true free port,
or the named end of the unique sewn exterior cable. The physical site
number and both local word starts are read from dynamic addressed columns.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.Tile

open Diagonal.ExternalSew Diagonal.ExternalSew.TileRuns Diagonal.ExternalSew.GridHosts
open CellAddressCircuit Inherited ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {R r field link g V groups copies old : ℕ}

/-- Row-major sparse rectangle, with the six probes varying fastest. -/
def ordinal (R V : ℕ) : (Fin (R+1) × Fin V × Fin 6) ≃ Fin (6*(R+1)*V) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans (finCongr (by ring))

/-- Parameter-only fragment operands, with both directory coordinates bounded. -/
structure Item (p m n : ℕ) where
  /-- The previous grouped port whose input contains this interval. -/
  port : Fin p
  /-- First lane of this interval within the previous grouped port. -/
  offset : ℕ
  /-- Number of consecutive lanes in the interval. -/
  span : ℕ
  /-- New port or cable end supplying the interval, when it has a source. -/
  endpoint : Option (End m n)
  /-- First lane within the new supplying port or cable end. -/
  displacement : ℕ

/-- A genuine tile interval in the row-major physical schema. A low cable
endpoint selects the source and a high endpoint selects the destination. -/
def item (count : groups*copies=R+1) (u : Fin (R+1)) (tile : Fin V) (old : ℕ)
    (hg : 0<g) (small : g≤link) (room : r*(2*field+R*link)≤V*g)
    (a : Run R r field link g u tile.val) : Item (groups*V) (old+4*(R+1)*V) ((R+1)*V) :=
  let group := teamBlocks groups copies count u
  let dst := match a.kind with
    | .zero => none
    | .free => some (.inr (finProdFinEquiv (u,tile)))
    | .cable side c => some (Layer.edgeEnd (FourSlot.pieceOrdinal old V hg small (by omega) room c) (!side))
  ⟨finProdFinEquiv (group.1,tile),group.2.val*g+a.first,a.width,dst,(match a.kind with | .free => a.first | _ => 0)⟩

/-- Recover the numerical metadata of the published `copyRows` schema. -/
def Item.target {p m n : ℕ} (a : Item p m n) : Target :=
  match a.endpoint with
  | none => .zero
  | some (.inl (.inl e)) => .wire false e.val
  | some (.inl (.inr e)) => .wire true e.val
  | some (.inr port) => .port port.val

theorem item_metadata (count : groups*copies=R+1) (u : Fin (R+1)) (tile : Fin V) (old : ℕ)
    (hg : 0<g) (small : g≤link) (room : r*(2*field+R*link)≤V*g)
    (a : Run R r field link g u tile.val) :
    let b := item count u tile old hg small room a
    copyRow u tile copies old hg small room a =
      ⟨b.port.val,u.val%copies,b.offset,b.span,b.target,b.displacement⟩ := by
  intro b
  have parts := teamBlocks_coordinates groups copies count u
  have first := congrArg Prod.fst parts
  have second := congrArg Prod.snd parts
  change ((teamBlocks groups copies count) u).1.val = _ at first
  change ((teamBlocks groups copies count) u).2.val = _ at second
  cases h : a.kind with
  | zero | «free» =>
    simp [b,item,copyRow,h,Item.target,finProdFinEquiv_apply_val,first,second,Nat.mul_comm,Nat.add_comm]
  | cable side c =>
    cases side <;> simp [b,item,copyRow,h,Item.target,Layer.edgeEnd,finProdFinEquiv_apply_val,first,second,Nat.mul_comm,Nat.add_comm]

/-- The exact interval installed at one reserved public address. -/
noncomputable def slot (count : groups*copies=R+1) (old : ℕ) (hg : 0<g) (small : g≤link)
    (room : r*(2*field+R*link)≤V*g) (i : Fin (6*(R+1)*V)) :
    Option (Item (groups*V) (old+4*(R+1)*V) ((R+1)*V)) :=
  let a := (ordinal R V).symm i
  ((runs (r:=r) (w:=field) a.1 a.2.1.val hg small)[a.2.2.val]?).map (item count a.1 a.2.1 old hg small room)

/-- Each of the six fixed probes reads exactly the corresponding `copyRows` entry. -/
theorem slot_metadata (count : groups*copies=R+1) (old : ℕ) (hg : 0<g) (small : g≤link)
    (room : r*(2*field+R*link)≤V*g) (u : Fin (R+1)) (v : Fin V) (j : Fin 6) :
    (slot count old hg small room (ordinal R V (u,v,j))).map (fun b =>
      CopyRow.mk b.port.val (u.val%copies) b.offset b.span b.target b.displacement) =
      (copyRows u v copies old hg small room)[j.val]? := by
  unfold slot
  rw [Equiv.symm_apply_apply]
  simp only [copyRows,List.getElem?_map,Option.map_map]
  have h : (fun b => CopyRow.mk b.port.val (u.val%copies) b.offset b.span b.target b.displacement) ∘
      item count u v old hg small room = copyRow u v copies old hg small room := by
    funext a
    exact (item_metadata count u v old hg small room a).symm
  rw [h]

/-- Physical input wires for the old port owner and start, and the new
endpoint start. All three banks use most-significant-first words. -/
structure Inputs (σ : Type*) (p m n w : ℕ) where
  /-- Public bits of the original host site number for each old port. -/
  owner : Fin p → Fin w → σ
  /-- Public bits of the within-site base address of each old port. -/
  oldStart : Fin p → Fin w → σ
  /-- Public bits of the new within-site base address of each cable end or port. -/
  newStart : End m n → Fin w → σ

variable {σ : Type*} {p m n w slots : ℕ} [Fintype σ] (f : Inputs σ p m n w)

/-- The actual source site and interval obtained from the addressed bit columns. -/
def Inputs.parsed (x : σ → Bool) (a : Item p m n) : Parsed :=
  ⟨value (x ∘ f.owner a.port),⟨value (x ∘ f.oldStart a.port)+a.offset,a.span,
    a.endpoint.map fun e => value (x ∘ f.newStart e)+a.displacement⟩⟩

/-- The interval widths and both addressed starts are representable in the public word. -/
def Inputs.Fits (x : σ → Bool) (a : Item p m n) : Prop :=
  value (x ∘ f.oldStart a.port)+a.offset < 2^w ∧ a.span < 2^w ∧
    ∀ e, a.endpoint=some e → value (x ∘ f.newStart e)+a.displacement < 2^w

private def lit (v : ℕ) (j : Fin w) : Expr σ := .const (v.testBit (w-1-j.val))

private def plus (v : Fin w → σ) (a : ℕ) := addWord (fun j => .input (v j)) (lit a)

private def scalar (a : Item p m n) (k : Fin 4) : Fin w → Expr σ :=
  ![(fun j => .input (f.owner a.port j)),plus (f.oldStart a.port) a.offset,lit a.span,
    (match a.endpoint with | none => lit 0 | some e => plus (f.newStart e) a.displacement)] k

private def expr (rows : Fin slots → Option (Item p m n)) : Pin slots w → Expr σ
  | (i,c) => match rows i with
    | none => .const false
    | some a => match c with
      | .inl false => .const (decide (0<a.span))
      | .inl true => .const a.endpoint.isSome
      | .inr (k,j) => scalar f a k j

/-- Actual shared Boolean circuit. Each scalar is a selection or one
ordinary word addition with a static lane offset. -/
noncomputable def frame (rows : Fin slots → Option (Item p m n)) : Frame σ (Pin slots w) :=
  (Frame.initial id).step (expr f rows)

private theorem eval_expr (rows : Fin slots → Option (Item p m n)) (x : σ → Bool) (i : Pin slots w) :
    (frame f rows).eval x i = (expr f rows i).eval x := by
  have h : (Frame.initial (id : σ → σ)).eval x = x := funext (Frame.initial_eval id x)
  simp only [frame,Frame.step_eval,h]

omit [Fintype σ] in
private theorem plus_size (v : Fin w → σ) (a : ℕ) (j : Fin w) : (plus v a j).size ≤ 16*w+22 :=
  sumWord_size_le false _ _ 1 (fun _ => le_rfl) (fun _ => le_rfl) _

/-- All probes cost linearly in the number of rows and quadratically in
the word width, including every inactive slot. -/
theorem frame_size (rows : Fin slots → Option (Item p m n)) :
    (frame f rows).size ≤ slots*(2+4*w)*(16*w+22) := by
  have each (i : Pin slots w) : (expr f rows i).size ≤ 16*w+22 := by
    obtain ⟨r,b|⟨k,j⟩⟩ := i
    · cases h : rows r <;> cases b <;> simp [expr,h,StatementCircuit.Expr.size]
    · cases h : rows r with
      | none => simp [expr,h,StatementCircuit.Expr.size]
      | some a =>
        simp only [expr,h]
        fin_cases k <;> first | exact plus_size .. | (change 1≤16*w+22; omega) | skip
        change ((match a.endpoint with | none => lit 0 | some e => plus (f.newStart e) a.displacement) j).size ≤ _
        cases a.endpoint <;> first | exact plus_size .. | (change 1≤16*w+22; omega)
  simpa only [frame,Frame.initial_size,zero_add,Pin,Column,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Fintype.card_sum] using Frame.step_size_le (Frame.initial (id : σ → σ)) (expr f rows) _ each

/-- The active flag is precisely a present interval of positive width. -/
theorem active_iff (rows : Fin slots → Option (Item p m n)) (x : σ → Bool) (i : Fin slots) :
    active ((frame f rows).eval x) i = true ↔ ∃ a, rows i=some a ∧ 0<a.span := by
  cases h : rows i <;> simp [active,eval_expr,expr,h,StatementCircuit.Expr.eval]

omit [Fintype σ] in
private theorem lit_value (x : σ → Bool) (a : ℕ) (fit : a<2^w) : wordValue x (lit (w:=w) a) = a :=
  (ParseRecords.bigValue_testBit w a).trans (Nat.mod_eq_of_lt fit)

omit [Fintype σ] in
private theorem plus_value (x : σ → Bool) (v : Fin w → σ) (a : ℕ) (fit : value (x ∘ v)+a<2^w) :
    wordValue x (plus v a) = value (x ∘ v)+a := by
  have constant := lit_value x a ((Nat.le_add_left _ _).trans_lt fit)
  have sum := addWord_value x (fun j => .input (v j)) (lit a) (by rw [constant]; exact fit)
  change wordValue x (addWord _ _) = wordValue x (fun j => .input (v j)) + a
  simpa only [constant] using sum

/-- For every true address the four emitted words give the actual source
site and the two within-site intervals. -/
theorem parse_eq (rows : Fin slots → Option (Item p m n)) (x : σ → Bool) {i : Fin slots} {a : Item p m n}
    (row : rows i = some a) (fit : f.Fits x a) : parse ((frame f rows).eval x) i = f.parsed x a := by
  have field (j : Fin 4) : word (fun c => (frame f rows).eval x (i,c)) j = wordValue x (scalar f a j) := by
    simp [word,eval_expr,expr,row,wordValue]
  have fst := plus_value x (f.oldStart a.port) a.offset fit.1
  have width := lit_value (w:=w) x a.span fit.2.1
  have owner : word (fun c => (frame f rows).eval x (i,c)) 0 = value (x ∘ f.owner a.port) := (field 0).trans rfl
  have off : word (fun c => (frame f rows).eval x (i,c)) 1 = value (x ∘ f.oldStart a.port)+a.offset :=
    (field 1).trans fst
  have span : word (fun c => (frame f rows).eval x (i,c)) 2 = a.span := (field 2).trans width
  have flag : (frame f rows).eval x (i,.inl true) = a.endpoint.isSome := by simp [eval_expr,expr,row,StatementCircuit.Expr.eval]
  simp only [parse,parseRow,owner,off,span,flag,Inputs.parsed]
  cases ht : a.endpoint with
  | none => rfl
  | some e =>
    have src := plus_value x (f.newStart e) a.displacement (fit.2.2 e ht)
    have last := field 3
    change _ = wordValue x (match a.endpoint with | none => lit 0 | some e => plus (f.newStart e) a.displacement) at last
    rw [ht] at last
    simp only [last,src,Option.isSome_some,ite_true,Option.map_some]

end Packing.SewnField.Fragment.Tile

end BorderVNP
end Computability
end OAI
