import OAI.Hierarchy.DescentOperandResetPublic
import OAI.Hierarchy.DescentPrivateOldDonors
import OAI.Hierarchy.DescentSeedRectangleOrder

namespace OAI
/-! # The selected original cable and aligned word in the installed reset recipes -/
namespace Hierarchy.DescentResetFreshWires
open DescentKernelHistory DescentBundleHistory DescentResetTrunks DescentResetAttachments
open DescentNamedContact DescentRouterBank DescentOrderedWords DescentResetPointerFields Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {n d L p : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
    (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
    (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
    (whole : ∀e,p∣N.width e) (hp : 0<p)
local notation "combinedGraph" => network N home group R

/-- The first relay argument reads the ordered trunk interval of the moved edge.
The second reads the same old edge at the new stem, beginning at its first word. -/
def relayRef (h : H) (e : Fibre (moved N home) h) (side : Fin 2) (j : Fin (N.width e.val/p)) :
    BlockRef p (boundaryWidth (combinedGraph) (.inl (true,h))) :=
  let old : Aligned p (N.width e.val):=⟨j.val,(Nat.mul_le_mul_right p j.isLt).trans_eq (Nat.div_mul_cancel (whole e.val))⟩
  let width (a : Fibre (moved N home) h):=N.width a.val
  let ordered:=DescentOrderedReset.fibreKey key (moved N home) h
  let packed:=inside ordered width (fun a=>whole a.val) e old
  if side.val=0 then ⟨.inl ⟨.inr (.inl h),Or.inr rfl⟩,packed.row,packed.fits⟩
  else ⟨.inl ⟨.inl (true,e.val),Or.inl (congrArg (fun t=>Sum.inl (true,t)) e.property)⟩,j.val,old.fits⟩

variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)
    (src : ∀v,Shape p (old v)) (dev : ∀v,Shape p (bank v))
local notation "installed" => trunkShape N home group R key whole hp old bank src dev
local notation "relayWord" => relayRef N home group R key whole

private theorem whole_names {α : Type} (xs : List α) :
    (xs.map (Slice.whole (p:=p) hp)).flatMap Slice.names = xs := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.map_cons,List.flatMap_cons,ih]
    simp [Slice.names,Slice.whole,List.ofFn_succ]

private theorem at_index {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (List.ofFn f)[i.val]? = some (f i) := by
  simp [i.isLt]

omit [Fintype Q] in
theorem relay_key_at (h : H) (e : Fibre (moved N home) h) (side : Fin 2) (j : Fin (N.width e.val/p)) :
    ((installed (.inl (true,h))).keys e)[(finProdFinEquiv (side,j)).val]?=
      some (.inl (relayWord h e side j)) :=by
  let read (a : Fin 2) (z : Fin (N.width e.val/p)) :=
    Sum.inl (β:=BlockRef p (relay N home group R key h).hiddenWidth) (relayWord h e a z)
  have leg (a : Fin 2) :
      (List.ofFn (fun z => Slice.whole hp (read a z))).flatMap Slice.names = List.ofFn (read a) := by
    simpa only [List.map_ofFn,Function.comp_def] using whole_names hp (List.ofFn (read a))
  have sheet : (installed (.inl (true,h))).keys e =
      List.ofFn (fun index : Fin (2*(N.width e.val/p))=>
        let pair:=finProdFinEquiv.symm index
        read pair.1 pair.2):=by
    rw [←DescentPackedSeed.Rectangle.flattened read]
    unfold Shape.keys Shape.rows
    rw [List.flatMap_def,List.map_ofFn]
    exact congrArg List.flatten (congrArg List.ofFn (funext leg))
  let atSlot (i : Fin (2*(N.width e.val/p))) := read (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  let index := finProdFinEquiv (side,j)
  have hit := at_index atSlot index
  have point : atSlot index = read side j :=
    congrArg (fun ab => read ab.1 ab.2) (finProdFinEquiv.symm_apply_apply (side,j))
  exact (congrArg (fun xs => xs[index.val]?) sheet).trans (hit.trans (congrArg some point))


omit [Fintype Q] in
theorem relay_fields_at (h : H) (e : Fibre (moved N home) h) (side : Fin 2) (j : Fin (N.width e.val/p)) :
    let ref:=relayWord h e side j
    (ref.port.map Subtype.val Subtype.val,ref.block)=
      if side.val=0 then
        (.inl (.inr (.inl h)),offset (DescentOrderedReset.fibreKey key (moved N home) h)
          (fun a : Fibre (moved N home) h=>N.width a.val) e/p+j.val)
      else (.inl (.inl (true,e.val)),j.val) :=by
  by_cases same : side.val=0 <;> simp [relayRef,same,inside]

omit [Fintype Q] in
/-- The bank pullback applies exactly the charged ordered installer to the pre-reset word. -/
theorem device_key_at (v : R.Site) (u : (bank v).Node) (j : ℕ)
    (r : BlockRef p (boundaryWidth R v)) (read : ((dev v).keys u)[j]?=some (.inl r)) :
    ((installed (.inr v)).keys u)[j]?=some (.inl (bankField hp N home group R key whole v r)) :=by
  change (((dev v).reroute (bankBlockMap N home group R key whole hp v)).keys u)[j]?=_
  let move := Sum.map (bankBlockMap N home group R key whole hp v).map
    (id : BlockRef p (bank v).hiddenWidth → _)
  have shape := reroute_keys (dev v) (bankBlockMap N home group R key whole hp v) u
  have hit := List.getElem?_map (f:=move) (l:=(dev v).keys u) (i:=j)
  refine (congrArg (fun xs => xs[j]?) shape).trans (hit.trans ?_)
  rw [read]
  exact congrArg (fun b => some (Sum.inl b)) (firstBlock_eq hp _ _ r).symm


private theorem source_ref {G : Network n P bits} {site : G.Site}
    (a : BlockRef p (boundaryWidth G site)) (s : Incident G site) (g : ℕ)
    (fit : (g+1)*p≤G.width s.val)
    (atSource : (a.port.map Subtype.val Subtype.val,a.block)=(.inl s.val,g)) :
    a=⟨.inl s,g,fit⟩ :=by
  rcases a with ⟨i|pin,j,fits⟩
  · have edges : i.val=s.val:=Sum.inl.inj (congrArg Prod.fst atSource)
    have row : j=g:=congrArg Prod.snd atSource
    cases Subtype.ext edges
    cases row
    rfl
  · have impossible : (Sum.inr pin.val : G.Edge ⊕ P) = Sum.inl s.val := congrArg Prod.fst atSource
    cases impossible

omit [Fintype Q] in
/-- At the selected flattened relay operand this is the exact incident, including its subword. -/
theorem relay_face_at (h : H) (e : Fibre (moved N home) h) (side : Fin 2) (j : Fin (N.width e.val/p))
    (target : Incident (combinedGraph) (.inl (true,h))) (word : ℕ) (fits : (word+1)*p≤(combinedGraph).width target.val)
    (slot : (if side.val=0 then
        (.inl (.inr (.inl h)),offset (DescentOrderedReset.fibreKey key (moved N home) h)
          (fun a : Fibre (moved N home) h=>N.width a.val) e/p+j.val)
      else (.inl (.inl (true,e.val)),j.val))=(Sum.inl (β:=P) target.val,word)) :
    ((installed (.inl (true,h))).keys e)[(finProdFinEquiv (side,j)).val]?=
      some (.inl ⟨.inl target,word,fits⟩) :=by
  rw [relay_key_at]
  apply congrArg some
  apply congrArg Sum.inl
  exact source_ref _ target word fits ((relay_fields_at N home group R key whole h e side j).trans slot)

omit [Fintype Q] in
theorem device_wire_at (v : R.Site) (u : (bank v).Node) (j : ℕ) (e : Incident R v)
    (g : ℕ) (fit : (g+1)*p≤R.width e.val) (read : ((dev v).keys u)[j]?=some (.inl ⟨.inl e,g,fit⟩))
    (target : Incident (combinedGraph) (.inr v)) (edgeAt : target.val=.inr (.inr e.val))
    (fits : (g+1)*p≤(combinedGraph).width target.val) :
    ((installed (.inr v)).keys u)[j]?=some (.inl ⟨.inl target,g,fits⟩) :=by
  rw [device_key_at N home group R key whole hp old bank src dev v u j _ read]
  apply congrArg some
  apply congrArg Sum.inl
  apply source_ref
  rw [edgeAt]
  exact bank_at_wire hp N home group R key whole v e g fit

omit [Fintype Q] in
theorem device_socket_at (v : R.Site) (u : (bank v).Node) (j : ℕ) (port : Attached R v)
    (g : ℕ) (fit : (g+1)*p≤publicWidth group N.width port.val)
    (read : ((dev v).keys u)[j]?=some (.inl ⟨.inr port,g,fit⟩)) :
    let order:=DescentOrderedReset.fibreKey key (group port.val.1) port.val.2
    let widths:=fun e : Fibre (group port.val.1) port.val.2=>N.width e.val
    let r : BlockRef p (boundaryWidth R v):=⟨.inr port,g,fit⟩
    let t:=(DescentOrderedWords.address order widths).symm (r.atBit ⟨0,hp⟩).2
    ∀(target : Incident (combinedGraph) (.inr v)) (_edgeAt : target.val=.inl (port.val.1,t.1.val))
      (fits : (t.2.val/p+1)*p≤(combinedGraph).width target.val),
      ((installed (.inr v)).keys u)[j]?=some (.inl ⟨.inl target,t.2.val/p,fits⟩) :=by
  intro order widths r t target edgeAt fits
  rw [device_key_at N home group R key whole hp old bank src dev v u j r read]
  apply congrArg some
  apply congrArg Sum.inl
  apply source_ref
  rw [edgeAt]
  exact bank_at_pin hp N home group R key whole v port g fit

end
end Hierarchy.DescentResetFreshWires

end OAI
