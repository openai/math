import OAI.Hierarchy.DescentNativeFallbackShapes
import OAI.Hierarchy.DescentIssuedFallbackOrdinal

namespace OAI
/-! # Real book heights and bit ordinals on the selected reset frame -/

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter DescentRelativeContacts DescentRouterSlots
open DescentFallbackRankRAM DescentFallbackShapeTable DescentNativeFallbackShapes DescentRosterOrder
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable {H w : ℕ} (vertex : V↪Fin H) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)
local notation "ids" => vertex.trans Fin.valEmbedding
variable (roster : SourceFrame.Roster Z T pos ix hub g frame (vertex.trans Fin.valEmbedding) near n f B wire K flow Δ wt)
variable (peer : V→Fin Δ→Option V) (real : ∀v x,x∈near v ↔ ∃j,peer v j=some x)
local notation "code" => frame.host.symm.toEmbedding.trans vertex
local notation "r" => Z.k-T.commonDepth
local notation "cap" => (2^Ht:ℕ)
local notation "D" => 32*Nat.clog 2 (2*Δ)
local notation "name" => fun (t : Z.Fallback)=>shortName T.commonDepth (T.code t)
local notation "hub'" => fun v=>hub (frame.host.symm v)
local notation "row" => fun (v : Z.V) (j : Fin Δ)=>Option.map frame.host (peer (frame.host.symm v) j)
variable (s : Bool) (t : Z.Fallback) (S : DescentNativeFallbackShapes.Banks)
variable (m : Memory w) (x : Word w) (dpth off opt : Expr) (peers flags : Fin Δ→Expr)
local notation "z" => (name t).2
local notation "shapes" => fun j : Fin Δ×Fin cap=>query S cap dpth off opt (flags j.1) j.2.val
local notation "number" => (Finset.univ.filter (fun j : Fin Δ×Fin cap=>
      (DescentFallbackLeafScan.candidate (k:=r) («D» := D) (g:=g) (f:=f) hub' row (name t) j).isSome)).card

include roster real

/-- The common host table can be filled before any particular contact has
been selected. Its destination may be *any* normalized shape at an old
neighbor. The source terminal fixes the candidate-set bound uniformly. -/
theorem shared_book_measure (data : DescentNativeFallbackShapes.Stored S r D g f (2^Z.n) cap m)
    (ww : 0<w) (wide : H<2^w)
    (rd : dpth.eval m x=(z.1.1:Word w)) (ri : off.eval m x=(z.1.2:Word w))
    (rz : opt.eval m x=(optionDigit z.2:Word w))
    (rp : ∀j,(peers j).eval m x=(hostDigit code (row (name t).1 j):Word w))
    (rh : ∀j v,row (name t).1 j=some v→(flags j).eval m x=((hub' v).toNat:Word w))
    (available : ∀i h',h'∈DescentFallbackLeafScan.localShape r D g f z i → shapeNumber h'+1<2^w)
    (y : Z.V×DescentContacts.Endpoint (2^Z.n)) (dst sh : Expr)
    (dest : (dst.eval m x).val=(code y.1).val) (tag : (sh.eval m x).val=shapeNumber y.2) :
    (DescentFallbackRankRAM.measure peers shapes H none).eval m x=((T.leaves.window (name t)).card:Word w) ∧
      (DescentFallbackRankRAM.measure peers shapes H (some (dst,sh))).eval m x=
        ((Finset.univ.filter (fun p : ↥(T.leaves.window (name t))=>
          endpoint T.columns.host p.val<endpoint T.columns.host y)).card:Word w) := by
  have legal := T.codeLegal t
  have dfit : z.1.1≤r := Nat.sub_le_sub_right legal.2.1 _
  have ifit : z.1.2<2^z.1.1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have shapes_read (j : Fin Δ×Fin cap) (v : Z.V) (hit : row (name t).1 j.1=some v) :
      ((shapes j).eval m x).val=encode (DescentFallbackLeafScan.localSlot
        (DescentFallbackLeafScan.localShape r D g f z (hub' v)) j.2) := by
    rw [query_read S r D g f m x dpth off opt (flags j.1) z dfit ifit (hub' v) j.2 data ww rd ri rz (rh _ _ hit)]
    apply Fin.val_cast_of_lt
    cases eqn : DescentFallbackLeafScan.localSlot (DescentFallbackLeafScan.localShape r D g f z (hub' v)) j.2 with
    | none=>exact Nat.two_pow_pos _
    | some a=>exact available _ a (DescentFallbackLeafScan.localSlot_some.mp eqn).choose
  have agree : (code).trans Fin.valEmbedding=T.columns.host := by
    ext a
    obtain ⟨v,rfl⟩:=frame.host.surjective a
    simpa using (roster.1 v).symm
  have real':=actual_roster frame ids near n f B wire K Δ wt flow roster peer real
  have same:=roster.2.2.2.2.1 (name t)
  have room : (T.leaves.window (name t)).card≤cap :=
    (Nat.le_pow_clog (by decide : 1<2) _).trans
      (Nat.pow_le_pow_right (by decide) ((T.leaves.depth false t).symm.le.trans (T.bookHeight false t)))
  have before:=earlier_slots row code hub' (name t) m x peers shapes dst sh y wide rp shapes_read dest tag
  rw [agree] at before
  have «prefix»:=DescentFallbackLeafScan.scan_card T.columns.near hub' row real' (name t)
    (same ▸ room) (fun p=>decide (endpoint T.columns.host p<endpoint T.columns.host y))
  have all:=DescentFallbackLeafScan.scan_card T.columns.near hub' row real' (name t)
    (same ▸ room) (fun _=>true)
  have any (o : Option (Z.V×DescentContacts.Endpoint (2^Z.n))) : o.any (fun _=>true)=o.isSome := by cases o <;> rfl
  rw [←same] at all «prefix»
  simp only [any] at all
  constructor
  · rw [all_slots row code hub' (name t) m x peers shapes wide rp shapes_read,all]
    simp
  · rw [before,«prefix»]
    simp

/-- The three fields of the true local terminal and the old fixed-width aperture
are input operands. The candidate and its paired ordinal come from a public ROM. -/
theorem book_measure (data : DescentNativeFallbackShapes.Stored S r D g f (2^Z.n) cap m)
    (ww : 0<w) (wide : H<2^w)
    (rd : dpth.eval m x=(z.1.1:Word w)) (ri : off.eval m x=(z.1.2:Word w))
    (rz : opt.eval m x=(optionDigit z.2:Word w))
    (rp : ∀j,(peers j).eval m x=(hostDigit code (row (name t).1 j):Word w))
    (rh : ∀j v,row (name t).1 j=some v→(flags j).eval m x=((hub' v).toNat:Word w))
    (available : ∀i h',h'∈DescentFallbackLeafScan.localShape r D g f z i → shapeNumber h'+1<2^w)
    (e : LinkId Z.placement.owner s (.inr t)) (dst sh : Expr)
    (dest : (dst.eval m x).val=(code (name (opposite Z.placement s t e)).1).val)
    (tag : (sh.eval m x).val=shapeNumber (name (opposite Z.placement s t e)).2) :
    (Z.placement.fallbackBook s t).height=Nat.clog 2 number ∧
      (DescentFallbackRankRAM.measure peers shapes H none).eval m x=(number:Word w) ∧
      (DescentFallbackRankRAM.measure peers shapes H (some (dst,sh))).eval m x=
        ((DescentRotor.bitWord _ ((Z.placement.fallbackBook s t).codes e)).val:Word w) := by
  have legal := T.codeLegal t
  have dfit : z.1.1≤r := Nat.sub_le_sub_right legal.2.1 _
  have ifit : z.1.2<2^z.1.1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have shapes_read (j : Fin Δ×Fin cap) (v : Z.V) (hit : row (name t).1 j.1=some v) :
      ((shapes j).eval m x).val=encode (DescentFallbackLeafScan.localSlot
        (DescentFallbackLeafScan.localShape r D g f z (hub' v)) j.2) := by
    rw [query_read S r D g f m x dpth off opt (flags j.1) z dfit ifit (hub' v) j.2 data ww rd ri rz (rh _ _ hit)]
    apply Fin.val_cast_of_lt
    cases eqn : DescentFallbackLeafScan.localSlot (DescentFallbackLeafScan.localShape r D g f z (hub' v)) j.2 with
    | none=>exact Nat.two_pow_pos _
    | some a=>exact available _ a (DescentFallbackLeafScan.localSlot_some.mp eqn).choose
  have agree : (code).trans Fin.valEmbedding=T.columns.host := by
    ext a
    obtain ⟨v,rfl⟩:=frame.host.surjective a
    simpa using (roster.1 v).symm
  refine ⟨source_height frame ids near n f B wire K Δ wt flow roster peer real s t,
    all_slots row code hub' (name t) m x peers shapes wide rp shapes_read,?_⟩
  have rank:=earlier_slots row code hub' (name t) m x peers shapes dst sh (name (opposite Z.placement s t e))
    wide rp shapes_read dest tag
  rw [agree] at rank
  rw [source_leaf frame ids near n f B wire K Δ wt flow roster peer real s t e]
  exact rank

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
