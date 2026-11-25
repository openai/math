import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedSiteOrdinals
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! Both signed three-socket stencils, mounted once per original seed vertex. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentSharedCableNames
open Computability.BorderVNP.Crossing Catalyst
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k n : ℕ} (X : Approximation F k n)
local notation "N" => X.network.copyGraph

def atEnd (side : Bool) (e : Cable X) : Vertex X := if side then target N e else source N e
def paid : Cable X → Bool:=Sum.elim (fun _=>true) (fun _=>false)

omit [Field F] in
theorem belongs (side : Bool) (e : Cable X) : present X (atEnd X side e) e := by
  cases side <;> simp [present,atEnd]

theorem peer_short (v : Vertex X) (e : Cable X) (he : present X v e) : seedPeer X v e<3 := by
  have yes : other X v e∈near N v := by
    unfold other
    split
    · rename_i eqn;rw [←eqn];exact (wire_near N e).1
    · rename_i neq;rw [←he.resolve_left neq];exact (wire_near N e).2
  have sub : (near N v).filter (fun u=>index u< index (other X v e)) ⊂ near N v :=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).2 ⟨_,yes,by simp⟩
  exact (Finset.card_lt_card sub).trans_le ((«initialize» X).1 v)

def record (side : Bool) (e : Cable X) : Stage.Live 3 256 where
  neighbor := ⟨seedPeer X (atEnd X side e) e,peer_short X _ _ (belongs X side e)⟩
  wire := ⟨seedParallel X (atEnd X side e) e,(parallel_short X ..).trans_lt (by decide)⟩
  sourceWire := ⟨position X (source N e) e,(position_short X _ _ (Or.inl rfl)).trans (by decide)⟩
  within := 0
  target := side
  markedOut := !side && paid X e

theorem record_ext {D cap : ℕ} (a b : Stage.Live D cap) (hn:a.neighbor=b.neighbor)
    (hw:a.wire=b.wire) (hs:a.sourceWire=b.sourceWire) (hi:a.within=b.within)
    (ht:a.target=b.target) (hm:a.markedOut=b.markedOut) : a=b := by
  cases a;cases b;simp_all

def has (v : Vertex X) (side : Bool) (ord : ℕ) (e : Cable X) : Prop :=
  atEnd X side e=v ∧ position X v e=ord

def panel (v : Vertex X) (side : Bool) (ord : ℕ) : Option (Stage.Live 3 256) :=
  if hit : ∃ e,has X v side ord e then some (record X side hit.choose) else none

theorem at_wire (side : Bool) (e : Cable X) :
    panel X (atEnd X side e) side (position X (atEnd X side e) e)=some (record X side e) := by
  let v:=atEnd X side e
  have hit : ∃f,has X v side (position X v e) f:=⟨e,rfl,rfl⟩
  have own:=hit.choose_spec
  have there : present X v hit.choose :=
    Eq.mp (congrArg (fun t=>present X t hit.choose) own.1) (belongs X side hit.choose)
  have unique:=position_unique X v hit.choose e there (belongs X side e) own.2
  change (if _ : ∃f,has X v side (position X v e) f then _ else _)=_
  rw [dite_eq_left hit,unique]

theorem out_of_range (v : Vertex X) (side : Bool) {ord : ℕ} (large : 3≤ord) :
    panel X v side ord=none := by
  apply dite_eq_right
  rintro ⟨e,eqn,rank⟩
  rw [←eqn] at rank
  exact (Nat.not_lt_of_ge large) (rank ▸ position_short X _ _ (belongs X side e))

def panelAt (v : Vertex X) (s : Fin (2*256)) : Option (Stage.Live 3 256) :=
  let t := finProdFinEquiv.symm s
  panel X v (finTwoEquiv t.1) t.2.val

def socket : Vertex X × (Fin 2 × Fin 3) ≃ Fin (Fintype.card (Vertex X)*(2*3)) :=
  ((Fintype.equivFin _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def literal (j : ℕ) : ℕ :=
  if h : j<Fintype.card (Vertex X)*(2*3) then
    let a:=(socket X).symm ⟨j,h⟩
    (DescentSignedCableCodec.encode (panel X a.1 (finTwoEquiv a.2.1) a.2.2.val)).val
  else 0

def program (w at₀ : ℕ) := DescentStaticWordColumn.program w at₀ (literal X) (size X)
def image {w : ℕ} (at₀ : ℕ) (m : Memory w) := DescentStaticWordColumn.image at₀ (literal X) m (size X)

theorem mount {w : ℕ} (at₀ : ℕ) (m : Memory w) (space : at₀+size X<2^w) :
    (program X w at₀).Exec m (image X at₀ m) (4+10*size X) := DescentStaticWordColumn.mount at₀ (size X) (literal X) m space

theorem frame {w : ℕ} (at₀ : ℕ) (m : Memory w) (a : ℕ) (away : a<at₀ ∨ at₀+size X≤a) :
    image X at₀ m a=m a := DescentStaticWordColumn.frame at₀ (size X) (literal X) m a away

theorem read {w : ℕ} (at₀ : ℕ) (m : Memory w) (v : Vertex X) (side : Bool) (r : Fin 3) :
    image X at₀ m (at₀+(socket X (v,finTwoEquiv.symm side,r)).val)=
      ((DescentSignedCableCodec.encode (panel X v side r.val)).val : Word w) := by
  unfold image
  rw [DescentStaticWordColumn.read _ _ _ _ (socket X (v,finTwoEquiv.symm side,r)).isLt]
  let : Nonempty (Vertex X) := ⟨v⟩
  simp only [literal,dite_eq_left (socket X (v,finTwoEquiv.symm side,r)).isLt,
    Fin.eta,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
