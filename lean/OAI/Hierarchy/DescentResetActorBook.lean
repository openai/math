import OAI.Hierarchy.DescentResetStencilActors
import OAI.Hierarchy.DescentSharedBookImage
import OAI.Hierarchy.DescentIssuedSharedBook

namespace OAI
/-! # Physical candidate counts for every legal fallback shape -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter DescentContacts DescentRelativeContacts DescentRouterSlots
open DescentFallbackRankRAM DescentFallbackShapeTable DescentNativeFallbackShapes DescentRosterOrder
open DescentSharedBookScan DescentIssuedTerminalId
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable {H w Δ : ℕ} (f : ℕ) (vertex : V↪Fin H) (peer : V→Fin Δ→Option V)
local notation "Y" => 2^Z.n
local notation "r" => Z.k-T.commonDepth
local notation "cap" => (2^Ht:ℕ)
local notation "actorDegree" => 32*Nat.clog 2 (2*Δ)
local notation "number" => frame.host.symm.toEmbedding.trans vertex
local notation "neighbors" => fun b (j : Fin Δ)=>(peer (frame.host.symm b) j).map frame.host
local notation "hub'" => fun b=>hub (frame.host.symm b)
variable (S : DescentSharedBookScan.Chart) (m : Memory w) (out : ℕ) (v : V) (p : Fields (Z.k-T.commonDepth) (2^Z.n) Δ)
local notation "host" => vertex v
local notation "z" => decode r Y p.1.val
local notation "e" => DescentSharedBookScan.expr S H Δ cap
local notation "loc" => (absolute host p).val
local notation "x" => (loc:Word w)
local notation "total" => (Finset.univ.filter (fun j : Fin Δ×Fin cap=>
      (DescentFallbackLeafScan.candidate (k:=r) (D:=actorDegree) (g:=g) (f:=f) hub' neighbors (frame.host v,z) j).isSome)).card

omit [Fintype V] [DecidableEq V] in
/-- No old edge, terminal or selected fallback witness is needed. The shared
zero-control row literally counts the legal distinct endpoint candidates. -/
theorem candidate_count (zero : p.2.1.val=0) (valid : z.1.1≤r ∧ z.1.2<2^z.1.1)
    (rom : fixed S r Y Δ H m) (room : Room S r Y Δ H w out)
    (data : DescentNativeFallbackShapes.Stored S.shapes r actorDegree g f Y cap m)
    (old : ∀ (u : V) (j : Fin Δ),m (S.neighbors.base+((vertex u).val*Δ+j.val))=(hostDigit vertex (peer u j):Word w))
    (flags : ∀u,m (S.isHub.base+(vertex u).val)=((hub u).toNat:Word w)) (ww : 0<w)
    (available : ∀i h',h'∈DescentFallbackLeafScan.localShape r actorDegree g f z i→shapeNumber h'+1<2^w) :
    ProtocolRAM.image out (H*DescentSharedBookScan.width r Y Δ) e m (out+loc)=(total:Word w) := by
  have sides (j : Fin Δ) : (side S j).eval m x=(hostDigit vertex (peer v j):Word w) :=
    (nb_read S out m rom room host p j (.lit j.val) rfl).trans (old v j)
  have peers (j : Fin Δ) : (side S j).eval m x=(hostDigit number (neighbors (frame.host v) j):Word w):=by
    cases orig : peer v j <;> simpa [hostDigit, orig] using sides j
  have read (j : Fin Δ×Fin cap) (u : Z.V) (hit : neighbors (frame.host v) j.1=some u) :
      ((shapes S j).eval m x).val=DescentFallbackShapeTable.encode (DescentFallbackLeafScan.localSlot
        (DescentFallbackLeafScan.localShape r actorDegree g f z (hub' u)) j.2) := by
    simp only [Equiv.symm_apply_apply] at hit
    obtain ⟨b,haveB,rfl⟩:=Option.map_eq_some_iff.mp hit
    have peerVal : (side S j.1).eval m x=((vertex b).val:Word w):=by simpa [haveB,hostDigit] using sides j.1
    have fire : (Expr.lookup S.isHub (side S j.1)).eval m x=((hub' (frame.host b)).toNat:Word w):=by
      simpa using (lookup_nat S.isHub m x (side S j.1) (vertex b).val peerVal ((vertex b).isLt.trans_le room.flag.2)
        room.flag.1.2.1).trans (flags b)
    unfold shapes
    rw [query_read S.shapes r actorDegree g f m x (ctl S .depth) (ctl S .offset) (ctl S .opt) (Expr.lookup S.isHub (side S j.1))
      z valid.1 valid.2 (hub' (frame.host b)) j.2 data ww
      (by simpa [datum] using ctl_read S out m rom room host p .depth)
      (by simpa [datum] using ctl_read S out m rom room host p .offset)
      (by simpa [datum] using ctl_read S out m rom room host p .opt) fire]
    apply Fin.val_cast_of_lt
    cases val : DescentFallbackLeafScan.localSlot (DescentFallbackLeafScan.localShape r actorDegree g f z (hub' (frame.host b))) j.2 with
    | none=>exact Nat.two_pow_pos _
    | some a=>exact available _ a (DescentFallbackLeafScan.localSlot_some.mp val).choose
  have real:=all_slots neighbors number hub' (frame.host v,z) m x (side S) (shapes S) room.word peers read
  rw [ProtocolRAMGeneratedWrite.read_image,DescentSharedBookScan.expr]
  simp only [Expr.eval,DescriptorExpr.Comparison.test,ctl_read S out m rom room,datum,zero,Fin.natCast_zero,beq_self_eq_true,ite_true]
  exact real

omit [Fintype V] [DecidableEq V] in
/-- Reading the emitted count as a bounded integer recovers the actual
site-independent (per high block) native height. -/
theorem candidate_height (wordFit : Δ*cap<2^w)
    (known : ProtocolRAM.image out (H*DescentSharedBookScan.width r Y Δ) e m (out+loc)=(total:Word w)) :
    Nat.clog 2 (ProtocolRAM.image out (H*DescentSharedBookScan.width r Y Δ) e m (out+loc)).val=heightAt frame f v z peer:=by
  have size : total≤Δ*cap:=by simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin Δ×Fin cap)) _)
  rw [known,Fin.val_cast_of_lt (size.trans_lt wordFit)]
  rfl

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
