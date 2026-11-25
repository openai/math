import OAI.Hierarchy.DescentSharedBookScan

namespace OAI
/-! # Native host-by-shape rows contain the installed fallback ranks -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter DescentContacts DescentRelativeContacts DescentRouterSlots
open DescentFallbackRankRAM DescentFallbackShapeTable DescentNativeFallbackShapes DescentRosterOrder
open DescentSharedBookScan DescentIssuedTerminalId
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable {H w : ℕ} (vertex : V↪Fin H) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)
variable (roster : SourceFrame.Roster Z T pos ix hub g frame (vertex.trans Fin.valEmbedding) near n f B wire K flow Δ wt)
variable (peer : V→Fin Δ→Option V) (real : ∀v x,x∈near v ↔ ∃j,peer v j=some x)
variable (t : Z.Fallback) (S : DescentSharedBookScan.Chart) (m : Memory w) (out : ℕ)
variable (p : Fields (Z.k-T.commonDepth) (2^Z.n) Δ)
variable (rom : fixed S (Z.k-T.commonDepth) (2^Z.n) Δ H m)
variable (room : Room S (Z.k-T.commonDepth) (2^Z.n) Δ H w out)
variable (data : DescentNativeFallbackShapes.Stored S.shapes (Z.k-T.commonDepth)
    (32*Nat.clog 2 (2*Δ)) g f (2^Z.n) (2^Ht) m)
variable (old : ∀ (u : V) (j : Fin Δ), m (S.neighbors.base+((vertex u).val*Δ+j.val))=
    (hostDigit vertex (peer u j):Word w))
variable (flags : ∀ u : V, m (S.isHub.base+(vertex u).val)=((hub u).toNat:Word w))
variable (ww : 0<w)
variable (src : decode (Z.k-T.commonDepth) (2^Z.n) p.1.val=(shortName T.commonDepth (T.code t)).2)
variable (available : ∀i h', h'∈DescentFallbackLeafScan.localShape (Z.k-T.commonDepth)
    (32*Nat.clog 2 (2*Δ)) g f (shortName T.commonDepth (T.code t)).2 i → shapeNumber h'+1<2^w)

local notation "seedName" => shortName T.commonDepth (T.code t)
local notation "oldVertex" => frame.host.symm (Prod.fst (shortName T.commonDepth (T.code t)))
local notation "bookHost" => vertex oldVertex
local notation "bookArg" => ((Fin.val (DescentSharedBookScan.absolute bookHost p)):Word w)
local notation "bookMemory" => ProtocolRAM.image out (H*DescentSharedBookScan.width (Z.k-T.commonDepth) (2^Z.n) Δ)
    (DescentSharedBookScan.expr S H Δ (2^Ht)) m
local notation "queryRow" => out + Fin.val (DescentSharedBookScan.absolute bookHost p)
local notation "hostCode" => frame.host.symm.toEmbedding.trans vertex

include roster real rom room data old flags ww src available in
theorem shared_book_at (y : Z.V×DescentContacts.Endpoint (2^Z.n)) (dst sh : Expr)
    (dest : (dst.eval m bookArg).val=(hostCode y.1).val) (tag : (sh.eval m bookArg).val=shapeNumber y.2) :
    (measure (side S) (shapes S) H (Δ:=Δ) (cap:=2^Ht) none).eval m bookArg=((T.leaves.window (seedName)).card:Word w) ∧
      (measure (side S) (shapes S) H (Δ:=Δ) (cap:=2^Ht) (some (dst,sh))).eval m bookArg=
        ((Finset.univ.filter (fun q : ↥(T.leaves.window (seedName))=>endpoint T.columns.host q.val<endpoint T.columns.host y)).card:Word w) := by
  let peerExpr:=fun j : Fin Δ=>side S j
  let markExpr:=fun j : Fin Δ=>Expr.lookup S.isHub (side S j)
  have received j : (side S j).eval m bookArg=(hostDigit vertex (peer oldVertex j):Word w) :=
    (nb_read S out m rom room bookHost p j (.lit j.val) rfl).trans (old oldVertex j)
  refine shared_book_measure frame vertex near n f B wire K Δ wt flow roster peer real t S.shapes m bookArg
    (ctl S .depth) (ctl S .offset) (ctl S .opt) peerExpr markExpr data ww room.word ?_ ?_ ?_ ?_ ?_ available y dst sh dest tag
  · simpa [datum,src] using ctl_read S out m rom room bookHost p .depth
  · simpa [datum,src] using ctl_read S out m rom room bookHost p .offset
  · simpa [datum,src] using ctl_read S out m rom room bookHost p .opt
  · intro j
    cases pj : peer oldVertex j <;>
      simpa [peerExpr,hostDigit,pj] using received j
  · intro j b atB
    obtain ⟨u,pu,rfl⟩:=Option.map_eq_some_iff.mp atB
    have rv : (side S j).eval m bookArg=((vertex u).val:Word w) := by simpa [pu,hostDigit] using received j
    simpa [markExpr] using (lookup_nat S.isHub m bookArg (side S j) (vertex u).val rv
      ((vertex u).isLt.trans_le room.flag.2) room.flag.1.2.1).trans (flags u)

include roster real rom room data old flags ww src available in
theorem shared_book_total (zero : p.2.1.val=0) : bookMemory queryRow=((T.leaves.window (seedName)).card:Word w) := by
  have one : shapeNumber (((0,0),none) : DescentContacts.Endpoint (2^Z.n))=0:=rfl
  let z₀ : Z.V×DescentContacts.Endpoint (2^Z.n):=((seedName).1,((0,0),none))
  have result:=shared_book_at frame vertex near n f B wire K Δ wt flow roster peer real t S m out p rom room data old flags ww src available
    z₀ (.lit (bookHost).val) (.lit 0) (by exact Fin.val_cast_of_lt ((bookHost).isLt.trans room.word)) (by simp [z₀,one,Expr.eval])
  rw [ProtocolRAMGeneratedWrite.read_image,DescentSharedBookScan.expr]
  simp only [Expr.eval,DescriptorExpr.Comparison.test,ctl_read S out m rom room,datum,zero,Fin.natCast_zero,beq_self_eq_true,ite_true]
  exact result.1

include roster real rom room data old flags ww src available in
theorem shared_book_prefix (j : Fin Δ) (u : V) (present : peer oldVertex j=some u) (index : p.2.1.val=j.val+1)
    (targetRoom : shapeNumber (decode (Z.k-T.commonDepth) (2^Z.n) p.2.2.val)<2^w) :
    let y:=(frame.host u,decode (Z.k-T.commonDepth) (2^Z.n) p.2.2.val)
    bookMemory queryRow=
      ((Finset.univ.filter (fun q : ↥(T.leaves.window (seedName))=>endpoint T.columns.host q.val<endpoint T.columns.host y)).card:Word w) := by
  let y:=(frame.host u,decode (Z.k-T.commonDepth) (2^Z.n) p.2.2.val)
  have ix:=(ctl_read S out m rom room bookHost p .slot)
  change (ctl S .slot).eval m bookArg=(p.2.1.val:Word w) at ix
  have sel : (slot S).eval m bookArg=((vertex u).val:Word w) := by
    apply (nb_read S out m rom room bookHost p j _ _).trans
    · simpa [present,hostDigit] using old oldVertex j
    · change (ctl S .slot).eval m bookArg-1=(j.val:Word w)
      rw [ix,index,Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
  have none : (ctl S .slot).eval m bookArg≠0 := by
    intro eqn
    have val:=congrArg Fin.val (ix.symm.trans eqn)
    rw [Fin.val_cast_of_lt (p.2.1.isLt.trans room.deg), Fin.val_zero] at val
    omega
  have live : (slot S).eval m bookArg≠(H:Word w) := by
    intro hx
    have hv := congrArg Fin.val (sel.symm.trans hx)
    rw [Fin.val_cast_of_lt ((vertex u).isLt.trans room.word),Fin.val_cast_of_lt room.word] at hv
    exact (vertex u).isLt.ne hv
  have result:=shared_book_at frame vertex near n f B wire K Δ wt flow roster peer real t S m out p rom room data old flags ww src available
    y (slot S) (ctl S .destShape) (by rw [sel,Fin.val_cast_of_lt ((vertex u).isLt.trans room.word)];simp [y])
    (by rw [ctl_read S out m rom room];exact Fin.val_cast_of_lt targetRoom)
  rw [ProtocolRAMGeneratedWrite.read_image,DescentSharedBookScan.expr]
  simp only [Expr.eval,DescriptorExpr.Comparison.test,Fin.natCast_zero,beq_iff_eq,none,live,ite_false]
  exact result.2

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
