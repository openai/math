import OAI.Hierarchy.DescentMaterialReceptionROM

namespace OAI
/-! The receiving sockets only read earlier numeric ranges, including at the last partial group. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route.Projection
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
private theorem atFits {w out : ℕ} (e j : Expr) (he : e.Fits w out) (hj : j.Fits w out) :
    (e.atRow j).Fits w out :=by
  induction e <;> simp_all [Expr.Fits,Expr.atRow]

variable {D a r H K G M w : ℕ} (base out : ℕ)
local notation "P" => breadth D
local notation "n" => K*chunks G M
local notation "b₁" => mapBase a r M base
local notation "b₂" => markBase a r M K G base
local notation "table₀" => table a r M base
local notation "mapB" => Route.bank K G M b₁
local notation "markB" => stampBank K G M b₂
local notation "s" => 2^Nat.clog 2 (n+1)
variable (end₀ : roof a r M K G (breadth D) base≤out) (width_ : out<2^w)
include end₀ width_ in
private theorem cols (f : Port) (p : Fin P) :
    (mapB).Fits w out ∧ n≤ (mapB).size ∧ (markB f p).Fits w out ∧ n≤(markB f p).size :=by
  have enough:n≤ s:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have numbers:b₂+(P+1)*s≤out:=end₀
  have index:= (stampId f p).isLt
  have total:=Nat.mul_le_mul_right s index
  rw [Nat.succ_mul (stampId f p).val] at total
  have allocated: (markB f p).base+(markB f p).size≤out:=by
    change b₂+(stampId f p).val*n+s≤_
    have:=Nat.mul_le_mul_left (stampId f p).val enough;omega
  have addr: (mapB).base+(mapB).size≤out:=by
    exact (Nat.le_add_right b₂ _).trans numbers
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (addr.trans_lt width_),addr⟩,enough,
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (allocated.trans_lt width_),allocated⟩,enough⟩

include end₀ width_ in
theorem socket_fit (B : DescentOrdinaryDonorRankDirectory.Banks) (ports : Ports P) (src : Bank)
    (f : Port) (p : Fin P) (i : Fin r) (prior : Accessible (keepPorts B ports) src H G M w out) :
    DescentPackedZip.Fits (table₀ f i) (lift mapB (H*chunks G M) (peerExpr (keepPorts B ports) src H p))
      (.lookup (markB f p) .row) (a*r) a M out w :=by
  obtain ⟨bankOk,_,markers,_⟩:=cols (K:=K) (a:=a) (r:=r) (G:=G) (M:=M) base out end₀ width_ f p
  have sep:b₁≤out:=(Nat.le_add_right b₁ (mapB).size).trans bankOk.2.2
  have baseFits (j : Fin 2): (ROM.bank (pages a r M) (width a r M) base (pageId (gated f) i j)).Fits w out :=
    ROM.bank_room (pages a r M) (width a r M) base _ (pageId (gated f) i j) (pageFit ..) sep width_
  have head: (Expr.lookup mapB .row).Fits w out:=⟨bankOk,trivial⟩
  have source:=peer_fits (keepPorts B ports) src out prior p
  have lhs:(lift mapB (H*chunks G M) (peerExpr (keepPorts B ports) src H p)).Fits w out :=
    ⟨head,trivial,trivial,atFits _ _ source head⟩
  exact ⟨lhs,⟨markers,trivial⟩,baseFits 0,baseFits 1,
    congrArg ROM.Page.bits (page_read (a:=a) (M:=M) (gated f) i 0),
    congrArg ROM.Page.bits (page_read (a:=a) (M:=M) (gated f) i 1)⟩

include end₀ width_ in
theorem source_at (R : Fin H→Fin D→Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks)
    (ports : Ports P) (src : Bank) (f : Port) (p : Fin P) (i : Fin r)
    (x : Fin H→Fin (G*r)→Cell a) (pitch : ℕ) (m : Memory w) (hm : 0<M) (hr : 0<r)
    (old : Reads src x (M*r) ((stage H K G M P a r pitch base w).image m)) (prior : Accessible (keepPorts B ports) src H G M w out)
    (mounted : Mounted ports (Gather.reaching R) ((stage H K G M P a r pitch base w).image m) G M) (ranks : DescentOrdinaryDonorRankDirectory.Reads R B ((stage H K G M P a r pitch base w).image m))
    (cap : H*chunks G M<2^w) :
    Source (projected B ports src mapB (markB f p) H G M p (table₀ f i))
      (value (K:=K) R pitch p f i x) M ((stage H K G M P a r pitch base w).image m) :=by
  obtain ⟨static,read,stamp⟩:=installed H K G M a r pitch base m f p i
  obtain ⟨mFit,mSize,_,sSize⟩:=cols (K:=K) (a:=a) (r:=r) (G:=G) (M:=M) base out end₀ width_ f p
  exact Route.source R B ports src mapB (markB f p) pitch out ((stage H K G M P a r pitch base w).image m) p f i (table₀ f i) x hm hr old mounted ranks
    prior mFit mSize cap read sSize stamp static (socket_fit base out end₀ width_ B ports src f p i prior)

include end₀ width_ in
/-- The smaller operand pages are computed later than the material sockets.
Their donor source is new, but the map, stamp and projection tables are the
actual previously mounted ones. They can all be reused below their old roof. -/
theorem source_later (R : Fin H → Fin D → Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks)
    (ports : Ports P) (src : Bank) (f : Port) (p : Fin P) (i : Fin r)
    (x : Fin H → Fin (G*r) → Cell a) (pitch : ℕ) (m later : Memory w) (hm : 0<M) (hr : 0<r)
    (stable : ∀j,j<roof a r M K G P base → later j=(stage H K G M P a r pitch base w).image m j)
    (old : Reads src x (M*r) later) (prior : Accessible (keepPorts B ports) src H G M w out)
    (roster : Mounted ports (Gather.reaching R) later G M) (ranks : DescentOrdinaryDonorRankDirectory.Reads R B later)
    (cap : H*chunks G M<2^w) :
    Source (projected B ports src mapB (markB f p) H G M p (table₀ f i)) (value (K:=K) R pitch p f i x) M later := by
  let bound:=roof a r M K G P base
  have boundRoom : bound<2^w:=end₀.trans_lt width_
  obtain ⟨static,read,stamp⟩:=installed H K G M a r pitch base m f p i
  obtain ⟨mf,ms,sf,ss⟩:=cols (K:=K) (a:=a) (r:=r) (G:=G) (M:=M) base bound le_rfl boundRoom f p
  have cell (bank : Bank) (j : ℕ) (fit : bank.Fits w bound) (idx : j<bank.size) :
      later (bank.base+j)=(stage H K G M P a r pitch base w).image m (bank.base+j) :=
    stable _ ((Nat.add_lt_add_left idx _).trans_le fit.2.2)
  have sep:b₁≤bound:=(Nat.le_add_right b₁ (mapB).size).trans mf.2.2
  have tableFit (j : Fin 2): (ROM.bank (pages a r M) (width a r M) base (pageId (gated f) i j)).Fits w bound :=
    ROM.bank_room (pages a r M) (width a r M) base _ (pageId (gated f) i j) (pageFit ..) sep boundRoom
  have stored : Static (table₀ f i) (choose (a:=a) (gated f) i) M later := by
    constructor
    · intro j
      refine (cell _ j.val (tableFit 0) ?_).trans (static.1 j)
      change j.val<2^(pages a r M (pageId (gated f) i 0)).bits
      rw [page_read];exact j.isLt
    · intro j
      refine (cell _ j.val (tableFit 1) ?_).trans (static.2 j)
      change j.val<2^(pages a r M (pageId (gated f) i 1)).bits
      rw [page_read];exact j.isLt
  have extra:=cols (K:=K) (a:=a) (r:=r) (G:=G) (M:=M) base out end₀ width_ f p
  exact Route.source R B ports src mapB (markB f p) pitch out later p f i (table₀ f i) x hm hr old roster ranks prior
    extra.1 ms cap (fun q=>(cell _ _ mf ((row K G M q).isLt.trans_le ms)).trans (read q))
    ss (fun q=>(cell _ _ sf ((row K G M q).isLt.trans_le ss)).trans (stamp q)) stored
    (socket_fit base out end₀ width_ B ports src f p i prior)

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route.Projection

end OAI
