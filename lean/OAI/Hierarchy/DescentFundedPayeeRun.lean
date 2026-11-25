import OAI.Hierarchy.DescentFundedSparseAtlas
import OAI.Hierarchy.DescentFundedTrunkReceipts
import OAI.Hierarchy.DescentClosedFallbackPay

namespace OAI
/-! # Native reset funding at every sparse host and common block -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentDenseHostOrder DescentPaidResidentCount
open DescentSIMDLookup DescentPackedZip DescentFundedCensus DescentPacking.PackedMatch.Local.Stage
open DescentSharedCableNames DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open DescentPaidResidentCount.Reset DescentCommonPalette DescentCommonHost DescentRelativeContacts
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
  {p b H M w:ℕ} (r:B.Recorded p) (oldRoom:Fintype.card cap.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => cap.placement
local notation "host" => cap.vertex.trans (Fin.castLEEmb oldRoom)
local notation "rank" => (B.frame.host.symm.toEmbedding.trans cap.vertex).trans (Fin.castLEEmb oldRoom)
local notation "grains" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T grains
local notation "cc" => (T).commonDepth
local notation "dep" => GroupStage.depthBound D n f g
local notation "relative" => ((Z).k-cc)
local notation "dim" => (S.groupWidth k tail i+k)
local notation "small" => (dim-cc)
local notation "pool" => DescentDenseHostOrder.roster (Z).graph relative dep
local notation "dataW" => (A).wire*((A).z*G.b)*(A).cap
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "idx" u:arg => (Z).hostFields T rank ((Z).placed T u)
local notation "N" => (Z).resetNames T
local notation "lit" => Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)
local notation "v₀" t:arg => B.frame.host.symm (((T).code t).1)
local notation "hi₀" t:arg => (Z).rootBlock T (.inr t)
local notation "oldIx" t:arg l:arg => (rearrange B.frame.basis).symm (join fit (hi₀ t) l)
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "count₀" => Census.count A (Equiv.refl _) host b
variable {fBits header field wide : ℕ}
local notation "s" => (⟨(pool).card,H,2^cc,M,b,wide⟩:Shape)
local notation "vals" => AtlasValues (Z).n relative (pool).card H (2^cc) b (A).degree (A).cap field header
variable (io : DescentFundedCensus.Ports (B.reset.k-B.terminals.commonDepth) B.reset.n)
  (flag : Fin (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth)
    (GroupStage.depthBound D n f g)).card → Expr)
  (v : AtlasValues B.reset.n (B.reset.k-B.terminals.commonDepth) (DescentDenseHostOrder.roster B.reset.graph
    (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)).card H (2^B.terminals.commonDepth)
    b cap.placement.degree cap.placement.cap field header)
local notation "job" => fun j=>compile (Ht:=dep) (Z).graph C (Z).width ((Z).unit/p) b (A).cap f (A).degree (A).cap
  field header io (flag j) (shapes B j)
local notation "av" => atlasValues («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p)
  (oldCap:=(A).cap) (f:=f) (Z).graph (shapes B) io flag v

private theorem two_operands {a b r s₁ n : ℕ} (equal : r=s₁) (u : Cell (a*2^r)) (v : Cell (b*2^r))
    (u' : Cell (a*2^s₁)) (v' : Cell (b*2^s₁)) (old : HEq u u') (amt : HEq v v') :
    (trunk a b (2^r) n).apply u v=(trunk a b (2^s₁) n).apply u' v' :=by
  subst s₁
  rw [eq_of_heq old,eq_of_heq amt]

/-- These are earlier paid, signed, stencil, presence and root input rows.
All five receipts refer to printed inputs before the atlas instruction. -/
structure Observed (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ) : Prop where
  present : ∀j h g,v.present j h g=lit j h g
  panel : ∀t,HEq (v.stencil (host (v₀ t)) (hi₀ t))
    (encode header (2^small) (Recorded.realPanel (reset:=B) rfl B.frame.basis fBits header (v₀ t) (hi₀ t)))
  previous : ∀t,HEq (v.old (host (v₀ t)) (hi₀ t)) (encode b (2^small)
    (fun l=>count₀ (host (v₀ t)) ((digits (oldIx t l)).1) ((digits (oldIx t l)).2)))
  incoming : ∀t,∃ports:Fin (2*(A).cap)→Fin (2^small)→Cell sig,
    (∀j l,ports j l=DescentSignedCableCodec.encode (Stage.signedPanel A order S cap.valid names
      ((((digits (oldIx t l)).1),v₀ t),(digits (oldIx t l)).2) j)) ∧
    HEq (v.relay (host (v₀ t)) (hi₀ t)) (encode b (2^small) (fun l=>((∑j,Arrivals.bit (A).degree (A).cap (ports j l):ℕ):Cell b)))
  root : ∀side t,Original B t (v.bank side ((Z).fallLabel T t,((T).code t).2.2) (host (v₀ t)) (hi₀ t))

variable {order : W.graph.Edge↪ℕ} {names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ}
  (observed : Observed (fBits:=fBits) B oldRoom v order names)
  (up : small<2^fBits) (one : 1<2^fBits) (enough : 2^small*dataW<2^fBits)
  (legal : 2*DescentFallbackShapeTable.rows small (2^(Z).n)≤2^header)
  (active : 0<dataW) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
  (paid : dataW<2^b) (arrivals : 2*(A).cap<2^b)

include observed up one enough legal active quotaPos degreePos paid arrivals in
theorem funded_cell (j : Fin (pool).card) (h₀ : Fin H) (hi : DescentColonies.Block cc) :
    quantity («s»:=s) job av j h₀ hi=payable B r oldRoom (finProdFinEquiv (h₀,j)) hi :=by
  apply funded_complete B r oldRoom
  · intro u
    have yes : v.present (idx u).2 (idx u).1 ((Z).blockId T u)=1 := (observed.present ..).trans (funded_present B oldRoom u)
    have tag:=funded_shape B oldRoom u
    have rel : relative=small:=by rw [B.keyWidth]
    let decode := Sum.elim (fun st : Bool × (Z).Fallback => Node.trunk st.1 (shortName cc ((T).code st.2)))
      (bankNode (Z).placement (Z).graph cc (T).code (Z).positive (Z).pay (Z).circuit d)
    have decoded (o) (eqn : N u = o) : (Z).commonName T u = decode o := congrArg decode eqn
    cases kind:N u with
    | inl st=>
      obtain ⟨side,t⟩:=st
      have tag' := tag.trans (congrArg (DescentDenseHostOrder.shape (Z).graph) (decoded _ kind))
      have hv : (idx u).1=host (v₀ t):=by
        exact congrArg (fun nm => rank (position (Z).graph nm)) (decoded _ kind)
      have hb : (Z).blockId T u=hi₀ t:=by
        apply Fin.ext
        change DescentCommonHost.rawCoordinate _ _ _ _ _ _ _ _ (N u)=_
        rw [kind]
        rfl
      have out:=trunk_value («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p) (oldCap:=(A).cap) (f:=f)
        (Z).graph (shapes B) io flag v (idx u).2 (idx u).1 ((Z).blockId T u) side ((),(shortName cc ((T).code t)).2) tag' yes
      rw [out,hv,hb]
      cases side with
      | false=>
        exact (two_operands rel _ _ _ _ (observed.panel t) (observed.previous t)).trans
          (primary_payout B r host up one enough legal active quotaPos degreePos t paid)
      | true=>
        obtain ⟨ports,physical,value⟩:=observed.incoming t
        exact (two_operands rel _ _ _ _ (observed.panel t) value).trans
          (relay_payout B r up one enough legal active quotaPos degreePos t order names ports physical arrivals)
    | inr bank=>
      obtain ⟨⟨side,z₀⟩,a⟩:=bank
      cases z₀ with
      | inl goodRoot=>
        have tag' := tag.trans (congrArg (DescentDenseHostOrder.shape (Z).graph) (decoded _ kind))
        have eqn:=good_value («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p) (oldCap:=(A).cap) (f:=f)
          (Z).graph (shapes B) io flag v (idx u).2 (idx u).1 ((Z).blockId T u) side _ (BankIssue.goodRotorSite (Z) side goodRoot a) tag' yes
        exact eqn.trans (congrArg (fun z:ℕ => (z:Cell b)) (middle_good_fixed B r side goodRoot a))
      | inr t=>
        let path:=DescentCommonPalette.path a
        let label:=(shortName cc ((T).code t)).2
        have height_ok:path.length≤dep:=by
          simpa [path,DescentCommonPalette.path] using (Nat.le_trans (Nat.le_of_lt_succ a.1.isLt) ((T).bookHeight side t))
        have fitLabel : label.1.1≤relative ∧ label.1.2<2^label.1.1 ∧ path.length≤dep:=
          ⟨Nat.sub_le_sub_right ((T).codeLegal t).2.1 cc,Nat.mod_lt _ (Nat.two_pow_pos _),height_ok⟩
        have tag' := tag.trans (congrArg (DescentDenseHostOrder.shape (Z).graph) (decoded _ kind))
        have hv : (idx u).1=host (v₀ t):=by
          change rank (position (Z).graph ((Z).commonName T u))=_
          exact congrArg (fun nm=>rank (position (Z).graph nm)) (decoded _ kind)
        have hb : (Z).blockId T u=hi₀ t:=by
          apply Fin.ext
          change DescentCommonHost.rawCoordinate _ _ _ _ _ _ _ _ (N u)=_
          rw [kind]
          rfl
        have out:=fall_value («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p) (oldCap:=(A).cap) (f:=f)
          (Z).graph (shapes B) io flag v (idx u).2 (idx u).1 ((Z).blockId T u) side label path tag' yes fitLabel
        rw [out,hv,hb]
        have exactPay:=middle_tree_paid B r field side t a _ (observed.root side t)
        have pathSite {left right : Σ e, Fin e → Bool} (same : left=right)
            (hl : left.1≤dep) (hr : right.1≤dep) :
            (BankIssue.Site.tree ⟨left.1,Nat.lt_succ_of_le hl⟩ left.2 : BankIssue.Site (Z).graph dep) =
            BankIssue.Site.tree ⟨right.1,Nat.lt_succ_of_le hr⟩ right.2 := by
          subst right
          rfl
        have node := pathSite (left:=⟨path.length,path.get⟩) (right:=⟨a.1.val,a.2⟩)
          (Fin.sigma_eq_of_eq_comp_cast (by simp [path, DescentCommonPalette.path])
            (funext fun i => List.get_ofFn a.2 i)) height_ok
          ((Nat.le_of_lt_succ a.1.isLt).trans ((T).bookHeight side t))
        change BankIssue.Site.tree _ _ = BankIssue.Site.tree _ _ at node
        rw [node]
        exact congrArg (fun z:ℕ=>(z:Cell b)) exactPay
  · intro j h₀ hi blank
    apply no_charge («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p) (oldCap:=(A).cap) (f:=f)
      (Z).graph (shapes B) io flag v j h₀ hi
    exact (observed.present ..).trans blank

include observed up one enough legal active quotaPos degreePos paid arrivals in
theorem funded_read {base : ℕ} (m : Memory w) (fits : Room («s»:=s) job w base) (source : RawSources («s»:=s) io flag v m)
    (j : Fin (pool).card) (rowId : Row H (2^cc) M) :
    memory («s»:=s) job base m ((s).column base j+(row _ _ _ rowId).val)=
      (data (fun v hi=>payable (precision:=b) B r oldRoom (finProdFinEquiv (v,j)) hi) rowId).val :=by
  have out:=raw_read («s»:=s) (Ht:=dep) (C:=C) (packet:=(Z).width) (batch:=(Z).unit/p) (oldCap:=(A).cap) (f:=f)
    (Z).graph (shapes B) io flag v m fits source j rowId
  have eqn : quantity («s»:=s) job av j=fun v hi=>payable B r oldRoom (finProdFinEquiv (v,j)) hi :=
    funext fun h₀=>funext fun hi=>funded_cell B r oldRoom io flag v observed up one enough legal active quotaPos degreePos paid arrivals j h₀ hi
  simpa only [eqn] using out

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
