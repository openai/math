import OAI.Hierarchy.TaggedWirePacketCatalogueControls
import OAI.Hierarchy.TaggedWireStripPacketCost

namespace OAI
/-! # Dated ballot cost from the real strip lookup, stored commodity and quantity expression -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Strip ProbeStage.CoreBoard.HistoryRoles
open WireTelescope StripPaths ChosenPackets.RowRouting PacketTurns
open scoped Classical BigOperators
variable {S : ProbeStage.PurchaseSampler} {h d k n D : ℕ} {A B : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (p : StripPorts S h d k (TreeColumn n) (Fin n) B)
    (extra : A⊕B→DistinctPair (TreeSite n k))
    (b : Board) (shift : ℕ) (site : TreeSite n k→Expr) (stock : A→Expr)
    (qty : (ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k)→Expr)
local notation "Rcount" => Fintype.card U
local notation "enum" => treeFirst R T
local notation "pr" => readPrimary stock shift (p.primary b)
local notation "ma" => emitterMate (A:=A) p b shift
local notation "tr" => emitterTree (A:=A) p b shift
local notation "menu" => menuInputs extra enum site pr ma tr qty

theorem menu_positions : Fintype.card ((i : Fin Rcount) × Fin (menuLen (enum i)))≤Rcount*2 := by
  simp only [Fintype.card_sigma,Fintype.card_fin]
  calc _≤∑ _ : Fin Rcount,2:=by
         apply Finset.sum_le_sum;intro i _
         rcases e:enum i with r|t
         · change (if _ then 2 else 1)≤2;split <;> decide
         · change 1 ≤ 2
           decide
       _=Rcount*2 :=by simp

def baseBound (B : ℕ) := 10*(2*B+16)+3

theorem StripPorts.menu_bound {bound : ℕ} (blocks : ∀c,(p.column c).work≤bound)
    (prim : ∀r:R,(p.primary b r).work≤bound) (mounted : ∀x,(site x).work≤bound)
    (held : ∀a,(stock a).work≤bound) (amount : ∀x,(qty x).work≤bound) : (menu).Bound (baseBound bound) := by
  let cap:=2*bound+16
  have fitsCap : bound ≤ cap := by dsimp [cap]; omega
  have m : ∀x,(site x).work≤cap:=fun x=>(mounted x).trans fitsCap
  have pay (r : R) : (PacketScan.add (.lit shift) (p.primary b r)).work≤cap:=by
    have a:=prim r;change 1+_+1≤_;unfold cap;omega
  have pfit (r : R) : (pr r).work≤cap := by
    cases r with
    | catalyst c j=>exact pay (.catalyst c j)
    | radius c j s=>exact pay (.radius c j s)
    | cross c j l r=>exact pay (.cross c j l r)
    | horizontal f l=>exact pay (.horizontal f l)
    | extra e=>cases e with
      | inl a=>exact (held a).trans fitsCap
      | inr x=>exact pay (.extra (.inr x))
  have mfit (c : C) (j : Fin k) : (ma c j).work≤cap := by
    have mf:=p.mate_work b bound blocks (.catalyst c j:R)
    change 1+_+1≤_;dsimp [cap];omega
  have tfit (x : T) : (tr x).work≤cap:=pay (treeRole n k x)
  have oldCap : 4*cap+1 ≤ baseBound bound := by dsimp [baseBound,cap]; omega
  have amountCap : bound ≤ baseBound bound := by dsimp [baseBound]; omega
  have edgeCap : 2*cap+2*cap+1 ≤ baseBound bound := by dsimp [baseBound,cap]; omega
  have endsCap : 2*cap+2*(4*cap+1)+1 ≤ baseBound bound := by dsimp [baseBound,cap]; omega
  refine ⟨?_,?_,?_,?_⟩
  · intro i v; exact (face_work site cap m _ v).trans oldCap
  · intro i; exact (amount (enum i)).trans amountCap
  · intro i j
    exact (routed_work extra site pr ma tr cap cap m pfit mfit tfit (enum i) j.val).trans edgeCap
  · intro i j v
    let ends := ColumnWires.ends (Strip.horizontal n) extra
    exact (routed_work extra site (fun r=>face site (ends (firstRole r)) v)
      (fun c a=>face site (ends (.radius c a true)) v)
      (fun t=>face site (treeEnds n k t) v) cap (4*cap+1) m
      (fun r=>face_work site cap m (ends (firstRole r)) v)
      (fun c a=>face_work site cap m (ends (.radius c a true)) v)
      (fun t=>face_work site cap m (treeEnds n k t) v) (enum i) j.val).trans endsCap

def catalogueWork (M D B : ℕ) := 128*(2*M+D+1)*(baseBound B+1)

theorem StripPorts.catalogueControls_work (M originalRows start shelfSize bits : ℕ) (siteBase : Bank) (participant : X)
    {bound : ℕ} (enough : Rcount≤M) (blocks : ∀c,(p.column c).work≤bound)
    (prim : ∀r:R,(p.primary b r).work≤bound) (mounted : ∀x,(site x).work≤bound)
    (held : ∀a,(stock a).work≤bound) (amount : ∀x,(qty x).work≤bound)
    (f : Fin ((M*3)*5+D)) :
    (p.catalogueControls extra b shift site stock qty M originalRows start shelfSize bits siteBase participant f).work≤
      catalogueWork M D bound := by
  let o:=menu
  let order:=(Fintype.equivFin ((i : Fin Rcount) × Fin (menuLen (enum i)))).symm
  let page (i:Fin 3) := pageRead (DatedRoleSheets.bank originalRows start shelfSize bits i) siteBase (site participant) (d:=D)
  have budget:=p.menu_bound extra b shift site stock qty blocks prim mounted held amount
  have siteFits:(site participant).work+12≤baseBound bound:=by have:=mounted participant;unfold baseBound;omega
  have ok (i : Fin 3) (q : Fin D) : (page i q).work≤baseBound bound:=by simpa [page,page_work] using siteFits
  have cost:=Operands.controls_work o order budget (page 0) (page 2) (site participant) (ok 0) (ok 2) (by omega) f
  have slots:=menu_positions (A:=A) (B:=B) (k:=k) (n:=n)
  apply cost.trans
  apply (Operands.controlWork_le ..).trans
  unfold catalogueWork
  gcongr; omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
