import OAI.Hierarchy.DescentPrimitiveBirthLayout
import OAI.Hierarchy.DescentOperandCandidateLookup
import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentResetRetainedPlacementRead

namespace OAI
/-! # Relocating guarded earlier root-opcode digits at their original physical pitch -/
namespace Hierarchy.DescentPrimitiveBirth
open DescentSIMDLookup DescentPackedZip DescentPackedSumWords
open DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

theorem zero {H G a w M : ℕ} (m : Memory w) : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell a)) M m:=by
  intro p
  have h : (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell a)) p).val=0:=by
    simp [lanes_val]
  simp only [Expr.eval, h, Fin.natCast_zero]

theorem totalFits {K w hi} (src : Fin K→Expr) (fit : ∀i,(src i).Fits w hi) : (total src (List.finRange K)).Fits w hi:=by
  generalize eq:List.finRange K=xs
  clear eq
  induction xs with
  | nil=>trivial
  | cons i xs ih=>exact ⟨fit i,ih⟩

theorem oneHot {H G w M a K} (src : Fin K→Expr) (m : Memory w) (which : Fin H→Fin G→Option (Fin K))
    (v : Fin K→Fin H→Fin G→Cell a)
    (read : ∀i,Source (src i) (fun h g=>if which h g=some i then v i h g else 0) M m) :
    Source (total src (List.finRange K)) (DescentOperandCandidateLookup.selected which v) M m:=by
  intro p
  have each i:=read i p
  have sum:=eval_sum _ _ m _ each (List.finRange K)
  rw [←List.ofFn_eq_map,List.sum_ofFn,DescentOperandCandidateLookup.packed_select which v p] at sum
  exact sum

namespace Layout
variable (z : Layout) {w U : ℕ}
local notation "P" => z.placement
local notation "d" => z.rootBits*z.stop
abbrev Guards :=Fin z.roots→Fin (z.residual+1)→Option Bank

def digit (n : Fin z.nodes) (value : Cell d) : Cell z.rootBits :=
  if h:n.val<z.stop then (encode z.rootBits z.stop).symm value ⟨n.val,h⟩ else 0

theorem digit_zero (n : Fin z.nodes) : z.digit n 0=0:=by
  have blank : encode z.rootBits z.stop (fun _ => 0) = 0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin z.stop => (0 : Cell z.rootBits))).val = 0
    simp []
  have unpack : (encode z.rootBits z.stop).symm 0 = (fun _ => 0) :=
    (encode z.rootBits z.stop).symm_apply_eq.mpr blank.symm
  simp [digit, unpack]

def digitPage (n : Fin z.nodes) : Book.Gate:=⟨d,0,z.rootBits,fun x _=>z.digit n x⟩
def mounts (floor w : ℕ) :=Book.install z.digitPage d z.sourceLanes w floor
def mounted (floor : ℕ) (m : Memory w) :=Book.image z.digitPage d z.sourceLanes floor m
def field (floor : ℕ) (n : Fin z.nodes) (src : Option Bank) : Expr :=
  src.elim (.lit 0) (fun bank=>(Book.tables z.digitPage d z.sourceLanes floor n).read (.lookup bank .row) (.lit 0))
def rootWord (floor : ℕ) (guard : z.Guards) (q : Fin (z.roots*z.nodes)) : Expr :=
  let j : Fin z.roots×Fin z.nodes:=finProdFinEquiv.symm q
  total (fun l=>z.field floor j.2 (guard j.1 l)) (List.finRange (z.residual+1))

variable (base : ℕ) (guard : z.Guards) (count inv : Bank)
local notation "head" => z.liftBase base
def rootCode (w : ℕ) :=(z.mounts base w).seq ((P).code z.batch head w (fun _=>true) (z.rootWord base guard) count inv)
def rootTime :=4+10*(z.nodes*(2*2^(d*z.sourceLanes)))+(P).ticks z.batch head (z.rootWord base guard) count inv
def rootMem (m : Memory w) :=(P).image z.batch head (fun _=>true) (z.rootWord base guard) count inv (z.mounted base m)
def rootBank (n : Fin z.nodes) (x : Fin (P).blocks) (root : Fin z.roots) :=(P).bank z.batch head (finProdFinEquiv (root,n)) x

def GuardsFit (w : ℕ) :=∀i j B,guard i j=some B→B.Fits w base

theorem lift_le : z.liftBase base≤z.lifted base:=by rw [lifted,(P).affine];exact Nat.le_add_right ..

private theorem fieldFit (n : Fin z.nodes) {src : Option Bank} (fit : ∀B,src=some B→B.Fits w base) (room : head<2^w) :
    (z.field base n src).Fits w head:=by
  cases src with
  | none=>trivial
  | some B=>
    have a:=Book.geometry z.digitPage d z.sourceLanes base n (out:=head) le_rfl room (by simp [digitPage])
    have p:=fit B rfl
    exact ⟨a.2,trivial,a.1,⟨⟨p.1,p.2.1,p.2.2.trans (Nat.le_add_right ..)⟩,trivial⟩⟩

theorem rootFit (f : z.GuardsFit base guard w) (room : head<2^w) (q) : (z.rootWord base guard q).Fits w head:=by
  apply totalFits
  intro j
  exact z.fieldFit base _ (f _ j) room

structure RootRoom (w : ℕ) : Prop where
  old : z.GuardsFit base guard w
  count : count.Fits w base
  inverse : inv.Fits w base
  lanes : 0<(P).lanes
  blocks : 0<(P).blocks
  roof : z.lifted base<2^w

variable (r : z.RootRoom base guard count inv w)
include r in
theorem rootAny (m : Memory w) :
    (z.rootCode base guard count inv w).Exec m (z.rootMem base guard count inv m) (z.rootTime base guard count inv) ∧
    CheapCode (z.rootCode base guard count inv w) ∧ ∀i,i<base ∨ z.lifted base≤ i→z.rootMem base guard count inv m i=m i:=by
  have room:=(z.lift_le base).trans_lt r.roof
  have start : base≤head:=Nat.le_add_right ..
  obtain ⟨mountRun,_,mountFrame,mountCheap⟩:=
    DescentPackedZip.Book.mount z.digitPage d z.sourceLanes base m (fun _=>by simp [digitPage]) room
  have bank {B : Bank} (p : B.Fits w base) : B.Fits w head:=⟨p.1,p.2.1,p.2.2.trans start⟩
  obtain ⟨placeRun,placeFrame,placeCheap⟩:=(P).any z.batch head (fun _=>true) (z.rootWord base guard) count inv (z.mounted base m)
    r.lanes r.blocks (z.rootFit base guard r.old room) (bank r.count) (bank r.inverse) r.roof
  refine ⟨@Procedure.Exec.then w (z.mounts base w)
    ((P).code z.batch head w (fun _=>true) (z.rootWord base guard) count inv)
    m (z.mounted base m) (z.rootMem base guard count inv m)
    (4+10*(z.nodes*(2*2^(d*z.sourceLanes)))) ((P).ticks z.batch head (z.rootWord base guard) count inv)
    (@mountRun) (@placeRun),?_,?_⟩
  · intro labels regs slots pc reg pub exit i
    exact @cheap_seq w (z.mounts base w)
      ((P).code z.batch head w (fun _=>true) (z.rootWord base guard) count inv)
      (@mountCheap) (@placeCheap) labels regs slots pc reg pub exit i
  · intro i hi
    exact (placeFrame i (hi.imp_left (fun h=>h.trans_le start))).trans
      (mountFrame i (hi.imp_right (fun h=>(z.lift_le base).trans h)))

abbrev Population :=Fin (P).oldHosts→Fin ((P).groups*(P).blocks)→Option (Fin (z.residual+1))
abbrev Original :=Fin z.roots→Fin (z.residual+1)→Fin (P).oldHosts→Fin ((P).groups*(P).blocks)→Cell d

/-- The original prepared root tables are read at their genuine input pitch.
Each old host has only its attained depth. Blank old hosts may use none. -/
structure Observed (m : Memory w) (depth : z.Population) (v : z.Original) : Prop where
  role : ∀q l B,guard q l=some B→Source (.lookup B .row)
    (fun h g=>if depth h g=some l then v q l h g else 0) z.sourceLanes m
  missing : ∀q l,guard q l=none→∀h g,depth h g=some l→v q l h g=0

include r in
theorem rootSource (m : Memory w) (depth : z.Population) (v : z.Original) (seen : z.Observed guard m depth v)
    (q : Fin z.roots) (n : Fin z.nodes) :
    Source (z.rootWord base guard (finProdFinEquiv (q,n))) (fun h g=>(depth h g).elim 0 (fun i=>z.digit n (v q i h g)))
      z.sourceLanes (z.mounted base m):=by
  have top:=(z.lift_le base).trans_lt r.roof
  obtain ⟨_,printed,frame,_⟩:=DescentPackedZip.Book.mount z.digitPage d z.sourceLanes base m
    (fun _=>by simp [digitPage]) top
  simp only [rootWord,Equiv.symm_apply_apply]
  apply oneHot (fun l=>z.field base n (guard q l)) (z.mounted base m) depth (fun l h g=>z.digit n (v q l h g))
  intro l
  cases eq:guard q l with
  | none=>
    have dead (h g) : (if depth h g=some l then z.digit n (v q l h g) else 0)=0:=by
      split <;>rename_i proof
      · rw [seen.missing q l eq h g proof,z.digit_zero]
      · rfl
    simpa only [field,eq,Option.elim_none,dead] using
      (DescentPrimitiveBirth.zero (H:=(P).oldHosts) (G:=(P).groups*(P).blocks)
        (a:=z.rootBits) (M:=z.sourceLanes) (z.mounted base m))
  | some B=>
    have old:=r.old q l B eq
    have stored:=seen.role q l B eq
    have room:=Book.geometry z.digitPage d z.sourceLanes base n (out:=head) le_rfl top (by simp [digitPage])
    let tab:=Book.tables z.digitPage d z.sourceLanes base n
    have fit : DescentPackedZip.Fits tab (.lookup B .row) (.lit 0) d 0 z.sourceLanes head w:=by
      exact ⟨⟨⟨old.1,old.2.1,old.2.2.trans (Nat.le_add_right ..)⟩,trivial⟩,trivial,room.1,room.2,rfl,rfl⟩
    have src : Source (.lookup B .row) (fun h g=>if depth h g=some l then v q l h g else 0)
        z.sourceLanes (z.mounted base m):=fun j=>
      (ProtocolRAM.eval_below (out:=base) (.lookup B .row) _ m (z.mounted base m)
        ⟨old,trivial⟩ (fun i low=>frame i (.inl low))).trans (stored j)
    have rd:=read_data tab _ _ head fit (fun x _=>z.digit n x) (z.digit_zero n)
      (z.mounted base m) (printed n) _ _ src
      (DescentPrimitiveBirth.zero (H:=(P).oldHosts) (G:=(P).groups*(P).blocks)
        (a:=0) (M:=z.sourceLanes) (z.mounted base m))
    simpa only [field,eq,Option.elim_some,tab,apply_ite,z.digit_zero] using rd

include r in
theorem liftedSource (m : Memory w) (depth : z.Population) (v : z.Original) (seen : z.Observed guard m depth v)
    (positive : 0<z.sourceLanes) (name : Fin U→Fin (P).sparse) (cnt : m count.base=(U:Word w))
    (inverse : ∀i:Fin U,m (inv.base+i.val)=((name i).val:Word w)) (narrow : U<2^w) (hosts : (P).newHosts≤2^w)
    (saved : U≤ inv.size) (q : Fin z.roots) (n : Fin z.nodes) (x : Fin (P).blocks) :
    Source (.lookup (z.rootBank base n x q) .row)
      ((P).compact z.batch (fun _=>true) name (fun k h g=>
        (depth h g).elim 0 (fun l=>z.digit (finProdFinEquiv.symm k).2 (v (finProdFinEquiv.symm k).1 l h g)))
        (finProdFinEquiv (q,n)) x) (P).lanes (z.rootMem base guard count inv m):=by
  have top:=(z.lift_le base).trans_lt r.roof
  obtain ⟨_,_,frame,_⟩:=DescentPackedZip.Book.mount z.digitPage d z.sourceLanes base m
    (fun _=>by simp [digitPage]) top
  have bank {B : Bank} (p : B.Fits w base) : B.Fits w head:=⟨p.1,p.2.1,p.2.2.trans (Nat.le_add_right ..)⟩
  let digits (k : Fin (z.roots*z.nodes)) (h : Fin (P).oldHosts) (g : Fin ((P).groups*(P).blocks)) :=
    (depth h g).elim 0 (fun l=>z.digit (finProdFinEquiv.symm k).2 (v (finProdFinEquiv.symm k).1 l h g))
  have input (k : Fin (z.roots*z.nodes)) :
      Source (z.rootWord base guard k) (digits k) z.sourceLanes (z.mounted base m):=by
    obtain ⟨⟨root,node⟩,rfl⟩:=finProdFinEquiv.surjective k
    simpa only [digits,Equiv.symm_apply_apply] using z.rootSource base guard count inv r m depth v seen root node
  exact (P).read z.batch head (fun _=>true) (z.rootWord base guard) count inv (z.mounted base m) r.lanes positive r.blocks
    (z.rootFit base guard r.old top) (bank r.count) (bank r.inverse) r.roof name
    ((frame count.base (.inl ((Nat.lt_add_of_pos_right r.count.1).trans_le r.count.2.2))).trans cnt)
    (fun i=>(frame _ (.inl ((Nat.add_lt_add_left (i.isLt.trans_le saved) _).trans_le r.inverse.2.2))).trans (inverse i))
    narrow hosts saved digits input (finProdFinEquiv (q,n)) x
end Layout
end
end Hierarchy.DescentPrimitiveBirth

end OAI
