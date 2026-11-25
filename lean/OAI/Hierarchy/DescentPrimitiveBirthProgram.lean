import OAI.Hierarchy.DescentPrimitiveBirthClassifier
import OAI.Hierarchy.DescentPrimitiveTapSpan

namespace OAI
/-! # The chronologically mounted opcode tables and the two actual checkpoint inputs -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentPrimitiveBirth.Layout) {w U : ℕ}
variable (base : ℕ) (guard : z.Guards) (cnt inv : Bank)
set_option quotPrecheck false
local notation "P" => z.placement
local notation "M" => (P).lanes
def program (w : ℕ) :=(z.rootCode base guard cnt inv w).seq (z.mountOrigin base w)
def clock :=z.rootTime base guard cnt inv+(4+10*(z.gates*(2*2^(z.aperture*M))))
def image (m : Memory w) :=z.originMem base (z.rootMem base guard cnt inv m)
def bornAt (n : Fin z.nodes) (x : Fin (P).blocks) (cls paid : Expr) (spans : Fin z.arguments→Expr) :=
  z.fresh base n cls paid spans (fun q=>.lookup (z.rootBank base n x q) .row)

theorem any (m : Memory w) (r : z.RootRoom base guard cnt inv w) (room : z.endAddress base<2^w) :
    (z.program base guard cnt inv w).Exec m (z.image base guard cnt inv m) (z.clock base guard cnt inv) ∧
    CheapCode (z.program base guard cnt inv w) ∧ ∀i,i<base ∨ z.endAddress base≤ i→z.image base guard cnt inv m i=m i:=by
  have one:=z.rootAny base guard cnt inv r m
  have two:=z.originsAny base (z.rootMem base guard cnt inv m) room
  have start : base≤z.lifted base:=(Nat.le_add_right ..).trans (z.lift_le base)
  exact ⟨(by
    intro labels regs slots machine
    exact Procedure.Exec.then one.1 two.1 machine),cheap_seq one.2.1 two.2.1,fun i h=>(two.2.2.1 i (h.imp_left (·.trans_le start))).trans
    (one.2.2 i (h.imp_right ((Nat.le_add_right ..).trans ·)))⟩

theorem operandsFit (n : Fin z.nodes) (x : Fin (P).blocks) (cls paid : Expr) (spans : Fin z.arguments→Expr)
    (fc : cls.Fits w base) (fp : paid.Fits w base) (fs : ∀j,(spans j).Fits w base) (space : z.endAddress base<2^w) :
    (z.bornAt base n x cls paid spans).Fits w (z.endAddress base) ∧ (z.relay base n cls paid).Fits w (z.endAddress base):=by
  have old : base≤z.lifted base:=(Nat.le_add_right ..).trans (z.lift_le base)
  exact z.originFits base n cls paid spans _ space (ProtocolRAMGeneratedWrite.fits_mono _ old fc)
    (ProtocolRAMGeneratedWrite.fits_mono _ old fp) (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ old (fs j))
    (fun q=>⟨((P).validBank z.batch (z.liftBase base) ((Nat.le_add_right ..).trans_lt space) (finProdFinEquiv (q,n)) x).1,trivial⟩)

def rootActual (depth : z.Population) (v : z.Original) (name : Fin U→Fin (P).sparse)
    (n : Fin z.nodes) (x : Fin (P).blocks) (q : Fin z.roots) :=
  (P).compact z.batch (fun _=>true) name (fun (k : Fin (z.roots*z.nodes)) h g=>
    let pair : Fin z.roots×Fin z.nodes:=finProdFinEquiv.symm k
    (depth h g).elim 0 (fun l=>z.digit pair.2 (v pair.1 l h g))) (finProdFinEquiv (q,n)) x

theorem issued (m : Memory w) (r : z.RootRoom base guard cnt inv w) (space : z.endAddress base<2^w)
    (depth : z.Population) (v : z.Original) (seen : z.Observed guard m depth v) (pos : 0<z.sourceLanes)
    (name : Fin U→Fin (P).sparse) (count : m cnt.base=(U:Word w))
    (inverse : ∀i:Fin U,m (inv.base+i.val)=((name i).val:Word w)) (narrow : U<2^w) (hosts : (P).newHosts≤2^w)
    (saved : U≤ inv.size) (n : Fin z.nodes) (x : Fin (P).blocks) (cls paid : Expr) (spans : Fin z.arguments→Expr)
    (C : Fin (P).newHosts→Fin (P).groups→Cell z.classBits) (P₀ : Fin (P).newHosts→Fin (P).groups→Cell z.paidBits)
    (S : Fin z.arguments→Fin (P).newHosts→Fin (P).groups→Cell z.spanBits)
    (fc : cls.Fits w base) (fp : paid.Fits w base) (fs : ∀j,(spans j).Fits w base)
    (rc : Source cls C M m) (rp : Source paid P₀ M m) (rs : ∀j,Source (spans j) (S j) M m) :
    Source (z.bornAt base n x cls paid spans)
      (fun h g=>z.raw n (C h g) (P₀ h g) (fun j=>S j h g) (fun q=>z.rootActual depth v name n x q h g))
      M (z.image base guard cnt inv m) ∧
    Source (z.relay base n cls paid) (fun h g=>z.tagRelay (z.admitted n (C h g) (P₀ h g))) M (z.image base guard cnt inv m):=by
  have old : base≤z.lifted base:=(Nat.le_add_right ..).trans (z.lift_le base)
  have keep:= (z.rootAny base guard cnt inv r m).2.2
  have carry {a : ℕ} (e : Expr) {values : Fin (P).newHosts→Fin (P).groups→Cell a}
      (fit:e.Fits w base) (read:Source e values M m) : Source e values M (z.rootMem base guard cnt inv m):=
    fun i=>(eval_below e _ _ _ fit (fun j h=>keep j (.inl h))).trans (read i)
  apply z.originSource base _ space n cls paid spans _ C P₀ S _
    (ProtocolRAMGeneratedWrite.fits_mono _ old fc) (ProtocolRAMGeneratedWrite.fits_mono _ old fp)
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ old (fs j)) _ (carry cls fc rc) (carry paid fp rp)
    (fun j=>carry _ (fs j) (rs j)) _
  · intro q
    exact ⟨((P).validBank z.batch (z.liftBase base) r.roof (finProdFinEquiv (q,n)) x).1,trivial⟩
  · intro q
    exact z.liftedSource base guard cnt inv r m depth v seen pos name count inverse narrow hosts saved q n x

theorem another_span {p : ℕ} {U A : Type} {w : A→ℕ} {rec : DescentKernelHistory.BitRecipe U A w}
    (shape : DescentBundleHistory.Shape p rec) (u : rec.Node) (hp : 0<p) (S : Fin z.arguments→Cell z.spanBits)
    (bound : (shape.recipe hp).arity u≤z.arguments)
    (read : ∀j,(S j).val=DescentResetMetadataInputs.argumentSpan shape u j.val) :
    z.extra S≠0 ↔ DescentResetMetadataInputs.another (DescentResetMetadataInputs.argumentSpan shape u) :=by
  have lookup:=DescentResetMetadataInputs.captured shape u S hp bound read
  rw [←lookup]
  unfold DescentResetMetadataInputs.another DescentResetMetadataInputs.measured extra spanId
  by_cases pos:0<z.arguments
  · simp only [pos,dite_eq_left]
    split
    next h=>
      simp only [Option.elim_some,dite_eq_left h.2]
      split <;> rename_i atSlot
      · simp [atSlot]
      · simp [Fin.pos_iff_ne_zero.mpr atSlot]
    next h=>
      simp only [Option.elim_none,ne_eq,not_true_eq_false,false_iff,not_lt]
      by_cases lo:(S ⟨0,pos⟩).val<z.arguments
      · have empty:(S ⟨0,pos⟩).val=0:=by omega
        simp [empty,pos]
      · simp [lo]
  · simp [pos]

end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
