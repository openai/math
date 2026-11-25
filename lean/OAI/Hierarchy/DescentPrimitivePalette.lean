import OAI.Hierarchy.DescentOriginalPaletteEncoding
import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentChosenRotorMenu
import OAI.Hierarchy.DescentEpochTagKeys

namespace OAI
/-! # The single coefficient dictionary of a branch of the paid descent -/
namespace Hierarchy.DescentPrimitivePalette
open DescentCompiler DescentSixParty DescentKernelHistory DescentEpochTagKeys DescentRotor DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {s Z p : ℕ} (G : PoweredGadget F) (op : RotorSpec)

def promote {z : ℕ} (h : z≤Z) (x : GadgetTag G z) : GadgetTag G Z :=
  ⟨x.1.castLE (Nat.succ_le_succ h),x.2⟩

theorem promote_read {z : ℕ} (h : z≤Z) (x : GadgetTag G z) :
    gadgetScalar G (promote G h x)=gadgetScalar G x := rfl

variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def Encoding.transport {U : Type} {read : U→List (List Bool)→F} {W' : MarkedWorld F d P bits}
    {B : BitDescription W} (e : W=W') (cap : Encoding U read B) :
    Encoding U read (cast (congrArg BitDescription e) B) := by
  subst W';exact cap

def Encoding.follow {U : Type} {read : U→List (List Bool)→F} {W : MarkedWorld F d P bits}
    {B : BitDescription W} (cap : Encoding U read B) (n : Normalize W) :
    Encoding U read (BitDescription.follow n B) := by
  revert B
  induction n with
  | done W =>
    intro B cap
    exact cap
  | named W site edge next ih =>
    intro B cap
    exact @ih (B.renamed site edge) ⟨cap.code,cap.correct⟩
  | merge W V key flag k g next ih =>
    intro B cap
    exact @ih (B.coalesced (V:=V) key flag k g) ⟨cap.code,cap.correct⟩
  | split W q m fit next ih =>
    intro B cap
    exact @ih (B.pieces m q fit) ⟨cap.code,cap.correct⟩

def Encoding.scanned {q ε : ℝ} (menu : Runnable F op) {B : BitDescription W}
    (cap : Encoding (Label G s Z op) (dictionary G op menu p) B)
    (T : StageInput W G q ε) (he : 0≤ε) (c : (T.result he).Choice) (limit : T.z≤Z) :
    Encoding (Label G s Z op) (dictionary G op menu p) (BitDescription.scanned he T B c) := by
  let rows:=BitDescription.scannedRows he T
  let selected:=B.selected G rows.pick (fun _=>T.z) (fun _=>T.unitPos) rows.fit (fun _=>le_refl T.z)
    rows.pack (rows.profile c)
  have actual : Encoding (Label G s Z op) (dictionary G op menu p) selected := by
    refine ⟨Sum.elim cap.code (fun tag=>Sum.inr (Sum.inl (promote G limit tag))),?_⟩
    intro t
    cases t with
    | inl a=>exact cap.correct a
    | inr a=>rfl
  exact Encoding.transport (rows.state c).symm actual

section Reset
variable {G}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail : ℕ}
    {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl)

def actualSpec : RotorSpec := ⟨b.reset.n,b.reset.graph.arcs,C,b.reset.width,D,h,f,g⟩

theorem actual_eq : actualSpec b=RotorSpec.ofRates ctl := by
  unfold actualSpec RotorSpec.ofRates
  have identify {n₁ n₂ h C w₁ w₂ : ℕ} (back : NonlinearExpanders.Graph n₁ h) (front : NonlinearExpanders.Graph n₂ h)
      (dim : n₁=n₂) (same : HEq back front) (width : w₁=w₂) :
      (⟨n₁,back.arcs,C,w₁,D,h,f,g⟩ : RotorSpec)=⟨n₂,front.arcs,C,w₂,D,h,f,g⟩ := by
    subst n₂
    rw [eq_of_heq same,width]
  exact identify b.reset.graph ctl.board b.dimension b.graph b.width

def resetTag (same : actualSpec b=op) : CanonicalTag (2^b.reset.n)→CanonicalTag (2^op.n) :=
  cast (congrArg (fun o : RotorSpec=>CanonicalTag (2^o.n)) same)

theorem gate_eq (menu : Runnable F op) (same : actualSpec b=op) (t : CanonicalTag (2^b.reset.n)) :
    gate op menu p (resetTag op b same t)=gate (actualSpec b) (Chronology.resetMenu b) p t := by
  subst op;rfl

end Reset

end
end Hierarchy.DescentPrimitivePalette

end OAI
