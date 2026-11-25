import OAI.Hierarchy.DescentFundedCensus
import OAI.Hierarchy.DescentPreparedBankPay
import OAI.Hierarchy.DescentPaidResetWindow

namespace OAI
/-! # The reset atlas uses the genuine two trunk tallies and the two fixed bank menus -/
namespace Hierarchy.DescentFundedCensus
open DescentSIMDLookup DescentResetHostSize DescentContacts DescentCommonHost DescentHostDirectory
open DescentPaidResidentCount.Reset DescentPaidResidentCount.Reset.BankIssue
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- The saved positive/empty bit is available even for a site with no charged records. -/
def whenPresent {b a : ℕ} (f : Cell a→Cell b) : Operation b :=
  ⟨1,a,fun present x => if present=0 then 0 else f x,by simp⟩

def trunk (field bits L root : ℕ) : Operation bits :=
  ⟨field*L,bits*L,tally field bits L root,tally_zero field bits L root⟩

def inactive (bits : ℕ) : Operation bits := ⟨0,0,fun _ _=>0,rfl⟩

variable {n h r : ℕ} (board : NonlinearExpanders.Graph n h)

/-- All rotor sites of a given kind at this date have the recorded reset's layer count. -/
def good (C packet batch oldCap f bits : ℕ) (role : (DescentCommonPalette.rotor board).Site) : Operation bits :=
  whenPresent (a:=0) (fun _=>(Rotor.funded board C packet batch (DescentRecordedRotorLayers.layers n packet f oldCap) role:ℕ))

/-- The original middle row of the matching exceptional-root gather contains its signed
incident fields and the true reservation counts. This is the same packed packet used to
print the cable headers of that root. -/
def fallback {Ht : ℕ} (C packet batch bits degree ports field : ℕ) (side : Bool)
    (key : Code r × Option (Fin (2^n))) (dep : Fin (Ht+1)) (node : DescentContactTree.Node dep.val) : Operation bits :=
  whenPresent (a:=field*DescentFallbackPeriod.inputCount degree (2^r) ports n r) (fun x=>
    ((amount board C packet batch (.tree dep node)
      (treeInput (ht:=Ht) (levels:=0) (degree:=degree) (L:=2^r) (cap:=ports) side key x):ℕ):Cell bits))

structure Ports (r n : ℕ) where
  old : Expr
  relay : Expr
  stencil : Expr
  bank : Bool → Code r × Option (Fin (2^n)) → Expr

def compile {Ht : ℕ} (C packet batch bits oldCap f degree ports field stencilBits : ℕ)
    (io : Ports r n) (present : Expr) :
    Node Unit (Unit×Endpoint (2^n)) (DescentCommonPalette.rotor board).Site → Job bits
  | .good _ _ role => ⟨good board C packet batch oldCap f bits role,present,.lit 0,present⟩
  | .trunk side (_,label) =>
    ⟨trunk stencilBits bits (2^r) (DescentFallbackShapeTable.cell r label),io.stencil,if side then io.relay else io.old,present⟩
  | .fall side (_,label) path =>
    if legal : label.1.1≤r ∧ label.1.2<2^label.1.1 ∧ path.length≤Ht then
      let key : Code r × Option (Fin (2^n)) := (⟨label.1,mem_codes legal.1 legal.2.1⟩,label.2)
      ⟨fallback board C packet batch bits degree ports field side key ⟨path.length,Nat.lt_succ_of_le legal.2.2⟩ path.get,
        present,io.bank side key,present⟩
    else ⟨inactive bits,.lit 0,.lit 0,present⟩

@[simp] theorem good_read (C packet batch bits oldCap f : ℕ) (role) (x : Cell 0) :
    (good board C packet batch oldCap f bits role).apply 1 x=
      ((Rotor.funded board C packet batch (DescentRecordedRotorLayers.layers n packet f oldCap) role:ℕ):Cell bits) := by
  simp only [good,whenPresent]
  split
  · next h => exact Nat.noConfusion (congrArg Fin.val h)
  · rfl

@[simp] theorem fallback_read {Ht : ℕ} (C packet batch bits degree ports field : ℕ)
    (side : Bool) (key : Code r × Option (Fin (2^n))) (dep : Fin (Ht+1)) (node) (input) :
    (fallback board C packet batch bits degree ports field side key dep node).apply 1 input=
      ((amount board C packet batch (.tree dep node)
        (treeInput (ht:=Ht) (levels:=0) (degree:=degree) (L:=2^r) (cap:=ports) side key input):ℕ):Cell bits) := by
  simp only [fallback,whenPresent]
  split
  · next h => exact Nat.noConfusion (congrArg Fin.val h)
  · rfl

end
end Hierarchy.DescentFundedCensus

end OAI
