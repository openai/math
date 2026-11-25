import OAI.Hierarchy.DescentResetActorClassShape
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Installed finite actor classifications in the role-checkpoint packing -/
namespace Hierarchy.DescentResetActorClass.Shape
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (c : Shape) (base : ℕ) {w : ℕ}
abbrev Classifier (bits : ℕ := 3) := Fin c.rawHosts→Cell bits
variable {bits : ℕ} (kind : c.Classifier bits)
def values (h : Fin c.rawHosts) (_ : Fin c.groups) :=kind h
def literal (i : ℕ) :=if h:i<c.cells then (data (c.values kind) ((row c.rawHosts c.groups c.lanes).symm ⟨i,h⟩)).val else 0
def page : Bank := ⟨base,Nat.clog 2 c.cells⟩
def sparseProgram (w : ℕ) :=DescentStaticWordColumn.program w base (c.literal kind) c.cells
def sparseImage (m : Memory w) :=DescentStaticWordColumn.image base (c.literal kind) m c.cells
def program (w : ℕ) := (c.sparseProgram base kind w).seq ((c.remap base).setup w)
def image (m : Memory w) := (c.remap base).mounted (c.sparseImage base kind m)
def ticks :=4+10*c.cells+(4+10*(c.remap base).size)
def expr (count inverse : Bank) : Expr := (c.remap base).load count inverse (.lookup (c.page base) .row)

theorem priced (w : ℕ) : DescentStaticWordColumn.names (c.program base kind w)=
    15*(c.cells+1)+15*((c.remap base).size+1):=by
  simp [program,sparseProgram,Layout.setup,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]

theorem guard : base≤c.next base ∧ c.next base≤c.endAddress base:=
  ⟨Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem any (m : Memory w) (space : c.endAddress base<2^w) :
    (c.program base kind w).Exec m (c.image base kind m) (c.ticks base) ∧ CheapCode (c.program base kind w) ∧
    ∀a,a<base ∨ c.endAddress base≤a→c.image base kind m a=m a:=by
  have raw : c.cells≤2^Nat.clog 2 c.cells:=Nat.le_pow_clog (by decide) _
  have ends : base+c.cells≤c.next base:=Nat.add_le_add_left raw _
  have cut := c.guard base
  have one : (c.sparseProgram base kind w).Exec m (c.sparseImage base kind m) (4+10*c.cells) :=
    @DescentStaticWordColumn.mount w base c.cells (c.literal kind) m (ends.trans_lt (cut.2.trans_lt space))
  have two:=(c.remap base).setup_run (c.sparseImage base kind m) space
  refine ⟨?_,cheap_seq (@DescentStaticWordColumn.cheap w base (c.literal kind) c.cells) two.2.1,?_⟩
  · intro labels regs pubs machine
    exact Procedure.Exec.then (@one) two.1 machine
  intro a ha
  have low : a<(c.remap base).first ∨ (c.remap base).endAddress≤a := ha.imp (fun h=>h.trans_le cut.1) id
  have rawAway : a<base ∨ base+c.cells≤a:=ha.imp id ((ends.trans cut.2).trans ·)
  exact (two.2.2.2 a low).trans (DescentStaticWordColumn.frame base c.cells (c.literal kind) m a rawAway)

theorem cheap (w : ℕ) : CheapCode (c.program base kind w):=
  cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)

def native (w : ℕ) : NativePhase w:=⟨c.program base kind w,c.ticks base,c.image base kind,c.cheap base kind w⟩

theorem page_fits (space : c.endAddress base<2^w) : (c.page base).Fits w (c.next base):=by
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((c.guard base).2.trans_lt space),le_rfl⟩

theorem original (m : Memory w) (space : c.endAddress base<2^w) :
    Source (.lookup (c.page base) .row) (c.values kind) c.lanes (c.sparseImage base kind m):=by
  apply source_column _ _ (c.page_fits base space) _ _ (Nat.le_pow_clog (by decide) _)
  intro p
  have r : (row c.rawHosts c.groups c.lanes p).val < c.cells :=
    (row c.rawHosts c.groups c.lanes p).isLt
  calc
    _=(c.literal kind (row c.rawHosts c.groups c.lanes p).val:Word w):=
      DescentStaticWordColumn.read base c.cells (c.literal kind) m r
    _= _:= by
      unfold literal
      rw [dite_eq_left r]
      change ((data (c.values kind) ((row c.rawHosts c.groups c.lanes).symm
        (row c.rawHosts c.groups c.lanes p))).val : Word w) = _
      rw [Equiv.symm_apply_apply]

theorem received {U : ℕ} (name : Fin U→Fin c.rawHosts) (cnt inv : Bank) (m : Memory w)
    (fit₁ : cnt.Fits w base) (fit₂ : inv.Fits w base) (count : m cnt.base=(U:Word w))
    (stored : ∀i : Fin U,m (inv.base+i.val)=((name i).val:Word w)) (size : U ≤ inv.size)
    (fits : U<2^w) (hostFits : c.hosts≤2^w) (space : c.endAddress base<2^w) :
    (c.expr base cnt inv).Fits w (c.endAddress base) ∧
    Source (c.expr base cnt inv) (dense (H:=c.hosts) name (c.values kind)) c.lanes (c.image base kind m):=by
  let L:=c.remap base
  let before:=c.sparseImage base kind m
  let out:=c.image base kind m
  have cuts:=c.guard base
  have safe:=L.book_fits cnt inv ⟨fit₁.1,fit₁.2.1,fit₁.2.2.trans cuts.1⟩ ⟨fit₂.1,fit₂.2.1,fit₂.2.2.trans cuts.1⟩ space
  have small (a) (h:a<base) : out a=m a:=(c.any base kind m space).2.2 a (.inl h)
  have frames (a) (h:a<L.first) : out a=before a:=(L.setup_run before space).2.2.2 a (.inl h)
  have held:=c.original base kind m space
  have young : Source (.lookup (c.page base) .row) (c.values kind) c.lanes out:=
    fun x=>(eval_below (out := L.first) (.lookup (c.page base) .row)
      ((row c.rawHosts c.groups c.lanes x).val : Word w) before out
      ⟨c.page_fits base space,trivial⟩ frames).trans (held x)
  have pg:=c.page_fits base space
  refine ⟨L.fits safe (.lookup (c.page base) .row) ⟨⟨pg.1,pg.2.1,pg.2.2.trans cuts.2⟩,trivial⟩,?_⟩
  have countOut : out cnt.base=(U:Word w) :=
    (small _ ((Nat.lt_add_of_pos_right fit₁.1).trans_le fit₁.2.2)).trans count
  have namesOut (i : Fin U) : out (inv.base+i.val)=((name i).val:Word w) :=
    (small _ ((Nat.add_lt_add_left (i.isLt.trans_le size) inv.base).trans_le fit₂.2.2)).trans (stored i)
  exact DescentResetDenseOperand.source L.first cnt inv (.lookup (c.page base) .row) out name
    (c.values kind) young L.endAddress (L.books before) safe countOut namesOut fits hostFits size

end
end Hierarchy.DescentResetActorClass.Shape

end OAI
