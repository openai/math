import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.DescentTerminalSpanMarkers

namespace OAI
/-! # Cumulative site ordinal and local offset on each actual paid row -/
namespace Hierarchy.DescentTerminalSpanBook
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {w n S W q : ℕ}
structure Cursors where
  marker : Bank
  number : Bank
  first : Bank
  last : Bank
  active : Bank
  owner : Bank
  localRow : Bank

namespace Cursors
def raw (L : Cursors) : Expr := .lookup L.number .row
def site (L : Cursors) : Expr := .op .sub L.raw (.lit 1)
def localOffset (L : Cursors) : Expr := .op .sub .row (.lookup L.first L.site)
def covered (L : Cursors) : Expr := .branch .eq L.raw (.lit 0) (.lit 0)
  (.branch .lt .row (.lookup L.first L.site) (.lit 0) (.branch .lt (.lookup L.last L.site) .row (.lit 0) (.lit 1)))
def program (L : Cursors) (w n : ℕ) := (((DescentTerminalHeaderPrefixRAM.program w L.number.base n .add (.lookup L.marker .row)).seq
  (scan w L.active.base n L.covered)).seq (scan w L.owner.base n L.site)).seq (scan w L.localRow.base n L.localOffset)
def state (L : Cursors) (n : ℕ) (m : Memory w) :=
  DescentTerminalHeaderPrefixRAM.result L.number.base n .add (.lookup L.marker .row) m
def activated (L : Cursors) (n : ℕ) (m : Memory w) := image L.active.base n L.covered (L.state n m)
def located (L : Cursors) (n : ℕ) (m : Memory w) := image L.owner.base n L.site (L.activated n m)
def final (L : Cursors) (n : ℕ) (m : Memory w) := image L.localRow.base n L.localOffset (L.located n m)
def cost (L : Cursors) (n : ℕ) := (4+n*(2*DescentTerminalHeaderPrefixRAM.work .add (.lookup L.marker .row)+4))+
  (4+n*(2*L.covered.work+4))+(4+n*(2*L.site.work+4))+(4+n*(2*L.localOffset.work+4))
structure Fits (L : Cursors) (w n : ℕ) : Prop where
  mark : L.marker.Fits w L.number.base
  first : L.first.Fits w L.number.base
  last : L.last.Fits w L.number.base
  number : L.number.Fits w L.active.base
  active : L.active.Fits w L.owner.base
  owner : L.owner.Fits w L.localRow.base
  ranges : n≤L.number.size ∧ n≤L.active.size ∧ n≤L.owner.size
  endAt : L.localRow.base+n<2^w

private theorem four_runs (A B C D : Procedure w) {s₀ s₁ s₂ s₃ s₄ : Memory w} {a b c d : ℕ}
    (ra : A.Exec s₀ s₁ a) (rb : B.Exec s₁ s₂ b) (rc : C.Exec s₂ s₃ c) (rd : D.Exec s₃ s₄ d)
    (ca : CheapCode A) (cb : CheapCode B) (cc : CheapCode C) (cd : CheapCode D) :
    (((A.seq B).seq C).seq D).Exec s₀ s₄ (a+b+c+d) ∧ CheapCode (((A.seq B).seq C).seq D) :=
  by
    have ab : (A.seq B).Exec s₀ s₂ (a+b) :=
      @Procedure.Exec.then w A B s₀ s₁ s₂ a b (@ra) (@rb)
    have abc : ((A.seq B).seq C).Exec s₀ s₃ (a+b+c) :=
      @Procedure.Exec.then w (A.seq B) C s₀ s₂ s₃ (a+b) c (@ab) (@rc)
    exact ⟨@Procedure.Exec.then w ((A.seq B).seq C) D s₀ s₃ s₄ (a+b+c) d (@abc) (@rd),
      cheap_seq (cheap_seq (cheap_seq ca cb) cc) cd⟩

theorem run (L : Cursors) (n : ℕ) (m : Memory w) (f : L.Fits w n) :
    (L.program w n).Exec m (L.final n m) (L.cost n) ∧ CheapCode (L.program w n) := by
  have c:=f.number.2.2;have a:=f.active.2.2;have o:=f.owner.2.2;have ranges:=f.ranges;have hi:=f.endAt
  have k := @DescentTerminalHeaderPrefixRAM.exec_any w L.number.base n .add (.lookup L.marker .row) m trivial ⟨f.mark,trivial⟩ (by omega)
  have old : L.last.Fits w L.active.base:=DescentTerminalChipRuntime.bankMono f.last (by omega)
  have earlyFirst:=DescentTerminalChipRuntime.bankMono f.first (show L.number.base≤L.active.base by omega)
  have numberFit := f.number
  have x := @scan_exec w L.active.base n L.covered (L.state n m) (by
    simp only [covered,raw,site,Expr.Fits];tauto) (by omega)
  have sn:=DescentTerminalChipRuntime.bankMono f.number (show L.active.base≤L.owner.base by omega)
  have so := @scan_exec w L.owner.base n L.site (L.activated n m) ⟨⟨sn,trivial⟩,trivial⟩ (by omega)
  have sd:=DescentTerminalChipRuntime.bankMono f.number (show L.active.base≤L.localRow.base by omega)
  have ff:=DescentTerminalChipRuntime.bankMono f.first (show L.number.base≤L.localRow.base by omega)
  have l := @scan_exec w L.localRow.base n L.localOffset (L.located n m) ⟨trivial,ff,⟨sd,trivial⟩,trivial⟩ f.endAt
  exact four_runs
    (DescentTerminalHeaderPrefixRAM.program w L.number.base n .add (.lookup L.marker .row))
    (scan w L.active.base n L.covered) (scan w L.owner.base n L.site)
    (scan w L.localRow.base n L.localOffset) (@k) (@x) (@so) (@l)
    (@DescentTerminalHeaderPrefixRAM.cheap w L.number.base n .add (.lookup L.marker .row))
    (@scan_cheap w L.active.base n L.covered) (@scan_cheap w L.owner.base n L.site)
    (@scan_cheap w L.localRow.base n L.localOffset)

theorem printed_count (L : Cursors) (m : Memory w) (_f : L.Fits w n) (sites : Fin S→Site)
    (markers : ∀i:Fin n,L.marker.read m (i.val:Word w)=((mark (W:=W) (q:=q) sites i.val):Word w)) (i : Fin n) :
    L.state n m (L.number.base+i.val)=((count (W:=W) (q:=q) sites (i.val+1)):Word w) := by
  let rowExpr : Expr := .lookup L.marker .row
  have seen (t : ℕ) (ht : t≤n) :
      DescentTerminalHeaderPrefixRAM.stateOn .add rowExpr m t =
        (count (W:=W) (q:=q) sites t : Word w) := by
    induction t with
    | zero => simp [DescentTerminalHeaderPrefixRAM.stateOn,count,prior]
    | succ j ih =>
      let p : Fin n := ⟨j,ht⟩
      change DescentTerminalHeaderPrefixRAM.stateOn .add rowExpr m j
          + L.marker.read m (p.val:Word w) = _
      rw [ih (by omega),markers p,step (W:=W) (q:=q) sites j,Nat.cast_add]
  unfold state DescentTerminalHeaderPrefixRAM.result
  rw [DescentTerminalHeaderPrefixRAM.at_row]
  exact seen (i.val+1) i.isLt

end Cursors
end
end Hierarchy.DescentTerminalSpanBook

end OAI
