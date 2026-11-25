import OAI.Hierarchy.TaggedWireCommodityGraphs
import OAI.Hierarchy.TaggedWireSettlement
import OAI.Hierarchy.TaggedWideSettledRows

namespace OAI
/-! # Terminal tensors on the original charged core-board walks -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe WireTelescope ProtocolRAM ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators

variable {S : PurchaseSampler} {h d k K : ℕ}

namespace Mount
variable {π : Equiv.Perm (Fin (2^h))} {place : Site h d k → Fin K} {edges : ℕ}
    (B : Mount (S:=S) π place edges)

theorem ordinary_walk (i : Commodity (Fin (2^h)) (Stages h d) k) :
    Traverses B.actual ((commodityGraph π place).tail i) (B.ordinary i) ((commodityGraph π place).head i) := by
  let : Nonempty (Fin K) := ⟨(commodityGraph π place).tail i⟩
  exact mapped_walk _ B.actual B.row B.tail B.head (commodity_walk (S:=S) π place 0 i).1

theorem center_walk (c : Columns h d × Fin k) :
    Traverses B.actual ((catalystGraph place).tail c) (B.centers c) ((catalystGraph place).head c) := by
  let : Nonempty (Fin K) := ⟨(catalystGraph place).tail c⟩
  exact mapped_walk _ B.actual B.row B.tail B.head (catalyst_walk (S:=S) π place 0 c).1

theorem ordinary_price (M : ℝ) (len : Fin edges→ℝ)
    (code : ∀e,len (B.row e)=coreLength (freeLength M) e) (i : Commodity (Fin (2^h)) (Stages h d) k) :
    ((B.ordinary i).map len).sum = commodityLength M i := by
  simp only [ordinary,List.map_map,Function.comp_def,code]
  exact (commodity_walk (S:=S) π place M i).2

theorem center_price (M : ℝ) (len : Fin edges→ℝ)
    (code : ∀e,len (B.row e)=coreLength (freeLength M) e) (c : Columns h d × Fin k) :
    ((B.centers c).map len).sum=2*M := by
  simp only [centers,List.map_map,Function.comp_def,code]
  exact (catalyst_walk (S:=S) π place M c).2

end Mount

/-- The native reporter receives the original board's links by ordinal.
Its occurrence list is the board's paid-walk list under that same numbering. -/
theorem core_report {F : Type*} [Field F] [Nonempty (Fin K)] {W edges r : ℕ}
    (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) (B : Mount (S:=S) π place edges)
    (b : Banks) (src : ℕ) (m : Memory W)
    (enum : Fin r ≃ RouteOccurrence B.ordinary B.centers)
    (ci : Commodity (Fin (2^h)) (Stages h d) k → ℕ) (cj : Columns h d × Fin k → ℕ) (geo : Fin 7 → Expr)
    (fit : edges≤b.width.size) (bound : edges≤2^W) (space : b.width.base+edges≤ src)
    (room : ∀ e : Fin edges,(m (b.width.base+e.val)).val +
      (routeLoad B.ordinary (fun i=>actual b.stock m (ci i)) e+
       routeLoad B.centers
         (fun c=>actual b.reserved m (cj c)-actual b.used m (cj c)) e)<2^W) :
    let A := B.actual
    (raw F (A.chordWidths (fun e=>(m (b.width.base+e.val)).val) +
      (commodityGraph π place).chordWidths (fun i=>actual b.stock m (ci i)) +
      (catalystGraph place).chordWidths (fun c=>actual b.reserved m (cj c)-actual b.used m (cj c)))).Restricts
      (raw F (A.chordWidths (fun e=>(reportedRows [] (fields b geo) (output b src m enum ci cj) e).width))) := by
  apply reported_restricts b src m enum ci cj geo fit bound space room
    B.actual (commodityGraph π place) (catalystGraph place)
  · intro i
    exact B.ordinary_walk i
  · intro c
    exact B.center_walk c

/-- The same ordinal walks charge the actual rendered widths to the terminal
ledger, with physical lengths N, M+1, and 2M. -/
theorem core_report_budget {W edges r : ℕ}
    (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) (B : Mount (S:=S) π place edges)
    (b : Banks) (src : ℕ) (m : Memory W)
    (enum : Fin r ≃ RouteOccurrence B.ordinary B.centers)
    (ci : Commodity (Fin (2^h)) (Stages h d) k → ℕ) (cj : Columns h d × Fin k → ℕ) (geo : Fin 7 → Expr)
    (fit : edges≤b.width.size) (bound : edges≤2^W) (space : b.width.base+edges≤ src)
    (room : ∀ e : Fin edges,(m (b.width.base+e.val)).val +
      (routeLoad B.ordinary (fun i=>actual b.stock m (ci i)) e+
       routeLoad B.centers
         (fun c=>actual b.reserved m (cj c)-actual b.used m (cj c)) e)<2^W) (p q Q Λ : ℝ) (ticks w M : ℕ) (nonempty : 0<ticks) (hw : 0<w)
    (t len : Fin edges→ℝ) (code : ∀e,len (B.row e)=coreLength (freeLength M) e) (cash : ℝ)
    (within : ∀ j,actual b.used m (cj j)≤actual b.reserved m (cj j))
    (prepaid : (∑ e : Fin edges,(len e*(((m (b.width.base+e.val)).val:ℝ)/w)+
      Λ*capacity p q Q (t e) (len e)))≤cash+2*M*(∑ j,(actual b.used m (cj j):ℝ))/w)
    (paid : cash+pairing (fun i=>(actual b.stock m (ci i):ℝ)/w) (commodityLength M)≤6*ticks) :
    TermBudget p q Q Λ ticks w M (∑ j,actual b.reserved m (cj j)) t len
      (fun e : Fin edges=>((reportedRows [] (fields b geo) (output b src m enum ci cj) e).width:ℝ)/w) :=
  report_termBudget b src m enum ci cj geo fit bound space room p q Q Λ ticks w M nonempty hw
    t len cash (commodityLength M) within (fun i=>(B.ordinary_price M len code i).le)
    (fun j=>(B.center_price M len code j).le) prepaid paid

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
