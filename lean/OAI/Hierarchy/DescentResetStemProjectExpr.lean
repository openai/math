import OAI.Hierarchy.DescentResetStemProjectExprGather
import OAI.Hierarchy.DescentResetStemProject

namespace OAI
/-! # Projecting the original signed one-hop and receiver expressions directly -/
namespace Hierarchy.DescentResetStemProjectExpr
open DescentSIMDLookup DescentPackedZip DescentResetStemProject ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w N : ℕ} (base H G X a A M : ℕ) (src : Fin N→Expr)
local notation "finish" => endAddress base N H G X a A M
local notation "cut" => overlapBase base N H G X A
local notation "scans" => passes src H (G*X) A base

def program (w : ℕ) := (ProtocolRAM.program w scans).seq (postProgram (N:=N) base H G X a A M w)
def ticks := clock scans+postTicks (N:=N) base H G X a A M
def image (m : Memory w) := postImage (N:=N) base H G X a A M (result scans m)

private theorem locations : base≤cut ∧ base+N*(H*chunks (G*X) A)≤cut ∧ cut≤finish := by
  obtain ⟨r₁,r₂,r₃,r₄,r₅⟩:=regions (N:=N) base H G X a A M
  exact ⟨(Nat.le_add_right ..).trans r₁,r₁,r₂.trans ((Nat.le_add_right ..).trans
    (r₃.trans (r₄.trans ((Nat.le_add_right ..).trans r₅))))⟩

/-- The same executable and clock apply to corrupted, missing, or untyped row contents. -/
theorem any (m : Memory w) (hm : 0<M) (hx : 0<X) (fits : ∀q,(src q).Fits w base) (room : finish<2^w) :
    let final:=image base H G X a A M src m
    (program base H G X a A M src w).Exec m final (ticks base H G X a A M src) ∧
    (∀u,u<base ∨ finish≤u→final u=m u) ∧ CheapCode (program base H G X a A M src w) := by
  obtain ⟨before,upto,after⟩:=locations (N:=N) base H G X a A M
  let es:=List.ofFn src
  have sz : es.length=N:=List.length_ofFn
  have ready : ∀e∈es,e.Fits w base:=by intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact fits j
  have limit:=((upto.trans after).trans_lt room)
  have cp : (ProtocolRAM.program w scans).Exec m (result scans m) (clock scans) :=
    ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es (le_refl base) ready
      (by simpa only [sz] using limit))
  obtain ⟨run,frame,cheap⟩:=post_any (N:=N) base H G X a A M (result scans m) hm hx room
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then cp run machine pc reg pub exit rom advice cfg raw enter same,?_,@cheap_seq w _ _ (@program_cheap w scans) (@cheap)⟩
  rintro u (h|h)
  · exact (frame _ (.inl (h.trans_le before))).trans (ProbeStage.Native.columns_frame es m (.inl h))
  · exact (frame _ (.inr h)).trans (ProbeStage.Native.columns_frame es m
      (.inr (by simpa only [sz] using (upto.trans after).trans h)))

theorem run (m : Memory w) (Y : Fin N→Fin H→Fin (G*X)→Cell a) (ha : 0<A) (hm : 0<M) (hx : 0<X)
    (fits : ∀q,(src q).Fits w base) (read : ∀q,Source (src q) (Y q) A m) (room : finish<2^w) :
    let final:=image base H G X a A M src m
    (program base H G X a A M src w).Exec m final (ticks base H G X a A M src) ∧
      (∀q x,Source (.lookup (bank base N H G X a A M q x) .row)
        (fun h g=>Y q h (finProdFinEquiv (g,x))) M final) ∧
      (∀q x,(bank base N H G X a A M q x).Fits w finish) ∧
      (∀u,u<base ∨ finish≤u→final u=m u) ∧ CheapCode (program base H G X a A M src w) := by
  obtain ⟨before,upto,after⟩:=locations (N:=N) base H G X a A M
  obtain ⟨_,rows,_⟩:=gather_run base src Y m fits read ((upto.trans after).trans_lt room)
  obtain ⟨_,stored,banks,_,_⟩:=post_run base H G X a A M (result scans m) Y ha hm hx rows room
  obtain ⟨clocked,frame,cheap⟩:=any base H G X a A M src m hm hx fits room
  exact ⟨clocked,stored,banks,frame,cheap⟩

theorem clock_bound (T : ℕ) (cost : ∀q,(src q).work≤T) :
    ticks base H G X a A M src≤(4+N*(4+H*chunks (G*X) A*(2*T+4)))+
      postTicks (N:=N) base H G X a A M :=
  Nat.add_le_add_right (gather_clock src H (G*X) A base T cost) _

end
end Hierarchy.DescentResetStemProjectExpr

end OAI
