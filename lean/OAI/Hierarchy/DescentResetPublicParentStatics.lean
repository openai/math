import OAI.Hierarchy.DescentResetPublicParentRaster
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The two shared public geometry words used by every reset parent raster -/
namespace Hierarchy.DescentResetPublicParentStatics
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w a : ℕ}

def geom (a Q : ℕ) (s : Fin 2) (h : Fin H) (g : Fin G) : Cell a :=
  if s.val=0 then h.val%Q else (decide (g.val=0)).toNat

def rowIndex (H G M : ℕ) : (Fin 2×Row H G M)≃Fin (2*(H*chunks G M)) :=
  ((Equiv.refl _).prodCongr (row H G M)).trans finProdFinEquiv

def literal (H G M a Q : ℕ) (j : ℕ) : ℕ :=
  if ok : j<2*(H*chunks G M) then
    let p:=(rowIndex H G M).symm ⟨j,ok⟩
    (data (geom a Q p.1) p.2).val
  else 0

def bank (base H G M : ℕ) (s : Fin 2) : Bank:=⟨base+s.val*(H*chunks G M),Nat.clog 2 (H*chunks G M+1)⟩

theorem installed (base Q : ℕ) (m : Memory w)
    (room : base+2*(H*chunks G M)<2^w) (ceiling : ℕ) (allocated : ∀s,(bank base H G M s).Fits w ceiling) :
    let N:=2*(H*chunks G M)
    let column:=literal H G M a Q
    let dst:=DescentStaticWordColumn.image base column m N
    (DescentStaticWordColumn.program w base column N).Exec m dst (4+10*N) ∧
    (∀s : Fin 2,Source (.lookup (bank base H G M s) .row) (geom (H:=H) (G:=G) a Q s) M dst) ∧
    (∀j,j<base ∨ base+N≤j→dst j=m j) ∧ DescentStaticWordColumn.names (DescentStaticWordColumn.program w base column N)=15*(N+1):=by
  intro N column dst
  refine ⟨DescentStaticWordColumn.mount base N column m room,?_,DescentStaticWordColumn.frame base N column m,DescentStaticWordColumn.names_mount ..⟩
  intro s
  apply source_column (bank base H G M s) ceiling (allocated s) dst _ (by exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
  intro p
  let j:=rowIndex H G M (s,p)
  have addr : (bank base H G M s).base+(row H G M p).val=base+j.val:=by
    simp [bank,j,rowIndex,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,Nat.add_assoc]
  rw [addr]
  dsimp only [dst]
  rw [DescentStaticWordColumn.read base N column m j.isLt]
  simp only [column,literal,dite_eq_left j.isLt]
  change ((data (geom a Q ((rowIndex H G M).symm j).1) ((rowIndex H G M).symm j).2).val:Word w)=_
  simp only [j,Equiv.symm_apply_apply]

def zeroExpr (base H G M x : ℕ) : Expr:=if x=0 then .lookup (bank base H G M 1) .row else .lit 0

theorem zero_source (base Q x : ℕ) (m : Memory w)
    (already : Source (.lookup (bank base H G M 1) .row) (geom (H:=H) (G:=G) a Q (1:Fin 2)) M m) :
    Source (zeroExpr base H G M x) (fun (_ : Fin H) (g : Fin G)=>((decide (g.val=0 ∧ x=0)).toNat:Cell a)) M m:=by
  by_cases hx : x=0
  · have same : geom (H:=H) (G:=G) a Q 1 =
        fun (_ : Fin H) (g : Fin G) => ((decide (g.val=0 ∧ x=0)).toNat:Cell a) := by
      funext h g
      simp [geom,hx]
    rw [←same,zeroExpr,ite_eq_left hx]
    exact already
  · intro p
    have z : encode a M (fun _=>0)=0 := by
      apply Fin.ext
      change (finFunctionFinEquiv (fun _ : Fin M=>(0:Cell a))).val=0
      simp
    simp [zeroExpr,hx,Expr.eval,DescentSIMDLookup.data,z]

end
end Hierarchy.DescentResetPublicParentStatics

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
theorem public_zero (u : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k) :
    zeroCoarse B u=decide (u.1.1.val=0 ∧ u.2.val=0):=by
  change decide ((finProdFinEquiv (u.1.1,u.2)).val=0)=_
  congr 1
  simp [finProdFinEquiv_apply_val,Nat.add_eq_zero_iff,And.comm]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
