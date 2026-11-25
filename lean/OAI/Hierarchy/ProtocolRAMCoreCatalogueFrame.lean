import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Preserving the checked core catalogue across later native passes -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open scoped Classical Fin.CommRing
variable {w h W k R H attempts : ℕ} {S : PurchaseSampler}

structure Fits (c : CatalogueRows.CoreSource) (w out : ℕ) : Prop where
  group : c.group.Fits w out
  left : c.left.Fits w out
  right : c.right.Fits w out
  lengthCode : c.lengthCode.Fits w out
  menu : c.menu.Fits w out

theorem Fits.all {c : CatalogueRows.CoreSource} {limit : ℕ} (fit : Fits c w limit) :
    c.All (Expr.Fits w limit) := ⟨fit.group,fit.left,fit.right,fit.lengthCode,fit.menu⟩

/-- Last read addresses are public. The two socket banks may each extend to
the next power-of-two boundary, as required by the native lookup instruction. -/
theorem source_fits (base R bits siteBase superStart K G H k attempts out : ℕ)
    (room : out<2^w) (rows : base+headerWords R≤ out) (point : 2^bits≤ out)
    (directory : superStart+2*ProtocolRAMSupergroupDirectory.span K≤ out)
    (offsets : siteBase+(SiteROM.offsets siteBase G).size≤ out)
    (sites : siteBase+G+(SiteROM.sites siteBase G H).size≤ out) :
    Fits (source base R bits siteBase superStart K G H k attempts) w out := by
  have safe (b : Bank) (endAt : b.base+b.size≤ out) : b.Fits w out :=
    ⟨Nat.two_pow_pos _,by omega,endAt⟩
  have row (i : Fin 10) : (field base R i).Fits w out := by
    refine ⟨safe _ ?_,trivial⟩
    have bound := Nat.mul_le_mul_right (stride R) i.isLt
    rw [Nat.succ_mul] at bound
    change base+i.val*stride R+stride R≤ out
    change base+10*stride R≤ out at rows
    omega
  have ptr (i : Fin 10) : (pointed base R bits i).Fits w out :=
    ⟨safe _ (by simpa [Bank.size] using point),row _⟩
  have grp : (globalGroup base R bits).Fits w out :=
    ⟨safe _ (by simpa [Bank.size] using point),row 6,ptr 3⟩
  have global : (ProtocolRAMSupergroupDirectory.groupBank superStart K).Fits w out :=
    safe _ (by change superStart+ProtocolRAMSupergroupDirectory.span K≤ out; omega)
  have offset : (ProtocolRAMSupergroupDirectory.offsetBank superStart K).Fits w out :=
    safe _ (by change superStart+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤ out; omega)
  have lift (c : ℕ) (x : Expr) (ok : x.Fits w out) : (scale c x).Fits w out := by
    induction c with
    | zero => trivial
    | succ i ih => exact ⟨ok,ih⟩
  have side (port tag : Fin 10) :
      (SiteROM.atPort siteBase G H superStart K (copies k attempts) (globalGroup base R bits)
        (pointed base R bits port) (field base R tag)).Fits w out :=
    ⟨safe _ sites,⟨safe _ offsets,global,grp⟩,⟨offset,grp⟩,
      lift 1 _ ⟨row tag,lift _ _ (ptr port)⟩⟩
  exact ⟨⟨row 0,trivial,trivial,global,grp⟩,⟨row 0,trivial,row 1,side 4 7⟩,
    ⟨row 0,trivial,row 2,side 5 8⟩,row 9,trivial⟩

theorem Rows.frame {c : CatalogueRows.CoreSource} {order : Fin R ≃ Edges S h (2^W) k}
    {dir : Directory (reserved h W (copies k attempts)) H} {π : Equiv.Perm (Fin (2^h))}
    {M out : ℕ} {m m' : Memory w} (rows : Rows c order dir π M m) (readable : Fits c w out)
    (retain : ∀a< out,m' a=m a) : Rows c order dir π M m' := by
  intro r
  obtain ⟨g,l,u,cost,menu⟩ := rows r
  have eq (e : Expr) (f : e.Fits w out) := eval_below e (r.val:Word w) m m' f retain
  exact ⟨(eq _ readable.group).trans g,(eq _ readable.left).trans l,(eq _ readable.right).trans u,
    (eq _ readable.lengthCode).trans cost,(eq _ readable.menu).trans menu⟩

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
