import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Numeric layout and native lookup of the three dated role pages -/
namespace Hierarchy.ProtocolRAM.RoleWidths
/-- Both words use original outer-memory order. The role index has already
been localized to the genuine site, so the only multiplication in the
address calculation is a lookup in the fixed site-stride ROM. -/
def offset (stride : Bank) (site role : Expr) : Expr := .op .add (.lookup stride site) role
end Hierarchy.ProtocolRAM.RoleWidths

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open ProtocolRAM
def pageRead {d : ℕ} (page stride : Bank) (site : Expr) (q : Fin d) : Expr :=
  .lookup page (RoleWidths.offset stride site (.lit q.val))

variable {native : ℕ}
theorem page_work {d : ℕ} (page stride : Bank) (site : Expr) (q : Fin d) :
    (pageRead page stride site q).work=site.work+12 := by
  simp only [pageRead,RoleWidths.offset,Expr.work]

theorem page_fits {d out : ℕ} (page stride : Bank) (site : Expr) (q : Fin d)
    (pageOk : page.Fits native out) (strideOk : stride.Fits native out) (siteOk : site.Fits native out) :
    (pageRead page stride site q).Fits native out := ⟨pageOk,⟨strideOk,siteOk⟩,trivial⟩

namespace DatedRoleSheets
def span (L n : ℕ) := 1+L+2*(n+n)
def sink (start L n : ℕ) (f : Fin 3) := start+f.val*span L n
def sheet (start L n : ℕ) (f : Fin 3) := sink start L n f+1
def bank (n start L bits : ℕ) (f : Fin 3) : Bank := ⟨sheet start L n f,bits⟩
end DatedRoleSheets
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end OAI
