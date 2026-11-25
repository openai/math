import OAI.Hierarchy.ProtocolRAMCatalogueRowFields

namespace OAI
/-! # Address and native instruction bounds for the common row serializer -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

def CoreSource.All (s : CoreSource) (P : Expr→Prop) :=
  P s.group ∧ P s.left ∧ P s.right ∧ P s.lengthCode ∧ P s.menu

def BoughtSource.All (s : BoughtSource) (P : Expr→Prop) :=
  P s.group ∧ P s.left ∧ P s.right ∧ P s.flag ∧ P s.menu

theorem fits_atRow {W bound : ℕ} (x j : Expr) (hx : x.Fits W bound) (hj : j.Fits W bound) :
    (x.atRow j).Fits W bound := by
  induction x <;> simp_all only [Expr.atRow,Expr.Fits] <;> tauto

theorem Board.select_fits {W limit : ℕ} (b : Board) (x y : Expr)
    (hx : x.Fits W limit) (hy : y.Fits W limit) : (b.select x y).Fits W limit :=
  ⟨trivial,trivial,hx,fits_atRow _ _ hy ⟨trivial,trivial⟩⟩

theorem Board.geometry_fits {W limit : ℕ} (b : Board) (f : Fin 7)
    (hc : b.core.All (Expr.Fits W limit)) (hb : b.bought.All (Expr.Fits W limit)) :
    (b.geometry f).Fits W limit := by
  obtain ⟨cg,cl,cr,ck,cm⟩ := hc
  obtain ⟨bg,bl,br,bf,bm⟩ := hb
  have left := b.select_fits _ _ cl bl
  have right := b.select_fits _ _ cr br
  fin_cases f
  · exact b.select_fits _ _ cg bg
  · exact ⟨left,right,left,right⟩
  · exact ⟨left,right,right,left⟩
  · exact ⟨trivial,trivial⟩
  · trivial
  · exact b.select_fits _ _ ck trivial
  · exact b.select_fits _ _ cm ⟨bf,trivial,trivial,bm⟩

theorem substitute_work (x j : Expr) : (x.atRow j).work≤x.work*(j.work+1) := by
  induction x <;> simp only [Expr.atRow,Expr.work,Nat.add_mul,Nat.one_mul] at * <;> omega

theorem Board.select_work (b : Board) (x y : Expr) :
    (b.select x y).work≤x.work+5*y.work+4 := by
  have sub := substitute_work y (.op .sub .row (.lit b.coreRows))
  simp only [select,Expr.work] at *
  omega

/-- The number of core and bought candidates affects the number of rows in the
scan. The seven expressions each have constant overhead per source instruction. -/
theorem Board.geometry_work (b : Board) (f : Fin 7) (K : ℕ)
    (hc : b.core.All (fun e=>e.work≤K)) (hb : b.bought.All (fun e=>e.work≤K)) :
    (b.geometry f).work≤32*(K+1) := by
  obtain ⟨cg,cl,cr,ck,cm⟩ := hc
  obtain ⟨bg,bl,br,bf,bm⟩ := hb
  have hg := b.select_work b.core.group b.bought.group
  have hl := b.select_work b.core.left b.bought.left
  have hr := b.select_work b.core.right b.bought.right
  have hk := b.select_work b.core.lengthCode (.lit 1)
  have hm := b.select_work b.core.menu (.branch .eq b.bought.flag (.lit 0) (.lit 0) b.bought.menu)
  simp only [Expr.work] at hk hm
  let L := b.select b.core.left b.bought.left
  let R := b.select b.core.right b.bought.right
  change L.work≤_ at hl
  change R.work≤_ at hr
  fin_cases f
  · change (b.select b.core.group b.bought.group).work≤_
    omega
  · change L.work+R.work+L.work+R.work+1≤_
    omega
  · change L.work+R.work+R.work+L.work+1≤_
    omega
  · change 1+2+1≤_
    omega
  · change 1≤_
    omega
  · change (b.select b.core.lengthCode (.lit 1)).work≤_
    omega
  · change (b.select b.core.menu (.branch .eq b.bought.flag (.lit 0) (.lit 0) b.bought.menu)).work≤_
    omega

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
