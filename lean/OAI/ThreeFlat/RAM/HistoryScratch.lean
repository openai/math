import OAI.ThreeFlat.RAM.PhysicalPinsNat
import Mathlib.Tactic.Ring

namespace OAI
/-! # Selected-node arenas with direct indexed subregions -/

namespace ThreeFlat.RAM.HistoryScratch

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

/-- Every stage has bounded active motifs and parties. Parallel tile copies
always occupy a single dense batch sector, regardless of their number. -/
structure Local where
  motif : ℕ
  party : ℕ
  family : ℕ
  bank : ℕ
  deriving DecidableEq

/-- The two reserved ordinals at each level represent the shared per-node
and per-motif records; other ordinals are their actual physical party ids. -/
def sector (_M P : ℕ) (x : Local) := (((x.motif*(P+2)+x.party)*8+x.family)*32+x.bank)

def atWord (base V M P node : ℕ) (x : Local) (j : ℕ) :=
  base+(node*V+sector M P x)*V+j

def Local.Valid (M P : ℕ) (x : Local) := x.motif<M+2 ∧ x.party<P+2 ∧ x.family<8 ∧ x.bank<32

theorem sector_lt {M P : ℕ} {x : Local} (ok : x.Valid M P) : sector M P x < (M+2)*(P+2)*8*32 := by
  rcases ok with ⟨h₁,h₂,h₃,h₄⟩
  have q : x.motif*(P+2)+x.party<(M+2)*(P+2) := calc
    _ < x.motif*(P+2)+(P+2) := Nat.add_lt_add_left h₂ _
    _ = (x.motif+1)*(P+2) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h₁
  unfold sector
  omega

theorem separated {base V M P i i' : ℕ} {x y : Local} {j j' : ℕ}
    (sectorRoom : (M+2)*(P+2)*8*32≤V) (hx : x.Valid M P) (hy : y.Valid M P)
    (lo : j<V) (hi : j'<V) (same : atWord base V M P i x j=atWord base V M P i' y j') :
    i=i' ∧ x=y ∧ j=j' := by
  have pos := Nat.zero_lt_of_lt lo
  have sx := (sector_lt hx).trans_le sectorRoom
  have sy := (sector_lt hy).trans_le sectorRoom
  have block (a b c d : ℕ) (hb : b<V) (hd : d<V) (h : a*V+b=c*V+d) : a=c ∧ b=d := by
    have q := congrArg (·/V) h
    have r := congrArg (·%V) h
    simpa [Nat.mul_comm a V,Nat.mul_comm c V,Nat.mul_add_div pos,Nat.div_eq_of_lt hb,Nat.div_eq_of_lt hd,
      Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hd] using And.intro q r
  have sum : (i*V+sector M P x)*V+j=(i'*V+sector M P y)*V+j' := by
    unfold atWord at same; omega
  obtain ⟨a,b⟩ := block _ _ _ _ lo hi sum
  obtain ⟨c,d⟩ := block _ _ _ _ sx sy a
  refine ⟨c,?_,b⟩
  rcases hx with ⟨_,xp,xf,xb⟩
  rcases hy with ⟨_,yp,yf,yb⟩
  unfold sector at d
  have k : x.bank=y.bank ∧ (x.motif*(P+2)+x.party)*8+x.family=(y.motif*(P+2)+y.party)*8+y.family := by omega
  have k' : x.family=y.family ∧ x.motif*(P+2)+x.party=y.motif*(P+2)+y.party := by omega
  have q := congrArg (·/(P+2)) k'.2
  have r := congrArg (·%(P+2)) k'.2
  have pos' : 0<P+2 := by omega
  simp [Nat.mul_comm x.motif (P+2),Nat.mul_comm y.motif (P+2),Nat.mul_add_div pos',Nat.div_eq_of_lt xp,Nat.div_eq_of_lt yp,Nat.mod_eq_of_lt xp,Nat.mod_eq_of_lt yp] at q r
  cases x; cases y; simp_all

/-- Every selected record lies inside one S workspace even if each chosen
node has its own private sector bank. The empty space requires no RAM steps. -/
theorem fits {base V M P i : ℕ} {x : Local} {j : ℕ}
    (count : i<V^2) (sectorRoom : (M+2)*(P+2)*8*32≤V) (hx : x.Valid M P) (hj : j<V) :
    atWord base V M P i x j<base+V^4 := by
  have sg := (sector_lt hx).trans_le sectorRoom
  have inner : i*V+sector M P x<V^2*V := by
    calc
      _ < i*V+V := Nat.add_lt_add_left sg _
      _ = (i+1)*V := by ring
      _ ≤ V^2*V := Nat.mul_le_mul_right _ count
  unfold atWord
  calc
    _ < base+((i*V+sector M P x)*V+V) := by omega
    _ = base+(i*V+sector M P x+1)*V := by ring
    _ ≤ base+(V^2*V)*V := Nat.add_le_add_left (Nat.mul_le_mul_right _ inner) _
    _ = _ := by ring

def formula : Formula 8 :=
  let v (i : Fin 8) : Formula 8 := .reg i
  let s := add (mul (add (mul (add (mul (v 3) (add (v 2) (.lit 2))) (v 4)) (.lit 8)) (v 5)) (.lit 32)) (v 6)
  add (add (v 0) (mul (add (mul (v 7) (v 1)) s) (v 1))) (.lit 0)

theorem value (W : ℕ) (data : Param→ℕ) (mem : ℕ→ℕ) (base V M P i : ℕ) (x : Local) :
    formula.natural W data mem ![base,V,P,x.motif,x.party,x.family,x.bank,i]=atWord base V M P i x 0 := by
  simp [formula,atWord,sector,Formula.natural,natOp]

end ThreeFlat.RAM.HistoryScratch

end OAI
