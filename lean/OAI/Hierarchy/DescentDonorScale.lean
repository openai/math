import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Fixed exponent estimates for data fields of the compiler's packed donor tables -/

namespace Hierarchy.DescentCompiler.TerminalScale

/-- A family of integer fields with one exponent valid at all chronological ages. -/
def AgeBound {ι : Type*} (age value : ι→ℕ) : Prop := ∃e : ℕ,∀x,value x≤ scale (age x) e

namespace AgeBound
variable {ι : Type*} {age f g l : ι→ℕ}

theorem const (age : ι→ℕ) (a : ℕ) : AgeBound age (fun _=>a) := by
  refine ⟨a,fun x=>?_⟩
  exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos (age x))))

theorem mono (F : AgeBound age f) (smaller : ∀x,g x≤f x) : AgeBound age g := by
  obtain ⟨e,rows⟩:=F
  exact ⟨e,fun x=>(smaller x).trans (rows x)⟩

theorem mul (F : AgeBound age f) (G : AgeBound age g) : AgeBound age (fun x=>f x*g x) := by
  obtain ⟨u,rows⟩:=F
  obtain ⟨v,columns⟩:=G
  exact ⟨u+v,fun x=> by rw [←scale_mul];exact Nat.mul_le_mul (rows x) (columns x)⟩

theorem add (F : AgeBound age f) (G : AgeBound age g) : AgeBound age (fun x=>f x+g x) := by
  obtain ⟨u,rows⟩:=F
  obtain ⟨v,columns⟩:=G
  refine ⟨1+(u+v),fun x=>?_⟩
  have grow (a b : ℕ) (ab : a≤b) : scale (age x) a≤ scale (age x) b :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_right _ ab)
  have a: f x≤ scale (age x) (u+v) :=(rows x).trans (grow _ _ (by omega))
  have b: g x≤ scale (age x) (u+v) :=(columns x).trans (grow _ _ (by omega))
  have two : 2≤ scale (age x) 1 := by
    change 2^1≤2^(1*(age x+1))
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  calc
    _ ≤ 2*scale (age x) (u+v) := by
      change f x+g x≤_
      omega
    _ ≤ scale (age x) 1*scale (age x) (u+v) := Nat.mul_le_mul_right _ two
    _ = _ := scale_mul ..

theorem maximum (F : AgeBound age f) (G : AgeBound age g) :
    AgeBound age (fun x=>max (f x) (g x)) :=
  (F.add G).mono (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _,Nat.le_add_left _ _⟩)

theorem pow (F : AgeBound age f) (n : ℕ) : AgeBound age (fun x=>f x^n) := by
  obtain ⟨e,rows⟩:=F
  refine ⟨e*n,fun x=>?_⟩
  calc
    _ ≤ (scale (age x) e)^n := Nat.pow_le_pow_left (rows x) _
    _ = _ := by unfold scale;rw [←pow_mul];congr 1;ring

theorem clog (F : AgeBound age f) : AgeBound age (fun x=>Nat.clog 2 (f x)) :=
  F.mono (fun x=>Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le : f x≤2^(f x)))
end AgeBound
end Hierarchy.DescentCompiler.TerminalScale

end OAI
