import OAI.Computability.IntegerMultiplication.Brief.Fraction

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Code Carry Bits Grid Staff Strip

variable {J:Type} (r:Regime J)
/-- rational-valued real expression under construction. Size is bit length not value!
Denominator is positive integer. -/
def Blot (f:J→ℝ) : Prop :=
  ∃ (a:J→ℤ) (b:J→ℕ), Signed r a ∧ Figure r b ∧ (∀ i,0<b i) ∧
    ∀ i, f i=(a i:ℤ)/(b i:ℝ)
namespace Blot
variable {r} {x y:J→ℝ}
theorem integer {m:J→ℤ} (h : Signed r m) :
    Blot r (fun i=>(m i:ℝ)) := ⟨m,(fun _=>1),h,.natural 1,(by simp),by simp⟩
theorem constant (n:ℤ) :
    Blot r (fun _=>(n:ℝ)) := integer (.fixed n)
theorem natural {m:J→ℕ} (h:Figure r m) :
    Blot r (fun i=>(m i:ℝ)) := by simpa only [Int.cast_natCast] using integer (Signed.up h)
variable (h:Blot r x) (q:Blot r y)
include h q

theorem adding :
    Blot r (fun i=>x i+y i) := by
  obtain ⟨a,b,s,j,v,e⟩:=h
  obtain ⟨c,d,u,t,w,f⟩:=q
  refine ⟨_,_,(s.multiplying (Signed.up t)).adding (u.multiplying (Signed.up j)),j.multiplied t,fun i=>Nat.mul_pos (v i) (w i),fun i=>?_⟩
  specialize v i; specialize w i
  dsimp only; rw [e,f]; push_cast
  have B:(b i:ℝ) ≠0:= by exact_mod_cast (Nat.ne_of_gt v)
  have D:(d i:ℝ) ≠0:= by exact_mod_cast (Nat.ne_of_gt w)
  field
theorem times :
    Blot r (fun i=> x i*y i) := by
  obtain ⟨a,b,s,l,v,e⟩:=h
  obtain ⟨c,d,u,t,w,f⟩:=q
  refine ⟨_,_,s.multiplying u,l.multiplied t,fun i=>Nat.mul_pos (v i) (w i),fun i=>?_⟩
  dsimp only; rw [e,f]; push_cast; simp only [div_mul_div_comm]
theorem compared :
    Classified r (fun i=> x i<y i) := by
  obtain ⟨a,b,s,j,v,e⟩:=h
  obtain ⟨c,d,u,t,w,f⟩:=q
  have eq i : (x i<y i) ↔ a i*d i<c i*b i := by
    have t₀ : (0:ℝ)<b i := by exact_mod_cast v i
    have s₀ : (0:ℝ)<d i := by exact_mod_cast w i
    rw [e,f,div_lt_div_iff₀ t₀ s₀]
    norm_cast
  simp_rw [eq]
  exact (s.multiplying (Signed.up t)).ordered (u.multiplying (Signed.up j))
theorem choice {a:J→Prop} [DecidablePred a] (t:Classified r a) :
    Blot r (fun i=> if a i then x i else y i) := by
  obtain ⟨l,m,s,j,v,e⟩:=h
  obtain ⟨c,d,u,z,w,f⟩:=q
  exact ⟨_,_,s.choose u t,j.variant z t,fun i=> by split <;> [exact v i; exact w i],fun i=> by dsimp only; split <;> [exact e i; exact f i]⟩

theorem minimum :
    Blot r (fun i=>min (x i) (y i)) := by
  simpa only [min_def_lt] using h.choice q (h.compared q)
theorem maximum :
    Blot r (fun i=>max (x i) (y i)) := by
  simpa only [max_def_lt] using q.choice h (h.compared q)
omit q
theorem minus :
    Blot r (fun i=> -x i) :=
  let ⟨a,b,s,t,v,e⟩:=h
  ⟨_,_,s.negative,t,v,fun i=> by dsimp only; rw [e]; push_cast; ring⟩
include q in
theorem sub :
    Blot r (fun i=>x i-y i) := by simpa only [sub_eq_add_neg] using h.adding q.minus
theorem power {a:J→ℕ} (u: Realizes r a) :
    Blot r (fun i=>x i^a i) :=
  let ⟨p,b,s,t,v,e⟩:=h
  ⟨_,_,s.power u,t.repeated u,fun i => Nat.pow_pos (v i),fun i=> by dsimp only; rw [e]; push_cast; rw [div_pow]⟩
-- seldom need denominator reciprocal variable except common. positive assumption easier.
theorem invpos (v : ∀ i,0 < x i) :
    Blot r (fun i=> (x i)⁻¹) := by
  obtain ⟨a,b,s,t,l,e⟩:=h
  have w i : 0 < a i := by
    have t := v i
    rw [e] at t
    have d:(0:ℝ)<b i := by exact_mod_cast l i
    have q:(0:ℝ)<a i := by rw [lt_div_iff₀ d] at t; simpa using t
    exact_mod_cast q
  refine ⟨_,_,Signed.up t,s.toNat,(fun i=>by have:= w i; omega),fun i=>?_⟩
  have g : (Int.toNat (a i):ℤ)=a i := by have := w i; omega
  dsimp only; rw [e,inv_div]
  congr 1
  exact_mod_cast g.symm

include q in
theorem ratio (v:∀ i,0<y i) :
    Blot r (fun i=> x i/y i) := by simpa [div_eq_mul_inv] using h.times (q.invpos v)

theorem ticket :
    ∃ b : J→Ticket,r.Has b ∧ (∀ i,live (b i)) ∧ ∀ i,view (b i)=x i := by
  obtain ⟨a,t,⟨s,V,e⟩,⟨p,T,u⟩,v,g⟩:=h
  refine ⟨_,V.pair T,fun i=>by change 0<value _; rw [u]; exact v i, fun i=>?_⟩
  rw [g]; unfold view; dsimp only; rw [e,u]
omit h
theorem exam (b : J→Ticket) (T:r.Has b) (v:∀ i,live (b i)) :
    Blot r (fun i=>view (b i)) :=
  ⟨_,_,⟨_,T.ez Easy.fst,fun _=>rfl⟩,⟨_,T.ez Easy.snd,fun _=>rfl⟩,v,fun _=>rfl⟩

variable (n:J→ℕ) (p:Realizes r n) (f:(i:J)→Fin (n i)→ℝ)
variable (T : Blot (signal n p) fun i:Across n=> f i.1 i.2)
include T
theorem sums :
    Blot r (fun i=>∑ j,f i j) := by
  obtain ⟨u,t,a,b⟩:=T.ticket
  have h := (harvest n p (fun i v=> u ⟨i,v⟩) t).thenDo sumTicketP
  let d i := List.ofFn (fun j=> u ⟨i,j⟩)
  have e (i:J) := sumTicket_v (d i) (fun x v=> by
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp v; exact a _)
  have x : r.Has (fun i=>sumTicket (d i)) := h
  have E := exam _ x (fun i=> (e i).2)
  have B (i:J) : ∀ j,view (u ⟨i,j⟩)=f i j := fun j=>b _
  have W i : view (sumTicket (d i))=∑ j,f i j := by
    rw [(e i).1]
    unfold d; rw [List.map_ofFn,Signed.summing]
    simp only [Function.comp_def,B]
  simpa only [W] using E
-- map to lower index
omit T
include h p in
theorem extend :
    Blot (signal n p) (x ∘ Sigma.fst) := by
  obtain ⟨u,t,a,b⟩:=h.ticket
  have q := sendRoof n p _ (show r.Small (send ∘ u) from t)
  refine ?_
  have Z := exam _ (show (signal n p).Has (u ∘ Sigma.fst) from q) (fun i=>a i.1)
  simpa only [Function.comp_def,b] using Z
end Blot
end Brief

end IntegerMultiplication
end Computability
end OAI
