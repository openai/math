import OAI.Computability.IntegerMultiplication.Base

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Code Strip Adic Net
variable {J W L I : Type} [Fintype J] [DecidableEq J] [Fintype W]
variable {p : ℕ} [NeZero p] {discount : ℝ}

noncomputable section

variable (D : ℕ) (p) (W)
abbrev SmallBase (D p : ℕ) (W : Type) := Boll D p W 0
abbrev Canopy (D p : ℕ) (W : Type) := Sigma fun k => Boll D p W (k+1)
variable {D p W}
private def low (i : SmallBase D p W) : Where D p W := ⟨0,i⟩
private def high (i : Canopy D p W) : Where D p W := ⟨i.1+1,i.2⟩
omit [Fintype W] [NeZero p] in
private theorem case_green (x : Where D p W) :
    (green x.1=false → ∃ i : SmallBase D p W,x=low i) ∧
    (green x.1=true → ∃ i : Canopy D p W,x=high i) := by
  rcases x with ⟨_|k,w⟩ <;> simp only [green]
  · exact ⟨fun _ => ⟨w,rfl⟩,fun q => Bool.noConfusion q⟩
  exact ⟨fun q => Bool.noConfusion q,fun _ => ⟨⟨_,w⟩,rfl⟩⟩

omit [Fintype W] [NeZero p] in
private theorem Tunnel.select {A B : Where D p W → Tree} {w : Where D p W→ℝ}
    {o : Oracle (Where D p W)} {a : Where D p W → List (Where D p W)}
    (x : Tunnel o (w ∘ low) (a ∘ low) (A ∘ low) (B ∘ low))
    (y : Tunnel o (w ∘ high) (a ∘ high) (A ∘ high) (B ∘ high)) :
    Tunnel o w a (together (send ∘ green ∘ Sigma.fst) A) B := by
  refine Code.Tunnel.fork (green ∘ Sigma.fst) ?_ ?_
  · let I := {i : Where D p W // green i.1=false}
    choose f E using fun i : I => (case_green i.1).1 i.2
    simpa only [Function.comp_def, ← E] using x.slide f
  let I := {i : Where D p W // green i.1=true}
  choose f E using fun i : I => (case_green i.1).2 i.2
  simpa only [Function.comp_def, ← E] using y.slide f

private def invitation (h : (i : Canopy D p W) → List (Where D p W)) :
    Where D p W → List (Where D p W)
| ⟨0,_⟩ => []
| ⟨_+1,v⟩ => h ⟨_,v⟩

variable (R : Series W)
omit [NeZero p] in
private theorem forecast (v : 2≤D) (hp : 2≤p) (S : ℤ)
    (d : let X := Canopy D p W
      let gov := Where.government D p W v
      Hopto (Where.current R) (gov.pull high) (fun i:X => (high i).plates.count)
        (fun i=>timeNow (high i)) (fun i x => SubZone (high i) x) S
        ((Where.current R).issue ∘ high) ((Where.current R).reply ∘ high)) :
    let j := (Where.current R (D:=D) (p:=p))
    let N := fun x : Where D p W => x.plates.count
    let L := timeNow (D:=D) (p:=p) (W:=W)
    let G := Where.government D p W v
    ∃ k uses, (∀ x y,y∈uses x → SubZone x y) ∧ (∀ x,x.1>0 → (uses x).length≤S) ∧
      (∀ x,x.1=0 → uses x=[]) ∧ (∀ w, Tunnel ⟨w,j.issue,j.reply⟩ (mass G N L k) uses j.issue j.reply) := by
  let G := Where.government D p W v
  let j : Job (Where D p W) := Where.current R
  let N (i : Where D p W) := i.plates.count
  obtain ⟨U,A,B,C⟩ := d.safe
  have m := primeval D p R (id : SmallBase D p W → _) hp (r:=G.pull low) rfl
  obtain ⟨a,b⟩ := (Quest.entry (j:=j) m).eligible
  obtain ⟨h,c⟩ := C.eligible

  -- activate choose arm by tag from ticket
  have hx : G.Small G.header := Regime.self
  have sy := Where.station_t (id : Where D p W→_) hp hx
  have pe (x : Where D p W) : (skein W R x.2.cargo x.1).count ≤ timeNow x := by rw [strands]; exact le_rfl
  have f := cloth_size (l:=timeNow (D:=D)) _ _ sy (fun i => i.2.option) pe
  have q := Rip.header (l:=timeNow (D:=D)) (r:=G) sy.1 Regime.self
  have iq : Alive G N timeNow j.issue := Rip.alivePair q f
  have prepared := ((Rip.split iq).1.chain (Rip.header (r:=G) sy.1
    (Where.signals (fun i => i.1) (fun i => i.site) hx).1)).twice iq
  obtain ⟨r,e⟩ := (Quest.entry (j:=j) prepared).eligible
  let k := a+h+r
  refine ⟨k,invitation U,?_,?_,?_,?_⟩
  · rintro ⟨_|k,x⟩ y
    · simp [invitation]
    exact A ⟨k,x⟩ _
  · rintro ⟨_|k,x⟩ i
    · contradiction
    exact B ⟨k,x⟩
  · rintro ⟨k,x⟩ z; change k=0 at z; subst k -- z : k=0 defeq
    rfl
  intro fee
  have z : Tunnel ⟨fee,j.issue,j.reply⟩ (mass G N timeNow k) (invitation U)
      (together (send ∘ green ∘ Sigma.fst) j.issue) j.reply :=
    Tunnel.select (Tunnel.monoT (b fee)
      (mass_le (by omega : a ≤ k))) (Tunnel.monoT (c fee) (mass_le (by omega : h ≤ k)))
  exact (Tunnel.monoT (e fee) (mass_le (by omega : r≤k))).join z

-- fare and accounting
def loft (k : ℕ) (x : Where D p W) : ℝ :=
  x.plates.count * ((timeNow x:ℕ) + ((x.site.supplyLimit:ℝ)+1)^k*(dim W:ℝ)^x.1)
def fare (z : ℝ) (k : ℕ) (x : Where D p W) : ℝ :=
  loft k x * ((D:ℝ)^z)^x.1

omit [NeZero p] in
theorem mild (H : 1≤dim W) (k : ℕ) (x : Where D p W) :
    ((x.plates.count:ℕ):ℝ)*((timeNow x:ℝ)+((x.site.supplyLimit:ℝ)+1)^k) ≤ loft k x := by
  unfold loft
  gcongr
  have h := one_le_pow₀ (n:=x.1) (show (1:ℝ) ≤ dim W by exact_mod_cast H)
  exact le_mul_of_one_le_right (by positivity) h

omit [NeZero p] in
private theorem shrink {x y : Where D p W} (k) (h : SubZone x y) :
    loft k y * dim W = loft k x := by
  unfold loft timeNow
  simp only [← h.equalRoom,← h.equalScale,← h.passenger,← h.down,pow_succ]
  push_cast
  ring

omit [NeZero p] in
private theorem settleCost (k : ℕ) (z : ℝ) (R_ : Series W)
    (v : 2≤D) (hp : 2≤p) (m : 1≤dim W) (g : 0≤z) (S : ℤ)
    (u : (S:ℝ)/dim W < (D:ℝ)^z) (U : Where D p W → List (Where D p W))
    (Y : ∀ x y,y∈U x → SubZone x y)
    (L : ∀ x,x.1>0 → (U x).length ≤ S)
    (B : ∀ x,x.1=0 → U x=[]) :
    let j := (Where.current R_ (D:=D) (p:=p))
    let N := fun x : Where D p W => x.plates.count
    let G := Where.government D p W v
    let T := fare z k (D:=D) (p:=p) (W:=W)
    let M := mass G N timeNow k
    (∀ x,1 ≤ T x ∧ M x ≤ T x) ∧
      ∃ a:ℝ,0<a ∧ ∀ x, Oracle.reserve (Oracle.mk T j.issue j.reply) (U x)+a*T x≤T x := by
  let G := Where.government D p W v
  let N (x : Where D p W) := x.plates.count
  let j := (Where.current R_ (D:=D) (p:=p))
  let T := fare z k (D:=D) (p:=p) (W:=W)
  let M := mass G N timeNow k
  change (_ ∧ ∃ a:ℝ,0<a ∧ ∀ x, Oracle.reserve ⟨T,j.issue,j.reply⟩ (U x)+a*T x ≤ T x)
  have N0 : ∀ x, 1≤N x := (Where.station_t (id : Where D p W → _) hp (Regime.self (r:=G))).1
  let K : ℝ := (D:ℝ) ^ z
  have K0 : 1 ≤ K := by
    apply Real.one_le_rpow <;> first | exact g | exact_mod_cast v.trans' (by decide : 1≤2)
  have h (x) := (mild m k (D:=D) (p:=p) x)
  have pass (x : Where D p W) : 1 ≤ T x ∧ M x ≤ T x := by
    have e : M x ≤ loft k x := mild m k x
    have u : 1≤ M x := unit_mass N0 k x
    have d : loft k x ≤ T x := le_mul_of_one_le_right (by linarith) (one_le_pow₀ K0)
    exact ⟨u.trans (e.trans d),e.trans d⟩
  have wc : (0:ℝ)<dim W := by exact_mod_cast m
  have kc : 0<K := lt_of_lt_of_le (by norm_num) K0
  refine ⟨pass,(1-max 0 ((S:ℝ)/(dim W*K))), by
    have e : (S:ℝ)/(dim W*K) < 1 := (div_lt_one (mul_pos wc kc)).2 (by have := (div_lt_iff₀ wc).1 u; unfold K at *; linarith)
    linarith [show max 0 ((S:ℝ)/(dim W*K)) < 1 from max_lt (by norm_num) e], fun x => ?_⟩
  have positive : 0 < T x := lt_of_lt_of_le (by norm_num) (pass x).1
  suffices q : Oracle.reserve ⟨T,j.issue,j.reply⟩ (U x) ≤
      max 0 ((S:ℝ)/(dim W*K))*T x by linarith
  have se (l : List (Where D p W)) (h : ∀ y∈l,SubZone x y) :
      Oracle.reserve ⟨T,j.issue,j.reply⟩ l *
        ((dim W:ℝ)*K) = l.length * T x := by
    induction l with
    | nil => simp [Oracle.reserve]
    | cons c b ih =>
      have t := h c List.mem_cons_self
      have ok : T c * ((dim W:ℝ)*K) = T x := by
        change loft k c * K^_ * _=loft k x * K^_
        rw [← t.down,pow_succ,← shrink k t]; ring
      specialize ih (fun y hh => h y (by simp [hh]))
      rw [show Oracle.reserve ⟨T,j.issue,j.reply⟩ (c::b) =
        T c + Oracle.reserve ⟨T,j.issue,j.reply⟩ b by simp [Oracle.reserve]]
      rw [List.length_cons,add_mul, ok, ih]; push_cast; ring
  have us := se (U x) (Y x)
  cases ne_or_eq x.1 0 with
  | inl n =>
    have v := L x (by omega)
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) positive.le)
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos wc kc), us]
    have hh : (((U x).length:ℕ):ℝ) ≤ (S:ℝ) := by exact_mod_cast v
    exact mul_le_mul_of_nonneg_right hh positive.le
  | inr n =>
    simp only [B x n,Oracle.reserve,List.map_nil,List.sum_nil]
    exact mul_nonneg (le_max_left ..) positive.le

variable (d : Design J W L p discount)
include d
theorem accelerate (h : 0≤discount) :
    ∃ k, Sized (fare discount k (D:=dim J))
      (Where.current R (p:=p)).issue (Where.current R).reply := by
  let S := ∑ w,d.train.cost (fun _ => d.quota) w
  obtain ⟨k,u,x,y,m,g⟩ := forecast R d.occupancy d.large S
    (transport d R (k:= Sigma.fst) (fun i : Canopy (dim J) p W => i.2) rfl)
  obtain ⟨z,a,c,b⟩ := settleCost k discount R d.occupancy d.large d.roles h S d.saved u x y m
  refine ⟨k,Code.Tunnel.solve (Oracle.mk _ (Where.current R).issue _) (g _)
    (fun i => (z i).1) (fun i => (z i).2) a c b Sigma.fst ?_⟩
  intro a b w
  exact (x a b w).down ▸ Nat.lt_succ_self _
end
end Loom

end IntegerMultiplication
end Computability
end OAI
