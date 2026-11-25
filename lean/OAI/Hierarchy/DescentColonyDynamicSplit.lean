import OAI.Hierarchy.DescentColonySplitRAM

namespace OAI
/-! # Reading the actual rectangular neighbor directory in the colony split pass -/

namespace Hierarchy.DescentColonies.DynamicSplit
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing
variable {ℓ k Δ w out : ℕ}
local notation "H" => 2^ℓ

abbrev Roster (ℓ Δ : ℕ) := Fin (2^ℓ)→Fin Δ→Option (Fin (2^ℓ))

def incoming (roster : Fin H→Fin Δ→Option (Fin H)) (v : Fin H) :=
  (List.ofFn (roster v)).filterMap id

def virtualBase (flagBase : ℕ→Option ℕ) (k z : ℕ) (u : Fin H) :=
  (flagBase z).map (fun b=>b+u.val*2^k)

def code (u : Option (Fin H)) : ℕ := u.elim H Fin.val

def idWord (adj : ℕ) (v : Fin H) (j : Fin Δ) : Expr :=
  .lookup ⟨adj+v.val*Δ+j.val,0⟩ (.lit 0)

/-- The instruction set in this scan has a native add. Unrolling `k` doublings
uses at most a constant times `2^k` instructions per actual neighbor read. -/
def scale : ℕ→Expr→Expr
  | 0,e=>e
  | n+1,e=>.op .add (scale n e) (scale n e)

private theorem scale_eval (n : ℕ) (e : Expr) (m : Memory w) (r : Word w) :
    (scale n e).eval m r=e.eval m r*2^n := by
  induction n with
  | zero=>simp [scale]
  | succ n ih=>simp only [scale,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,pow_succ];ring

def cell (ℓ k d : ℕ) (base : Option ℕ) (id : Expr) (x y : Block k) : Expr :=
  if group d y=group d x then
    match base with
    | none=>.lit 0
    | some b=>.branch .eq id (.lit (2^ℓ)) (.lit 0)
        (.lookup ⟨b,ℓ+k⟩ (.op .add (scale k id) (.lit y.val)))
  else .lit 0

def target (flagBase : ℕ→Option ℕ) (D d : ℕ) (v : Fin H) (p : Unit⊕Fin Δ)
    (adj : ℕ) : Option ℕ×Expr :=
  match p with
  | .inl _=>(flagBase (d+1),.lit v.val)
  | .inr j=>(flagBase (d+D),idWord adj v j)

def lane (k ℓ Δ adj : ℕ) (loadBase : Fin (2^ℓ)→ℕ) (flagBase : ℕ→Option ℕ)
    (D cap d : ℕ) (v : Fin (2^ℓ)) (x : Block k) : Expr :=
  let ys:=List.finRange (2^k)
  let sub (z : Unit⊕Fin Δ):=target flagBase D d v z adj
  let ids : List (Unit⊕Fin Δ):=.inl () :: (List.finRange Δ).map Sum.inr
  .branch .lt (.lit cap) (SplitRAM.total (SplitRAM.loadCell (loadBase v) d x) ys) (.lit 1)
    (SplitRAM.anyFlag (fun z=>SplitRAM.anyFlag (cell ℓ k d (sub z).1 (sub z).2 x) ys) ids)

def expr (k ℓ Δ adj : ℕ) (loadBase : Fin (2^ℓ)→ℕ) (flagBase : ℕ→Option ℕ)
    (D cap d : ℕ) (v : Fin (2^ℓ)) : Expr :=
  chooseField (2^k) 0 (lane k ℓ Δ adj loadBase flagBase D cap d v) .row

def Stored (adj : ℕ) (roster : Roster ℓ Δ) (m : Memory w) : Prop :=
  ∀v j,m (adj+v.val*Δ+j.val)=(code (roster v j) : Word w)

private theorem id_read (roster : Fin H→Fin Δ→Option (Fin H)) (adj : ℕ) (m : Memory w)
    (stored : Stored adj roster m) (r : Word w) (v : Fin H) (j : Fin Δ) :
    (idWord adj v j).eval m r=(code (roster v j) : Word w) := by
  simpa [idWord,Expr.eval,Bank.read,Bank.size] using stored v j

private theorem cell_read (d : ℕ) (fb : Option ℕ) (ptr : Expr) (u : Option (Fin H)) (x y : Block k)
    (m : Memory w) (r : Word w) (room : 2^(ℓ+k)<2^w) (read : ptr.eval m r=(code u : Word w)) :
    (cell ℓ k d fb ptr x y).eval m r=
      u.elim 0 (fun z=>(SplitRAM.flagCell (fb.map (fun b=>b+z.val*2^k)) d x y).eval m r) := by
  have power (n : ℕ) (hn : n≤ℓ+k) : 2^n<2^w :=
    (Nat.pow_le_pow_right (by decide) hn).trans_lt room
  have hr := power ℓ (Nat.le_add_right _ _)
  have kr := power k (Nat.le_add_left _ _)
  rcases u with _|u
  · cases fb <;> by_cases equal : group d y=group d x <;>
      simp [cell,equal,Expr.eval,read,code,Comparison.test]
  · rw [Option.elim_some,SplitRAM.eval_flagCell _ d x y m r kr]
    by_cases equal : group d y=group d x
    · simp only [equal,ite_true,cell]
      rcases fb with _|b
      · rfl
      · have live : Comparison.eq.test (u.val : Word w) ((2^ℓ : ℕ):Word w)=false := by
          have ne : (u.val : Word w) ≠ ((2^ℓ : ℕ):Word w) := by
            intro same
            have vals := congrArg Fin.val same
            rw [Fin.val_cast_of_lt (u.isLt.trans hr),Fin.val_cast_of_lt hr] at vals
            exact (Nat.ne_of_lt u.isLt) vals
          simpa [Comparison.test] using ne
        have idx : u.val*2^k+y.val<2^(ℓ+k) := by
          rw [pow_add]
          have n := Nat.mul_le_mul_right (2^k) u.isLt
          rw [Nat.succ_mul] at n
          exact (Nat.add_lt_add_left y.isLt _).trans_le n
        have castIndex : (ptr.eval m r)*2^k+(y.val:Word w) = ((u.val*2^k+y.val:ℕ):Word w) := by
          simp [read,code]
        simp only [Expr.eval,read,code,Option.elim_some,live,Bool.false_eq_true,ite_false,
          Bank.read,Bank.size,RowOp.opcode,BinaryOp.eval,scale_eval]
        simp only [read,code,Option.elim_some] at castIndex
        rw [castIndex,Fin.val_cast_of_lt (idx.trans room),Nat.mod_eq_of_lt idx]
        simp [SplitRAM.flagWord,Nat.add_assoc]
    · simp [cell,equal,Expr.eval]

private theorem any_filter {A B : Type} (left : A→Expr) (right : B→Expr) (which : A→Option B)
    (m : Memory w) (r : Word w) (agree : ∀j,(left j).eval m r=(which j).elim 0 (fun u=>(right u).eval m r))
    (xs : List A) : (SplitRAM.anyFlag left xs).eval m r=(SplitRAM.anyFlag right (xs.filterMap which)).eval m r := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    cases h : which x with
    | none=>simp [SplitRAM.anyFlag,h,Expr.eval,agree x,Comparison.test,ih]
    | some u=>simp only [SplitRAM.anyFlag,List.filterMap_cons,h,Expr.eval,agree x,Option.elim_some,ih]; rfl

private theorem any_congr {A : Type} (a b : A→Expr) (m : Memory w) (r : Word w)
    (equal : ∀i,(a i).eval m r=(b i).eval m r) (xs : List A) :
    (SplitRAM.anyFlag a xs).eval m r=(SplitRAM.anyFlag b xs).eval m r := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>simp [SplitRAM.anyFlag,Expr.eval,equal,ih]

private theorem any_zero {A : Type} (a : A→Expr) (m : Memory w) (r : Word w)
    (equal : ∀i,(a i).eval m r=0) (xs : List A) : (SplitRAM.anyFlag a xs).eval m r=0 := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>simp [SplitRAM.anyFlag,Expr.eval,equal,ih,Comparison.test]

private theorem marks_read (d : ℕ) (fb : Option ℕ) (ptr : Expr) (u : Option (Fin H))
    (x : Block k) (m : Memory w) (r : Word w) (room : 2^(ℓ+k)<2^w) (rd : ptr.eval m r=(code u : Word w)) :
    (SplitRAM.anyFlag (cell ℓ k d fb ptr x) (List.finRange (2^k))).eval m r=
      u.elim 0 (fun z=>(SplitRAM.anyFlag (SplitRAM.flagCell (fb.map (fun b=>b+z.val*2^k)) d x)
        (List.finRange (2^k))).eval m r) := by
  cases u with
  | none=>exact any_zero _ m r (fun y=>cell_read d fb ptr none x y m r room rd) _
  | some z=>exact any_congr _ _ m r (fun y=>cell_read d fb ptr (some z) x y m r room rd) _

private theorem any_map {A B : Type} (a : B→Expr) (f : A→B) (xs : List A) :
    SplitRAM.anyFlag a (xs.map f)=SplitRAM.anyFlag (a∘f) xs := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp [SplitRAM.anyFlag,ih]

theorem read_eq (roster : Fin H→Fin Δ→Option (Fin H)) (adj : ℕ)
    (loadBase : Fin H→ℕ) (flagBase : ℕ→Option ℕ) (D cap d : ℕ) (v : Fin H)
    (m : Memory w) (stored : Stored adj roster m) (room : 2^(ℓ+k)<2^w) (x : Block k) :
    (expr k ℓ Δ adj loadBase flagBase D cap d v).eval m (x.val : Word w)=
      (SplitRAM.expr k (incoming roster) loadBase (virtualBase flagBase k) D cap d v).eval m (x.val : Word w) := by
  have kr : 2^k<2^w := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left k ℓ)).trans_lt room
  have value : (Expr.eval m (x.val : Word w) .row).val=0+x.val := by
    simpa only [Expr.eval,Nat.zero_add] using Fin.val_cast_of_lt (x.isLt.trans kr)
  rw [expr,SplitRAM.expr,eval_chooseField _ _ _ _ _ _ x (by omega) value,
    eval_chooseField _ _ _ _ _ _ x (by omega) value]
  let ys:=List.finRange (2^k)
  let old (z : ℕ×Fin H):=SplitRAM.anyFlag (SplitRAM.flagCell (virtualBase flagBase k z.1 z.2) d x) ys
  let new (z : Unit⊕Fin Δ):=SplitRAM.anyFlag
    (cell ℓ k d (target flagBase D d v z adj).1 (target flagBase D d v z adj).2 x) ys
  have self : (new (.inl ())).eval m (x.val : Word w)=(old (d+1,v)).eval m (x.val : Word w) :=
    marks_read d (flagBase (d+1)) (.lit v.val) (some v) x m _ room rfl
  have neigh (j : Fin Δ) : (new (.inr j)).eval m (x.val : Word w)=
      (roster v j).elim 0 (fun z=>(old (d+D,z)).eval m (x.val : Word w)) :=
    marks_read d (flagBase (d+D)) (idWord adj v j) (roster v j) x m _ room (id_read roster adj m stored _ v j)
  have tail := any_filter (fun j=>new (.inr j)) (fun u=>old (d+D,u)) (roster v) m (x.val:Word w) neigh (List.finRange Δ)
  change (Expr.branch .lt (.lit cap) _ (.lit 1) (SplitRAM.anyFlag new (_::_))).eval m _=
      (Expr.branch .lt (.lit cap) _ (.lit 1) (SplitRAM.anyFlag old (_::_))).eval m _
  simp only [Expr.eval,SplitRAM.anyFlag,self,any_map]
  have lists : (List.finRange Δ).filterMap (roster v)=(incoming roster v) := by
    simp [incoming,List.ofFn_eq_map]
  rw [lists] at tail
  simp only [Function.comp_def,tail]
  rfl

private theorem scale_fits (e : Expr) (h : e.Fits w out) (n : ℕ) : (scale n e).Fits w out := by
  induction n with
  | zero=>exact h
  | succ n ih=>exact ⟨ih,ih⟩

private theorem scale_work (n : ℕ) (e : Expr) : (scale n e).work+1=(e.work+1)*2^n := by
  induction n with
  | zero=>simp [scale]
  | succ n ih=>
    simp only [scale,Expr.work,pow_succ,←Nat.mul_assoc]
    omega

private theorem cell_fits (d : ℕ) (fb : Option ℕ) (ptr : Expr) (x y : Block k)
    (psi : ptr.Fits w out) (rectangle : ∀b,fb=some b→(Bank.mk b (ℓ+k)).Fits w out) :
    (cell ℓ k d fb ptr x y).Fits w out := by
  by_cases eqn : group d y=group d x
  · cases h : fb with
    | none=>simp [cell,eqn,Expr.Fits]
    | some b=>
      simp only [cell,eqn,ite_true]
      exact ⟨psi,trivial,trivial,rectangle b h,scale_fits ptr psi _,trivial⟩
  · simp [cell,eqn,Expr.Fits]

theorem fits (adj : ℕ) (loadBase : Fin H→ℕ) (flagBase : ℕ→Option ℕ) (D cap d : ℕ) (v : Fin H)
    (weights : (Bank.mk (loadBase v) k).Fits w out)
    (roster : ∀j : Fin Δ,(Bank.mk (adj+v.val*Δ+j.val) 0).Fits w out)
    (flags : ∀z b,flagBase z=some b→(Bank.mk b (ℓ+k)).Fits w out) :
    (expr k ℓ Δ adj loadBase flagBase D cap d v).Fits w out := by
  apply SplitRAM.fits_choice
  intro x
  refine ⟨trivial,SplitRAM.fits_total _ (fun y=>SplitRAM.fits_loadCell _ _ x y weights) _,trivial,
    SplitRAM.fits_anyFlag _ (fun z=>SplitRAM.fits_anyFlag _ (fun y=>?_) _) _⟩
  cases z with
  | inl _=>exact cell_fits d (flagBase (d+1)) (.lit v.val) x y trivial (flags (d+1))
  | inr j=>exact cell_fits d (flagBase (d+D)) (idWord adj v j) x y ⟨roster j,trivial⟩ (flags (d+D))

def cellWork (k : ℕ) := 20+7*2^k
def neighborWork (k : ℕ) := 1+2^k*(cellWork k+3)
def laneWork (k Δ : ℕ) := (1+2^k*7)+(1+(Δ+1)*(neighborWork k+3))+3
def workBound (k Δ : ℕ) := 1+2^k*(laneWork k Δ+4)

/-- A whole-directory prefix bound suffices for every one-word neighbor access. -/
theorem roster_fits (adj : ℕ) (v : Fin H) (j : Fin Δ)
    (wide : 1<2^w) (directoryEnd : adj+H*Δ≤out) :
    (Bank.mk (adj+v.val*Δ+j.val) 0).Fits w out := by
  have last := Nat.mul_le_mul_right Δ v.isLt
  rw [Nat.succ_mul] at last
  have slot := j.isLt
  unfold Bank.Fits Bank.size
  dsimp only
  exact ⟨by decide,wide,by omega⟩

/-- The fixed program size is cubic in the block width and linear in the roster width.
In particular it does not grow with the number of possible host identifiers. -/
theorem workBound_le (k Δ : ℕ) : workBound k Δ≤64*(Δ+1)*(2^k)^3 := by
  let r:=2^k
  have nonzero : r≠0 := (Nat.two_pow_pos k).ne'
  obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  change 1+r*(((1+r*7)+(1+(Δ+1)*((1+r*((20+7*r)+3))+3))+3)+4)≤64*(Δ+1)*r^3
  rw [hs]
  simp only [Nat.succ_eq_add_one]
  ring_nf
  omega

private theorem cell_work (ℓ k d : ℕ) (fb : Option ℕ) (ptr : Expr) (h : ptr.work≤6) (x y : Block k) :
    (cell ℓ k d fb ptr x y).work≤cellWork k := by
  have bound := Nat.mul_le_mul_right (2^k) (Nat.succ_le_succ h)
  rw [←scale_work] at bound
  by_cases eqn : group d y=group d x
  · cases fb <;> simp [cell,eqn,Expr.work,cellWork] <;> omega
  · simp [cell,eqn,Expr.work,cellWork]; omega

theorem work (adj : ℕ) (loadBase : Fin H→ℕ) (flagBase : ℕ→Option ℕ) (D cap d : ℕ) (v : Fin H) :
    (expr k ℓ Δ adj loadBase flagBase D cap d v).work≤workBound k Δ := by
  apply SplitRAM.work_choice
  intro x
  let ys:=List.finRange (2^k)
  let ids : List (Unit⊕Fin Δ):=.inl ()::(List.finRange Δ).map Sum.inr
  let sub (z : Unit⊕Fin Δ):=target flagBase D d v z adj
  have weight := SplitRAM.work_total _ 6 (SplitRAM.work_loadCell (loadBase v) d x) ys
  have point (z : Unit⊕Fin Δ) (y : Block k) : (cell ℓ k d (sub z).1 (sub z).2 x y).work≤cellWork k := by
    apply cell_work
    cases z <;> simp [sub,target,idWord,Expr.work]
  have marked (z : Unit⊕Fin Δ) :
      (SplitRAM.anyFlag (cell ℓ k d (sub z).1 (sub z).2 x) ys).work≤neighborWork k := by
    simpa [ys,neighborWork] using SplitRAM.work_anyFlag _ (cellWork k) (point z) ys
  have tail := SplitRAM.work_anyFlag _ (neighborWork k) marked ids
  have lengths : ids.length=Δ+1 := by simp [ids]
  rw [lengths] at tail
  simp only [ys,List.length_finRange] at weight
  change (1+_+1+_+1)≤laneWork k Δ
  dsimp only [laneWork]
  dsimp only [sub,ys,ids] at weight tail
  omega

end Hierarchy.DescentColonies.DynamicSplit

end OAI
