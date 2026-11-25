import OAI.Hierarchy.DescentExteriorHopPages
import OAI.Hierarchy.DescentExteriorCalendar

namespace OAI
/-! # The literal pages and writable rows for a complete dated ancestry replay -/

namespace Hierarchy.DescentExteriorReplay
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

namespace Snapshots
variable {k : ℕ} (S : Snapshots k)
def program (S : Snapshots k) (w base f : ℕ) : ℕ → Procedure w
  | 0 => DescentStaticWordColumn.program w base (fun _ => 0) 0
  | t+1 => (S.program w base f t).seq (HopLiteral.program w (S.start base f t)
      (S.hosts t) k f t (S.pitch t) (S.shape t))

def image (S : Snapshots k) {w : ℕ} (base f : ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | t+1 => HopLiteral.output (S.start base f t) (S.hosts t) k f t (S.pitch t)
      (S.shape t) (S.image base f m t)

def clocks (S : Snapshots k) (f : ℕ) : ℕ → ℕ
  | 0 => 4
  | t+1 => S.clocks f t + (4+10*HopLiteral.words (S.hosts t) k f)

theorem run {w : ℕ} (base f : ℕ) (m : Memory w) (age : ℕ)
    (fits : S.start base f age < 2^w) :
    (S.program w base f age).Exec m (S.image base f m age) (S.clocks f age) ∧
      CheapCode (S.program w base f age) := by
  induction age with
  | zero =>
    have eqn : DescentStaticWordColumn.image base (fun _ => 0) m 0=m := by
      funext x
      exact DescentStaticWordColumn.frame base 0 _ m x (by omega)
    refine ⟨?_,DescentStaticWordColumn.cheap w base _ 0⟩
    change (DescentStaticWordColumn.program w base (fun _=>0) 0).Exec m m 4
    have beginRun : (DescentStaticWordColumn.program w base (fun _=>0) 0).Exec m
        (DescentStaticWordColumn.image base (fun _=>0) m 0) 4 :=
      DescentStaticWordColumn.mount base 0 (fun _=>0) m (by simpa [start] using fits)
    intro P N K machine pc regs pub exit installed advice cfg raw startPC input
    have actual:=@beginRun P N K machine pc regs pub exit installed advice cfg raw startPC input
    simpa only [eqn] using actual
  | succ t ih =>
    obtain ⟨prev,cheapPrev⟩:=ih (lt_of_le_of_lt (S.start_mono base f (Nat.le_succ t)) fits)
    obtain ⟨step,cheapStep,_,_⟩:=HopLiteral.run (S.start base f t) (S.hosts t) k f t
      (S.pitch t) (S.shape t) (S.image base f m t) fits
    refine ⟨?_,cheap_seq cheapPrev cheapStep⟩
    intro P R K machine pc reg pub exit installed advice cfg current enter same
    exact Procedure.Exec.then prev step machine pc reg pub exit installed advice cfg current enter same

theorem image_frame {w : ℕ} (base f : ℕ) (m : Memory w) (age x : ℕ)
    (outside : x<base ∨ S.start base f age ≤ x) : S.image base f m age x=m x := by
  induction age with
  | zero => rfl
  | succ t ih =>
    have ordered := S.start_mono base f (Nat.le_succ t)
    have lower : base ≤ S.start base f t := S.start_mono base f (Nat.zero_le t)
    have atEnd : S.start base f (t+1)=S.start base f t + HopLiteral.words (S.hosts t) k f := rfl
    exact (DescentStaticWordColumn.frame _ _ _ _ x (by rcases outside with h | h
                                                       · exact Or.inl (h.trans_le lower)
                                                       · exact Or.inr h)).trans
      (ih (outside.imp_right (fun h => ordered.trans h)))

theorem previous {w : ℕ} (base f : ℕ) (m : Memory w) {t age : ℕ}
    (live : t<age) {x : ℕ} (old : x<S.start base f (t+1)) :
    S.image base f m age x=S.image base f m (t+1) x := by
  induction age with
  | zero => omega
  | succ age ih =>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ live) with eqn | earlier
    · subst age; rfl
    · have lt : x < S.start base f age := old.trans_le (S.start_mono base f earlier)
      exact (DescentStaticWordColumn.frame _ _ _ _ x (Or.inl lt)).trans (ih earlier)

def stride (n : ℕ) := 2^Nat.clog 2 (n+1)
def page (base n t : ℕ) : Bank := ⟨base+t*stride n,Nat.clog 2 (n+1)⟩

def hop (base f scratch n t : ℕ) : Hop :=
  HopLiteral.hop (S.start base f t) (S.hosts t) k f (page scratch n t)
    (page scratch n (t+1)) (S.compact t)

theorem stage_frame {w : ℕ} (base f scratch n : ℕ) (m : Memory w) (t x : ℕ) (low : x<scratch) :
    stage (S.hop base f scratch n) n m t x=m x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    exact (early (S.hop base f scratch n t) _ (a:=x)
      (show x<scratch+(t+1)*stride n from low.trans_le (Nat.le_add_right _ _))).trans ih

theorem bank_frame {w : ℕ} (b : Bank) (m m' : Memory w) (x : Word w) (before : ℕ)
    (finish : b.base+b.size≤before) (keep : ∀i<before,m i=m' i) : b.read m x=b.read m' x :=
  keep _ (lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos b.bits)) _) finish)

theorem rooms (w base f scratch n age : ℕ)
    (shelves : S.start base f age ≤ scratch)
    (fit : scratch+(age+1)*stride n < 2^w)
    (rank : ∀t<age,∀b,S.compact t=some b → b.Fits w scratch) (t : ℕ) (live : t<age) :
    Room w n (S.hop base f scratch n t) := by
  let dest := scratch+(t+1)*stride n
  have large : n+1 ≤ stride n := Nat.le_pow_clog (by decide) _
  have top : dest+stride n ≤ scratch+(age+1)*stride n := by
    dsimp [dest]
    rw [Nat.add_assoc,←Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.succ_le_of_lt live))) _
  have room : dest+n<2^w := by omega
  have lower : scratch≤dest := Nat.le_add_right _ _
  have middle := (S.start_mono base f live).trans shelves
  have frees : S.start base f t + HopLiteral.words (S.hosts t) k f < 2^w :=
    lt_of_le_of_lt middle (lt_of_le_of_lt lower (by omega))
  rcases HopLiteral.rooms _ _ _ _ _ frees with ⟨h,l,d⟩
  have extend {b : Bank} {i : ℕ} (ok : b.Fits w i) (le : i≤dest) : b.Fits w dest :=
    ⟨ok.1,ok.2.1,ok.2.2.trans le⟩
  have ed : S.start base f (t+1)≤dest := middle.trans lower
  have src : (page scratch n t).Fits w dest := by
    change (0 < stride n) ∧ (stride n < 2^w) ∧ (scratch+t*stride n+stride n ≤ (scratch+(t+1)*stride n))
    refine ⟨Nat.two_pow_pos _,by omega,?_⟩
    rw [Nat.succ_mul,Nat.add_assoc]
  have keyOK : (key (S.hop base f scratch n t)).Fits w dest :=
    ⟨⟨extend h ed,src,trivial⟩,extend l ed,extend d ed,trivial⟩
  refine ⟨?_,room⟩
  change (read (S.hop base f scratch n t)).Fits w dest
  cases e : S.compact t with
  | none =>
    simpa only [read,hop,HopLiteral.hop,e] using keyOK
  | some b =>
    have active : (Expr.lookup b (key (S.hop base f scratch n t))).Fits w dest :=⟨extend (rank t live b e) lower,keyOK⟩
    simpa only [read,hop,HopLiteral.hop,e] using active

end Snapshots
end
end Hierarchy.DescentExteriorReplay

end OAI
