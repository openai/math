import OAI.Computability.BorderVNP.DiagonalTallyOperandExprProof
import OAI.Computability.BorderVNP.DiagonalTallyRAMTrace

/-! # Writing native operand and reference arrays for each compact report block -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open VPVNP.BurstRAM RoutingISA DiagonalTallyPacketEmit

/-- Read the actual marked count for a unary bundle or the two fixed count dimensions,
and install the first of the two array loops. -/
def start (k : Kind) : Code := .seq (match k with
  | .count => .block [.copy 14 10,.binary .mul 13 10 11]
  | .unary => .block [.load 14 20,.binary .mul 14 14 21,.copy 13 14])
  (.block [.constant 40 0,.copy 41 13,.copy 42 31,.constant 43 1])

/-- Each row occupies five words in the operand array. -/
def next : Code := .block [.constant 40 0,.constant 46 5,.binary .mul 41 46 14,.copy 42 30,.constant 43 1]

/-- Advance the four cursors for the following cell or bundle. -/
def finish : Code := .block [.constant 46 5,.binary .mul 46 46 14,.binary .add 30 30 46,
  .binary .add 31 31 13,.binary .add 32 32 14,.binary .add 22 22 13]

/-- The two arrays are generated through scalar stores at the owner's current cursors. -/
def writer (k : Kind) : Code := .block [start k,array (refExpr k),next,array (fieldExpr k),finish]

/-- Physical state after the reference words followed by all five-word descriptors. -/
def Frame.image (f : Frame) (k : Kind) (m : ℕ → ℕ) : ℕ → ℕ :=
  written f.descriptors (f.field k) (written f.refs (f.refValue k) m (f.nrefs k)) (5*f.nrows k)

/-- Only a unary block consumes the dynamically decoded mark count. -/
def Frame.countAt (f : Frame) (k : Kind) (m : ℕ → ℕ) : Prop :=
  match k with | .count => True | .unary => m f.side=f.marked

/-- Native upper bound, including every expression and all loop guard ticks. -/
def Frame.cost (f : Frame) (k : Kind) : ℕ := (start k).slots+
  (f.nrefs k*((refExpr k).slots+save.slots+1)+1)+next.slots+
  (5*f.nrows k*((fieldExpr k).slots+save.slots+1)+1)+finish.slots

private theorem loaded_congr (f : Frame) (r t : Reg → ℕ) (h : f.Loaded r)
    (eq : ∀ j : Reg, j.val<40 → j≠13 → j≠14 → t j=r j) : f.Loaded t := by
  obtain ⟨a,b,c,d,e,g,i,l,n,p⟩ := h
  constructor <;> first | exact (eq _ (by decide) (by decide) (by decide)).trans a
                        | exact (eq _ (by decide) (by decide) (by decide)).trans b
                        | exact (eq _ (by decide) (by decide) (by decide)).trans c
                        | exact (eq _ (by decide) (by decide) (by decide)).trans d
                        | exact (eq _ (by decide) (by decide) (by decide)).trans e
                        | exact (eq _ (by decide) (by decide) (by decide)).trans g
                        | exact (eq _ (by decide) (by decide) (by decide)).trans i
                        | exact (eq _ (by decide) (by decide) (by decide)).trans l
                        | exact (eq _ (by decide) (by decide) (by decide)).trans n
                        | exact (eq _ (by decide) (by decide) (by decide)).trans p

private def ready (r : Reg → ℕ) (dst len : ℕ) : Prop := r 40=0 ∧ r 41=len ∧ r 42=dst ∧ r 43=1

private theorem start_ok (f : Frame) (k : Kind) (w : ℕ) (fit : f.Fits k w)
    (pub : Arg → ℕ) (m : ℕ → ℕ) (r : Reg → ℕ) (h : f.Loaded r) (header : f.countAt k m) :
    (start k).safeReadOnly w pub m r ∧
      let t := (start k).evalNat pub m r
      ready t f.refs (f.nrefs k) ∧ t 13=f.nrefs k ∧ t 14=f.nrows k := by
  obtain ⟨_,g,width,_,side,b,_,_,refs,_⟩ := h
  have small := fit.small
  have hw : w≠0 := by rintro rfl; simp at small
  have re := fit.refsEnd
  cases k <;> simp_all [start,ready,Frame.nrefs,Frame.nrows,Frame.countAt,Code.block,Code.safeReadOnly,
    Code.evalNat,Function.update,addressOpFits,addressOp] <;> omega

/-- Both count and unary loops operate on the actual dynamic marked count and write
the exact numerical pointer tables subsequently consumed by materialization. -/
theorem writer_runs {w : ℕ} (f : Frame) (k : Kind) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (h : f.Loaded (readings s)) (fit : f.Fits k w)
    (header : f.countAt k (readings m)) :
    ∃ es t mt, Runs pub mac (writer k) s m es t mt ∧ traceCost es ≤ f.cost k ∧
      readings mt=f.image k (readings m) ∧
      (t 22).val=f.external+f.nrefs k ∧ (t 30).val=f.descriptors+5*f.nrows k ∧
      (t 31).val=f.refs+f.nrefs k ∧ (t 32).val=f.prior+f.nrows k := by
  obtain ⟨safe,st⟩ := start_ok f k w fit (readings pub) (readings m) (readings s) h header
  obtain ⟨a,t₁,r₁,c₁,e₁⟩ := (start k).runReadOnly pub mac m s safe
  rw [← e₁] at st
  obtain ⟨⟨i₁,n₁,d₁,u₁⟩,x₁,y₁⟩ := st
  have l₁ := loaded_congr f _ _ h (fun j hj hn ho => congrArg Fin.val (r₁.keepsReg (by
    have keep : ∀ mode : Kind, ∀ q : Reg, q.val<40 → q≠13 → q≠14 → (start mode).keeps q=true := by intro mode; cases mode <;> decide
    exact keep k j hj hn ho)))
  obtain ⟨b,t₂,m₂,r₂,c₂,e₂,low₂⟩ := array_runs pub mac t₁ m (refExpr k) (f.refValue k)
    f.refs (f.nrefs k) (by cases k <;> decide) i₁ n₁ d₁ u₁ fit.refsEnd (fun i hi z lo idx unit =>
      refExpr_correct f k fit _ z i hi (loaded_congr f _ _ l₁ fun j hj _ _ => lo j hj) idx unit)
  have l₂ := loaded_congr f _ _ l₁ (fun j hj _ _ => congrArg Fin.val (low₂ j hj))
  have x₂ := (congrArg Fin.val (low₂ 13 (by decide))).trans x₁
  have y₂ := (congrArg Fin.val (low₂ 14 (by decide))).trans y₁
  have hsmall := fit.small
  have hw : w≠0 := by rintro rfl; simp at hsmall
  have dr := fit.descEnd
  have safe₃ : next.safeReadOnly w (readings pub) (readings m₂) (readings t₂) := by
    simp [next,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,readings,hw,y₂]
    omega
  obtain ⟨c,t₃,r₃,c₃,e₃⟩ := next.runReadOnly pub mac m₂ t₂ safe₃
  have d₂ := l₂.descriptors
  have st₃ : ready (readings t₃) f.descriptors (5*f.nrows k) := by
    rw [e₃]
    simp [next,ready,Code.block,Code.evalNat,Function.update,addressOp,d₂,y₂,readings] at *
  have l₃ := loaded_congr f _ _ l₂ (fun j hj _ _ => congrArg Fin.val (r₃.keepsReg (by
    have keep : ∀ q : Reg, q.val<40 → next.keeps q=true := by decide
    exact keep j hj)))
  obtain ⟨i₃,n₃,d₃,u₃⟩ := st₃
  obtain ⟨e,t₄,m₄,r₄,c₄,e₄,low₄⟩ := array_runs pub mac t₃ m₂ (fieldExpr k) (f.field k)
    f.descriptors (5*f.nrows k) (by cases k <;> decide) i₃ n₃ d₃ u₃ fit.descEnd (fun i hi z lo idx unit =>
      fieldExpr_correct f k fit _ z i hi (loaded_congr f _ _ l₃ fun j hj _ _ => lo j hj) idx unit)
  have l₄ := loaded_congr f _ _ l₃ (fun j hj _ _ => congrArg Fin.val (low₄ j hj))
  have x₄ : (t₄ 13).val=f.nrefs k := (congrArg Fin.val ((low₄ 13 (by decide)).trans
    (r₃.keepsReg (by decide)))).trans x₂
  have y₄ : (t₄ 14).val=f.nrows k := (congrArg Fin.val ((low₄ 14 (by decide)).trans
    (r₃.keepsReg (by decide)))).trans y₂
  obtain ⟨_,_,_,_,_,_,ext₄,desc₄,refs₄,prior₄⟩ := l₄
  change (t₄ 22).val=f.external at ext₄
  change (t₄ 30).val=f.descriptors at desc₄
  change (t₄ 31).val=f.refs at refs₄
  change (t₄ 32).val=f.prior at prior₄
  have safe₅ : finish.safeReadOnly w (readings pub) (readings m₄) (readings t₄) := by
    have ext := fit.externalEnd
    have ref := fit.refsEnd
    have count := fit.countEnd
    simp [finish,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
      readings,x₄,y₄,ext₄,desc₄,refs₄,prior₄]
    omega
  obtain ⟨g,t,r₅,c₅,e₅⟩ := finish.runReadOnly pub mac m₄ t₄ safe₅
  refine ⟨_,t,m₄,r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅))),?_,?_,?_⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+(traceCost c+(traceCost e+traceCost g))) ≤ _
    unfold Frame.cost
    omega
  · rw [e₄,e₂,Frame.image]
  · change readings t 22=_ ∧ readings t 30=_ ∧ readings t 31=_ ∧ readings t 32=_
    rw [e₅]
    simp [finish,Code.block,Code.evalNat,Function.update,addressOp,readings,x₄,y₄,ext₄,desc₄,refs₄,prior₄]

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
