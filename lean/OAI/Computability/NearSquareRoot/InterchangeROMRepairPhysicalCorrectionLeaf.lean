import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionPacket

/-! # Compiled correction leaf on an ordinary repair packet -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Correction

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters GeneratorSyntax InterchangeROMTable InterchangeROM

variable {D A X : Type} [Fintype D] [DecidableEq D] {s p w m : ℕ} {P : A → Type}

def leaf (emit : Cmd) (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) : Cmd :=
  if ii.isEmpty then .pass
  else (prependMask emit).join (underHeader (widenHead.join (kernel p s m t oi ii)))

theorem leaf_within {R : ℕ} (hR : 4 ≤ R) {emit : Cmd} (he : Within R emit)
    (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) : Within R (leaf emit p s m t oi ii) := by
  unfold leaf
  split_ifs
  · trivial
  · exact ⟨prependMask_within hR he,underHeader_within (by omega)
      ⟨RegisterSelect.within_mono hR _ widenHead_within,RegisterSelect.within_mono hR _ (kernel_within ..)⟩⟩

theorem effective_prependMask [Primcodable X] {emit : X → Cmd} (h : Effective ltr emit) :
    Effective ltr (fun x => prependMask (emit x)) :=
  (computable_nodeFile.comp ((effective_const ltr (clone 0 1 2)).join
    (h.join (effective_const ltr ((pack 0).join ((move 1 0 2).join (pack 0))))))).of_eq
      (fun _ => nodeFile_file _)

set_option maxHeartbeats 900000 in
theorem effective_leaf [Primcodable X] {emit : X → Cmd} {p s m : X → ℕ} {t : X → Raw.Tape}
    {oi ii : X → List CheckIndex} (he : Effective ltr emit) (hp : Computable p)
    (hs : Computable s) (hm : Computable m) (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Effective ltr fun x => leaf (emit x) (p x) (s x) (m x) (t x) (oi x) (ii x) := by
  have active := (effective_prependMask he).join (effective_underHeader
    ((effective_const ltr widenHead).join (effective_kernel hp hs hm ht ho hi)))
  have test := Primrec.eq.decide.to_comp.comp (Computable.list_length.comp hi) (Computable.const 0)
  exact (Computable.cond test (Computable.const (file ltr .pass)) active).of_eq (by
    intro x
    cases h : ii x <;> simp [leaf,h])

private theorem underHeader_fits_at (h input output : Tree) (c : Cmd) (t : ℕ) (env : Env) (d : Deck)
    (run : Fits env c (pile 0 input (pile 1 h d)) (pile 0 output (pile 1 h d)) t) :
    Fits env (underHeader c) (pile 0 (.fork h input) d) (pile 0 (.fork h output) d)
      (84*h.count+t+11) := by
  have start := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) h env (pile 0 input d)
  have finish := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) h env (pile 0 output d)
  rw [pile_comm 1 h d 0 _ (by decide)] at start finish
  exact (fits_pair (start.join (run.join (finish.join (fits_pack ..))))).mono (by omega)

def localClock (h bank narrow wide : Tree) (maskTime kernelTime : ℕ) : ℕ :=
  maskTime + kernelTime + 1200 * (h.count+bank.count+narrow.count+wide.count+1)

/-- The emitted packet has the original header followed by both corrected
check banks. The numerical address mask is generated once from the header. -/
theorem leaf_bounded (h : Tree) (emit : Cmd) (maskTime : ℕ) (t : Raw.Tape) (η : A → Fin m → Bool)
    (src dst : Series (D × Fin s)) (lane : D → ℕ) (inj : Function.Injective lane)
    (rows : Series A) (payload : (a : A) → Series (P a)) (width : ℕ) (hw : ∀ a, (payload a).count ≤ width)
    (v : Bool → D → (a : A) → P a → Fin s → ZMod (p+1)) (env : Env)
    (he : ∀ d b, DeckCap b d → Fits env emit (pile 0 h d)
      (pile 0 (stripe rows (fun a => numeral (Raw.mask (η a)).val)) d) maskTime)
    (deck : Deck) (base : ℕ) (hr : DeckCap base deck) :
    let ii := (twoBlocks src).tab (checkIndex lane)
    let oi := (twoBlocks dst).tab (checkIndex lane)
    let tag a := numeral (Raw.mask (η a)).val
    let out := correctValue (w:=w) t η v
    let xs := encodedBank src rows payload (v false) ++ encodedBank src rows payload (v true)
    let ys := encodedBank dst rows payload (out false) ++ encodedBank dst rows payload (out true)
    let cost := localClock h (Task.forest id xs) (stripe rows tag) (broadcast rows payload tag)
      maskTime (kernelFactor p s m t oi ii * (rows.count*(width+1)+1))
    BoundedFits env (leaf emit p s m t oi ii) (pile 0 (packet h xs) deck) (pile 0 (packet h ys) deck)
      cost (base+2*cost) cost := by
  intro ii oi tag out xs ys cost
  let bank := Task.forest id xs
  let n := stripe rows tag
  let wide := broadcast rows payload tag
  let T := kernelFactor p s m t oi ii * (rows.count*(width+1)+1)
  have hc : cost = maskTime+T+1200*(h.count+bank.count+n.count+wide.count+1) := rfl
  apply BoundedFits.of_fits (data := ?_) (ret := le_rfl)
  · cases hs : src.explore with
    | nil =>
      have hd : dst.explore = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro u _
        have no := src.complete u
        simp [hs] at no
      have ei : ii = [] := by simp [ii,Series.tab,twoBlocks,hs]
      have ex : xs = [] := by simp [xs,encodedBank,Series.tab,hs]
      have ey : ys = [] := by simp [ys,encodedBank,Series.tab,hd]
      rw [leaf,ei,ex,ey]
      exact (Fits.pass _).mono (by omega)
    | cons u us =>
      have ei : ii.isEmpty = false := by simp [ii,Series.tab,twoBlocks,hs]
      rw [leaf,ei]
      let head a j := numeral (v false u.1 a j u.2).val
      let top := stripe rows (fun a => stripe (payload a) (head a))
      let tail := (us.map fun z => encodedRow rows payload fun a j => v false z.1 a j z.2) ++
        encodedBank src rows payload (v true)
      have ex : xs = top::tail := by simp [xs,encodedBank,top,tail,head,Series.tab,hs,encodedRow]
      have eb : bank = Tree.fork top (Task.forest id tail) := by change Task.forest id xs = _; rw [ex]; rfl
      have topBound : top.count ≤ bank.count := by rw [eb]; change _ ≤ top.count + _ + 1; omega
      have pre := prependMask_fits h bank n emit env maskTime deck
        (he (pile 0 bank (pile 1 h deck)) _ ((hr.pile 1 h).pile 0 bank))
      have sc := widenHead_fits tag head rows payload (Task.forest id tail) env (pile 1 h deck)
      change Fits env widenHead (pile 0 (.fork n (.fork top (Task.forest id tail))) (pile 1 h deck))
        (pile 0 (.fork wide (.fork top (Task.forest id tail))) (pile 1 h deck))
        (700*(n.count+top.count+wide.count+1)) at sc
      rw [← eb] at sc
      have run := (kernel_bounded (w:=w) t η src dst lane inj rows payload width hw v env
        (pile 1 h deck) _ (hr.pile 1 h)).fits
      change Fits env (kernel p s m t oi ii) (pile 0 (.fork wide bank) (pile 1 h deck))
        (pile 0 (Task.forest id ys) (pile 1 h deck)) T at run
      have cmd := pre.join (underHeader_fits_at _ _ _ _ _ _ deck (sc.join run))
      exact cmd.mono (by omega)
  · intro i
    have hi := (hr.pile 0 (packet h xs)) i
    change (letters (pile 0 (packet h xs) deck) i).length + cost ≤ _
    change _ ≤ base+(h.count+bank.count+1) at hi
    omega

end InterchangeROMRepair.Physical.Correction

end NearSquareRoot
end Computability
end OAI
