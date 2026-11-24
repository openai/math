import OAI.Computability.VPVNP.CompressorRecordsDemandRoles

/-!
# Full scan of selected A, B, D and CD records

The scan follows each old outgoing slot. The first probe finds its opposite site,
and later probes follow its selected C and D positions. Old directory cells remain
readable throughout. Each row is written at its own permuted absolute arc ID.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Address and value of one output component. -/
def fieldAddr (p : Fin 11 → Word w) (i : Word w) (t : Fin 4) : ℕ :=
  let a := address p i
  ![a.val,(a+1).val,(a+1+1).val,(a+1+1+1).val] t

/-- Select a field from a demand record in storage order A, B, D, CD. -/
def Roles.field {α : Type} (r : Roles α) (t : Fin 4) : α := ![r.A,r.B,r.D,r.cd] t

/-- The address of each of the six reads needed for one demand record, including the three
placement reads at its ordered endpoints. -/
def inputAddr (p : Fin 11 → Word w) (m : Memory w) (i : Word w) (c : Fin 6) : ℕ :=
  let src := BundleRAM.sourceSite p i
  let dst := BundleRAM.targetSite p m i
  let ends := endpoints p m i
  ![(p 5+i).val,(p 6+src).val,(p 6+dst).val,(p 8+ends.1).val,(p 9+ends.1).val,(p 7+ends.2).val] c

/-- The output family can occupy any disjoint region of the external workspace. -/
structure Regions (p : Fin 11 → Word w) (old : Memory w) (N : ℕ) : Prop where
  fits : N ≤ 2^w
  unique : ∀ (i j : Word w) (t u : Fin 4), i.val<N → j.val<N →
    (fieldAddr p i t = fieldAddr p j u ↔ i=j ∧ t=u)
  input : ∀ (i j : Word w) (c : Fin 6) (t : Fin 4), i.val<N → j.val<N →
    inputAddr p old i c ≠ fieldAddr p j t

private theorem roles_same (p : Fin 11 → Word w) (old m : Memory w) (i : Word w)
    (hr : ∀ c : Fin 6, m (inputAddr p old i c) = old (inputAddr p old i c)) :
    roles p m i = roles p old i := by
  have hd : BundleRAM.targetSite p m i = BundleRAM.targetSite p old i :=
    congrArg (fun v => ShrinkRAM.div v (p 0)) (hr 0)
  have hs : m (p 6+BundleRAM.sourceSite p i).val = old (p 6+BundleRAM.sourceSite p i).val := hr 1
  have he : endpoints p m i = endpoints p old i := by simp only [endpoints,hd,hs]
  unfold roles
  dsimp only
  rw [he,hd,hs]
  rw [show m (p 8+(endpoints p old i).1).val = _ from hr 3,
    show m (p 9+(endpoints p old i).1).val = _ from hr 4,
    show m (p 7+(endpoints p old i).2).val = _ from hr 5,
    show m (p 6+BundleRAM.targetSite p old i).val = _ from hr 2]
  rfl

private theorem store_outside (p : Fin 11 → Word w) (m : Memory w) (i : Word w) (x : ℕ)
    (h : ∀ t, x ≠ fieldAddr p i t) : store p m i x = m x := by
  change (if x = fieldAddr p i 3 then _ else if x = fieldAddr p i 2 then _ else
    if x = fieldAddr p i 1 then _ else if x = fieldAddr p i 0 then _ else m x) = _
  simp [h]

private theorem store_field {p : Fin 11 → Word w} {old m : Memory w} {N : ℕ}
    (reg : Regions p old N) (i : Word w) (hi : i.val<N) (t : Fin 4) :
    store p m i (fieldAddr p i t) = (roles p m i).field t := by
  have eqv (u : Fin 4) : fieldAddr p i t = fieldAddr p i u ↔ t=u := by
    simp [reg.unique i i t u hi hi]
  change (if fieldAddr p i t = fieldAddr p i 3 then _ else
    if fieldAddr p i t = fieldAddr p i 2 then _ else
    if fieldAddr p i t = fieldAddr p i 1 then _ else
    if fieldAddr p i t = fieldAddr p i 0 then _ else _) = _
  simp only [eqv]
  fin_cases t <;> rfl

/-- The finished prefix contains precisely the rows for the visited source arcs. -/
structure Written (p : Fin 11 → Word w) (old m : Memory w) (k : ℕ) : Prop where
  row : ∀ (i : Word w) (t : Fin 4), i.val<k → m (fieldAddr p i t) = (roles p old i).field t
  frame : ∀ x : ℕ, (∀ (i : Word w) (t : Fin 4), i.val<k → x ≠ fieldAddr p i t) → m x = old x

theorem Written.start (p : Fin 11 → Word w) (m : Memory w) : Written p m m 0 :=
  ⟨fun _ _ h => False.elim (Nat.not_lt_zero _ h), fun _ _ => rfl⟩

private theorem Written.step {p : Fin 11 → Word w} {old m : Memory w} {N : ℕ} {i : Word w}
    (reg : Regions p old N) (hi : i.val<N) (h : Written p old m i.val) :
    Written p old (store p m i) (i.val+1) := by
  have hr : roles p m i = roles p old i := roles_same p old m i fun c =>
    h.frame _ fun j t hj => reg.input i j c t hi (hj.trans hi)
  constructor
  · intro j t hj
    by_cases he : j=i
    · subst j; rw [store_field reg i hi,hr]
    · rw [store_outside]
      · exact h.row j t (by have := Fin.val_ne_of_ne he; omega)
      · intro u hu; exact he ((reg.unique j i t u (by omega) hi).mp hu).1
  · intro x hx
    rw [store_outside p m i x (fun t => hx i t (by omega))]
    exact h.frame x (fun j t hj => hx j t (by omega))

/-- Sequential native execution with four exact output columns, all unrelated cells
framed, and ten probes per directed old port. -/
theorem scan_run {p : Fin 11 → Word w} {old m : Memory w} {N k n : ℕ}
    (reg : Regions p old N) (h : Written p old m k) (bound : k+n ≤ N) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 65 (some (ShrinkRAM.word w k)) m (List.replicate n []) = some rs ∧
      Written p old (after m (eventLog rs)) (k+n) ∧ rs.length = n ∧
      (∀ r ∈ rs, r.events.length = 64 ∧ countProbes r.events = 10) ∧
      RAMBuckets.cost Report.probes rs = 11*n := by
  let M := (template visit 0).instantiate w p
  induction n generalizing k m with
  | zero => exact ⟨[],rfl,h,rfl,by simp,rfl⟩
  | succ n ih =>
    let i := ShrinkRAM.word w k
    have hi : i.val=k := Nat.mod_eq_of_lt (by have := reg.fits; omega)
    have hr : Written p old (store p m i) (k+1) := hi ▸ Written.step reg (hi ▸ (by omega)) (hi ▸ h)
    obtain ⟨rs, he, hw, hl, hc, hcost⟩ := ih hr (by omega)
    let rep : Report w := ⟨events p m i, some (i+1)⟩
    have hnext : i+1 = ShrinkRAM.word w (k+1) := by
      change (k : Word w) + 1 = ((k+1 : ℕ) : Word w)
      simp
    have hmem : after m (eventLog (rep :: rs)) = after (store p m i) (eventLog rs) := by
      change after m (events p m i ++ eventLog rs) = _
      rw [show after m (events p m i ++ eventLog rs) = after (after m (events p m i)) (eventLog rs) from List.foldl_append,
        visit_after]
    refine ⟨rep :: rs, ?_, ?_, by simp [hl], ?_, ?_⟩
    · change runSegment M.program 65 (some i) m (List.replicate (n+1) []) = _
      rw [List.replicate_succ, runSegment, visit_native p m i]
      simp only [M,rep,visit_after,hnext,he,Option.map_some]
    · rw [hmem]; simpa [Nat.add_assoc,Nat.add_comm 1 n] using hw
    · intro r hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact visit_work p m i
      · exact hc r hx
    · change 1+countProbes (events p m i)+RAMBuckets.cost Report.probes rs = _
      rw [(visit_work p m i).2,hcost]; omega

end CompressorRecords.DemandRAM

end VPVNP
end Computability
end OAI
