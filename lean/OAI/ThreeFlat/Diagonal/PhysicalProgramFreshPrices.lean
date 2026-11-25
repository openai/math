import OAI.ThreeFlat.Diagonal.PhysicalLevelCaps
import OAI.ThreeFlat.Diagonal.PhysicalShrinkLocalWork
import OAI.ThreeFlat.Diagonal.PhysicalRefreshLocalPrices
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly

namespace OAI
/-! # A fresh-resource certificate for each history of any supported program -/

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] [Fintype F] {d l : ℕ} {A : State d l}

namespace Program
open private boundedSiteCharge from OAI.ThreeFlat.Diagonal.PhysicalRunCharges
attribute [local irreducible] shrinkBinary refreshBinary shrinkBinaryCharge refreshBinaryCharge recast recastMove
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

omit [Fintype F] in
/-- The certified shrink scan retains the elected charge row and recurses on its selected successor. -/
theorem certified_shrink_step (s t : ℕ) (T : ShrinkMotif.Table F)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t≤1/1024)
    (tail : Program F t) (factor : ℕ)
    (bounded : ∀ a∈(Program.shrink s t T small tail).factors, a ≤ factor)
    (rem : ℕ) (A : State (2^s) ((Program.shrink s t T small tail).charge+rem)) :
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let X : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let pos := Nat.two_pow_pos t
    let size : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
    let R := shrinkBinary T s (2^t) (tail.charge+rem) pos size X
    let kids := fun i => tail.run rem (R.next i)
    let head := boundedSiteCharge R (shrinkBinaryCharge T s (2^t) (tail.charge+rem) pos size X)
      (shrinkChargeFactor s) (bounded _ List.mem_cons_self)
      (shrinkBinaryCharge_sum T s (2^t) (tail.charge+rem) pos size X)
    (Program.shrink s t T small tail).certifiedCharges factor bounded rem A =
      certRecast e A (.step R kids) (consCert R kids head
        (fun i => tail.certifiedCharges factor (fun a ha => bounded a (List.mem_cons_of_mem _ ha)) rem (R.next i))) :=
  rfl

omit [Fintype F] in
/-- The certified refresh scan transports its actual local charge through the successor-degree equality. -/
theorem certified_refresh_step (s t h pad : ℕ) (c : Fin (2^s)→Fin (2^s)→ℕ) (γ C : ℝ)
    (T : RefreshMotif.Table F c (1+h+pad) C) (hm : 2≤2^s) (hh : 0<h)
    (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h) (zero : ∀ i,c i i=0)
    (conn : Expander.Bound (Expander.transition c h) ℝ γ) (degree : 1+h+pad=2^t)
    (tail : Program F t) (factor : ℕ)
    (bounded : ∀ a∈(Program.refresh s t h pad c γ C T hm hh sym rows zero conn degree tail).factors, a ≤ factor)
    (rem : ℕ) (A : State (2^s) ((Program.refresh s t h pad c γ C T hm hh sym rows zero conn degree tail).charge+rem)) :
    let e := Nat.add_assoc s tail.charge rem
    let X : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T X hm hh sym rows zero conn
    let Q := recastMove degree R
    let kids := fun i => tail.run rem (Q.next i)
    let fresh := boundedSiteCharge R (refreshBinaryCharge T X hm hh sym rows zero conn)
      (2*2^s+2) (bounded _ List.mem_cons_self) (refreshBinaryCharge_sum T X hm hh sym rows zero conn)
    (Program.refresh s t h pad c γ C T hm hh sym rows zero conn degree tail).certifiedCharges factor bounded rem A =
      certRecast e A (.step Q kids) (consCert Q kids (siteRecast degree R fresh)
        (fun i => tail.certifiedCharges factor (fun a ha => bounded a (List.mem_cons_of_mem _ ha)) rem (Q.next i))) :=
  rfl

end Program

omit [Fintype F] in
private theorem level_now (r : Run F A) (h : r.plan.History) (C : r.Charges) (prev : A.Site→ℕ)
    {V : ℕ} (room : r.LevelsCapped 1 V h C prev) (x : A.Site) : prev x≤V := by
  cases r with
  | done=>simpa using room x
  | step R next=>simpa using room.1 x

private def EveryHistory (K V : ℕ) (r : Run F A) (J : r.Assembler Pins) (C : r.Charges) :=
  ∀ h : r.plan.History, ∀ prev : A.Site→ℕ, r.LevelsCapped 1 V h C prev → r.FreshPath K h J.steps C prev

omit [Fintype F] in
private theorem every_recast {l' K V factor : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    (J : r.Assembler Pins) (C : Program.Certified r factor) (valid : EveryHistory K V r J C.val) :
    EveryHistory K V (Program.recast e A r) (Run.inputAssembler e A r J) (Program.certRecast e A r C).val := by
  cases e
  exact valid

omit [Fintype F] in
private theorem every_step {D n factor K V : ℕ} (R : Move F A D n)
    (kids : ∀ i, Run F (R.next i)) (Jhead : R.Assembler Pins)
    (Jtail : ∀ i,(kids i).Assembler Pins) (head : Program.siteCharge R factor)
    (tail : ∀ i,Program.Certified (kids i) factor)
    (headPaid : ∀ (i : Fin R.rules.count) (L : A.Words Pins), A.OrderedHalves L →
      ∀ prev : A.Site → ℕ, (∀ y,1+A.incidentWidth y ≤ prev y) →
      ∀ x : (R.next i).Site, R.push i (head.val i) prev x ≤ V →
        (Jhead L i).stage.freshResources (Move.WordStep.targetSite (R:=R) (i:=i) x) ≤
          K * R.push i (head.val i) prev x)
    (kidsPaid : ∀ i,EveryHistory K V (kids i) (Jtail i) (tail i).val) :
    EveryHistory K V (.step R kids) (Run.assembleStep R kids Jhead Jtail)
      (Program.consCert R kids head tail).val := by
  intro h prev room
  let branch := h.1
  let rest := Run.tailHistory R kids h
  let nextWork := R.push branch (head.val branch) prev
  have nextRoom : (kids branch).LevelsCapped 1 V rest (tail branch).val nextWork := room.2
  refine ⟨?_,kidsPaid branch rest nextWork nextRoom⟩
  intro L ord previous x
  exact headPaid branch L ord prev previous x (level_now (kids branch) rest (tail branch).val nextWork nextRoom x)

variable (B : Block F) (u : ℕ)
local notation "W" => 16*u^10
local notation "V" => 2^(u^10)
local notation "K" => B.localCoefficient*(W+1)^3

private theorem word_fits_height : V*max 1 V≤2^W := by
  rw [max_eq_right (Nat.one_le_two_pow)]
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

omit [Fintype F] in
private theorem head_le_push {d l D n : ℕ} {A : State d l} (M : Move F A D n)
    (j : Fin M.rules.count) (head : (M.next j).Site → ℕ) (prev : A.Site → ℕ)
    (x : (M.next j).Site) : head x ≤ M.push j head prev x := Nat.le_add_right ..

section
attribute [local irreducible] shrinkBinary shrinkBinary_assembler shrinkBinaryCharge
  refreshBinary refreshBinary_assembler refreshBinaryCharge Program.recastMove
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

omit [Fintype F] in
theorem Block.program_fresh_path {s : ℕ} (P : Program F s) (supported : P.SupportedBy B.publicTemplate)
    (factor : ℕ) (bounded : ∀ x∈P.factors,x≤factor) (rem : ℕ)
    (A : State (2^s) (P.charge+rem))
    (smallTiles : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤V)
    (largeTiles : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤V)
    (h : (P.run rem A).plan.History) (prev : A.Site→ℕ)
    (room : (P.run rem A).LevelsCapped 1 V h (P.certifiedCharges factor bounded rem A).val prev) :
    (P.run rem A).FreshPath K h ((P.assembly rem A : (P.run rem A).Assembler Pins).steps)
      (P.certifiedCharges factor bounded rem A).val prev := by
  suffices all : EveryHistory K V (P.run rem A) (P.assembly rem A : (P.run rem A).Assembler Pins)
      (P.certifiedCharges factor bounded rem A).val from all h prev room
  clear room prev h
  induction P with
  | done s=>intro h prev room;trivial
  | shrink s t T small tail ih=>
    obtain ⟨i,hs,hD,hT⟩:=B.public_shrink supported.1
    have ht : t=B.exponent (i.val+1):=by
      by_contra no
      rcases lt_or_gt_of_ne no with left|right
      · exact (Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide : 1<2) left)) hD
      · exact (Nat.ne_of_gt (Nat.pow_lt_pow_right (by decide : 1<2) right)) hD
    subst s
    subst t
    subst T
    let e:=Nat.add_assoc (shrinkCharge (B.exponent i.val)) tail.charge rem
    let X : State (2^B.exponent i.val) (shrinkCharge (B.exponent i.val)+(tail.charge+rem)):=e ▸ A
    let positive:=Nat.two_pow_pos (B.exponent (i.val+1))
    let M:=shrinkBinary B.shrink (B.exponent i.val) (2^B.exponent (i.val+1)) (tail.charge+rem)
      positive (by exact_mod_cast small) X
    let kids:=fun j=>tail.run rem (M.next j)
    let issued := shrinkBinaryCharge B.shrink (B.exponent i.val) (2^B.exponent (i.val+1))
      (tail.charge+rem) positive (by exact_mod_cast small) X
    let head : Program.siteCharge M factor := ⟨issued,fun j =>
      (shrinkBinaryCharge_sum B.shrink (B.exponent i.val) (2^B.exponent (i.val+1))
        (tail.charge+rem) positive (by exact_mod_cast small) X j).trans
          (Nat.mul_le_mul_right _ (bounded _ List.mem_cons_self))⟩
    let headAssembly := shrinkBinary_assembler (Pins:=Pins) B.shrink (B.exponent i.val)
      (2^B.exponent (i.val+1)) (tail.charge+rem) positive (by exact_mod_cast small) X
    have tailBound (z : ℕ) (hz : z ∈ tail.factors) : z ≤ factor :=
      bounded z (List.mem_cons_of_mem _ hz)
    let nextAssembly (j : Fin M.rules.count) : (kids j).Assembler Pins := tail.assembly rem (M.next j)
    let nextCharge (j : Fin M.rules.count) : Program.Certified (kids j) factor :=
      tail.certifiedCharges factor tailBound rem (M.next j)
    simp only [Program.assembly_shrink_step, Program.certified_shrink_step]
    refine every_recast e A (.step M kids) (Run.assembleStep M kids headAssembly nextAssembly)
      (Program.consCert M kids head nextCharge) ?_
    apply every_step (Pins:=Pins) M kids headAssembly nextAssembly head nextCharge
    · intro vote L _ordered prev previous x peak
      exact B.shrink_fresh_to_push i W V smallTiles (word_fits_height u) (tail.charge+rem) positive
        (by exact_mod_cast small) X L vote prev previous x ((head_le_push M vote _ prev x).trans peak)
    · intro vote
      exact ih supported.2 tailBound (M.next vote)
  | refresh s t hgt pad c γ scalar T hm hh sym rows zero conn degree tail ih=>
    let e:=Nat.add_assoc s tail.charge rem
    let X : State (2^s) (s+(tail.charge+rem)):=e ▸ A
    let M:=refreshBinary T X hm hh sym rows zero conn
    let M':=Program.recastMove degree M
    let kids:=fun j=>tail.run rem (M'.next j)
    have tailBound (z : ℕ) (hz : z ∈ tail.factors) : z ≤ factor :=
      bounded z (List.mem_cons_of_mem _ hz)
    have fund (j : Fin M.rules.count) :=
      (refreshBinaryCharge_sum T X hm hh sym rows zero conn j).trans
        (Nat.mul_le_mul_right _ (bounded _ List.mem_cons_self))
    let fresh : Program.siteCharge M factor := ⟨refreshBinaryCharge T X hm hh sym rows zero conn, fund⟩
    let charge := Program.siteRecast degree M fresh
    let step := Move.outputAssembler degree M
      (refreshBinary_assembler (Pins := Pins) T X hm hh sym rows zero conn)
    let nextAssembly (j : Fin M'.rules.count) : (kids j).Assembler Pins :=
      tail.assembly rem (M'.next j)
    let nextCharge (j : Fin M'.rules.count) : Program.Certified (kids j) factor :=
      tail.certifiedCharges factor tailBound rem (M'.next j)
    simp only [Program.assembly_refresh_step, Program.certified_refresh_step]
    refine every_recast e A (.step M' kids) (Run.assembleStep M' kids step nextAssembly)
      (Program.consCert M' kids charge nextCharge) ?_
    apply every_step (Pins := Pins) M' kids step nextAssembly charge nextCharge
    · intro j L _ prev previous x peak
      exact B.public_refresh_fresh T hm hh sym rows zero conn X (B.public_refresh supported.1)
        degree fund L j u prev previous largeTiles x peak
    · intro j
      exact ih supported.2 tailBound (M'.next j)


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
