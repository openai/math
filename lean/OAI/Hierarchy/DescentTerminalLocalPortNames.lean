import OAI.Hierarchy.DescentTerminalIssuedBook

namespace OAI
/-! # Readback from true chronological bundle lists in the local port record -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalRouteRows Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {G V M A a W q : ℕ}

variable (t : Site) (f : Room t G V M A) (cables : t.Name→Word a) (args : t.Arg→Word a)
local notation "book" => issue t f cables args
def ports : t.Name ≃ (book).Port := Equiv.sigmaCongrRight (fun i=>finCongr (size_live t f cables args i).symm)
def operands : t.Arg ≃ (book).Operand := Equiv.sigmaCongrRight (fun i=>finCongr (arity_live t f cables args i).symm)

theorem port_read (i : t.Name) : (book).tag (ports t f cables args i)=cables i := by
  rcases i with ⟨g,j⟩
  unfold Book.tag
  dsimp only [issue]
  split
  · split
    · rfl
    · rename_i h
      exact (h j.isLt).elim
  · rename_i h
    exact (h g.isLt).elim
theorem operand_read (i : t.Arg) : (book).ref (operands t f cables args i)=args i := by
  rcases i with ⟨v,j⟩
  unfold Book.ref
  dsimp only [issue]
  split
  · split
    · rfl
    · rename_i h
      exact (h j.isLt).elim
  · rename_i h
    exact (h v.isLt).elim

def coord {r q : ℕ} (p : Fin r×Fin q) : ℕ×ℕ := (p.1.val,p.2.val)
theorem coord_inj {r q : ℕ} : Function.Injective (@coord r q) := by
  intro j k same
  exact Prod.ext (Fin.ext <|congrArg Prod.fst same) (Fin.ext <|congrArg Prod.snd same)

theorem port_coordinate (pos : 0<q) (i : t.Name) : (book).portCoord q (ports t f cables args i)=coord (Site.source pos i) := by
  have counts : (fun g:Fin t.groups=>poolBatchCount ((book).size g) q)=t.chunks q :=
    funext (fun g=>congrArg (poolBatchCount · q) (size_live t f cables args g))
  exact congrArg (fun sizes : Fin t.groups → ℕ =>
    (ProtocolRAMPortRanks.prefix sizes Fin.val i.1 + i.2.val/q,i.2.val%q)) counts

theorem arg_coordinate (pos : 0<q) (i : t.Arg) : (book).argCoord q (operands t f cables args i)=coord (Site.target pos i) := by
  have how : (book).arity=t.arity :=funext (arity_live t f cables args)
  have sum : (∑g:Fin t.groups,poolBatchCount ((book).size g) q)=t.portRows q :=
    Finset.sum_congr rfl (fun g _=>congrArg (poolBatchCount · q) (size_live t f cables args g))
  exact congrArg₂ (fun base (widths : Fin t.nodes → ℕ) =>
    (base+(first q widths i.1+i.2.val)/q,(first q widths i.1+i.2.val)%q)) sum how

theorem live_port (pos : 0<q) (r : ℕ) (s : Fin q) (token : Word a) :
    (book).row q r 0 s=some token ↔ ∃i : t.Name,coord (Site.source pos i)=(r,s.val) ∧ cables i=token := by
  have geom:=port_coordinate t f cables args pos
  have inj:Function.Injective ((book).portCoord q):=by
    intro j k eqn
    obtain ⟨j,rfl⟩:=(ports t f cables args).surjective j
    obtain ⟨k,rfl⟩:=(ports t f cables args).surjective k
    exact congrArg _ (Site.source_unique pos (coord_inj ((geom j).symm.trans (eqn.trans (geom k)))))
  rw [Book.row,ite_eq_left (show (0 : Fin 2).val = 0 by decide),Book.at_iff _ _ inj]
  constructor
  · rintro ⟨i,h,h₁⟩;obtain ⟨j,rfl⟩:=(ports t f cables args).surjective i
    exact ⟨j,(geom j).symm.trans h,(port_read t f cables args j).symm.trans h₁⟩
  · rintro ⟨j,h,h₁⟩;exact ⟨_,(geom j).trans h,(port_read t f cables args j).trans h₁⟩

theorem live_arg (pos : 0<q) (r : ℕ) (s : Fin q) (token : Word a) :
    (book).row q r 1 s=some token ↔ ∃i : t.Arg,coord (Site.target pos i)=(r,s.val) ∧ args i=token := by
  have geom:=arg_coordinate t f cables args pos
  have inj:Function.Injective ((book).argCoord q):=by
    intro j k eqn
    obtain ⟨j,rfl⟩:=(operands t f cables args).surjective j
    obtain ⟨k,rfl⟩:=(operands t f cables args).surjective k
    exact congrArg _ (Site.target_unique pos (coord_inj ((geom j).symm.trans (eqn.trans (geom k)))))
  rw [Book.row,ite_eq_right (by decide),Book.at_iff _ _ inj]
  constructor
  · rintro ⟨i,h,h₁⟩;obtain ⟨j,rfl⟩:=(operands t f cables args).surjective i
    exact ⟨j,(geom j).symm.trans h,(operand_read t f cables args j).symm.trans h₁⟩
  · rintro ⟨j,h,h₁⟩;exact ⟨_,(geom j).trans h,(operand_read t f cables args j).trans h₁⟩

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
