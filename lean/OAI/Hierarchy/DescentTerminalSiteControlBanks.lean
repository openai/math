import OAI.Hierarchy.DescentTerminalControlValues
import OAI.Hierarchy.DescentTerminalControlProgram

namespace OAI
/-! # The eight primitive-header control banks acquired before computing the row spans -/
namespace Hierarchy.DescentTerminalControlProgram
open DescentTerminalLocalPortBook DescentTerminalRecipeRows DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
def layout (base S G V M A a verts W B : ℕ) : Plan :=
  ⟨base,S,Book.Bytes G V M A a,⟨verts,W,B⟩⟩
def earlyBanks (x : Plan) (parts : Book.Parts) : Fin 8→Bank :=
  ![x.ports,(parts 1).source,x.first,DescentTerminalControlROM.Shape.zero x.fixed,
    x.shape.bank x.fixed 0,x.shape.bank x.fixed 1,x.shape.bank x.fixed 2,x.shape.bank x.fixed 3]

theorem early_before (x : Plan) (parts : Book.Parts) (low : (parts 1).source.base+(parts 1).source.size ≤ x.base)
    (j : Fin 8) : (earlyBanks x parts j).base+(earlyBanks x parts j).size ≤ x.finish := by
  have p:=span_pos x.sites
  have q:=span_pos x.codeWords
  have h:=span_pos x.shape.limit
  have paid : ∀f : Fin 4,(x.shape.bank x.fixed f).base+(x.shape.bank x.fixed f).size ≤ x.finish := by
    intro f
    change x.fixed+1+f.val*x.shape.pitch+x.shape.pitch ≤ x.fixed+(1+4*x.shape.pitch)
    have hi:=Nat.mul_le_mul_right x.shape.pitch f.isLt
    rw [Nat.succ_mul] at hi
    omega
  fin_cases j
  · change x.base+span x.codeWords+span x.sites≤
      x.base+span x.codeWords+span x.sites+span x.sites+x.shape.size
    omega
  · exact low.trans (by change x.base ≤ x.base+_+_+_+_;omega)
  · change x.base+span x.codeWords+span x.sites+span x.sites≤
      x.base+span x.codeWords+span x.sites+span x.sites+x.shape.size
    omega
  · change x.fixed+1 ≤ x.fixed+(1+4*x.shape.pitch)
    omega
  · exact paid 0
  · exact paid 1
  · exact paid 2
  · exact paid 3

structure Reads {w S : ℕ} (q W B V : ℕ) (site : Fin S→Site) (bank : Fin 8→Bank) (m : Memory w) : Prop where
  ports : ∀i,(bank 0).read m (i.val:Word w)=((site i).portRows q:Word w)
  nodes : ∀i,(bank 1).read m (i.val:Word w)=((site i).nodes:Word w)
  first : ∀i : Fin S,(bank 2).read m (i.val:Word w)=(i.val:Word w)
  skip : ∀i : Fin S,(bank 3).read m (i.val:Word w)=0
  countROM : ∀j : Fin (V+1),(bank 4).read m (j.val:Word w)=((j.val*((W+1)*(B*(2^B*2^B))):ℕ):Word w)
  modeROM : ∀j : Fin (W+1),(bank 5).read m (j.val:Word w)=((j.val*(B*(2^B*2^B)):ℕ):Word w)
  skipROM : ∀j : Fin B,(bank 6).read m (j.val:Word w)=((j.val*(2^B*2^B):ℕ):Word w)
  wordROM : ∀j : Word B,(bank 7).read m (j.val:Word w)=((j.val*2^B:ℕ):Word w)

variable {S G V M A a verts W B q w : ℕ}
theorem acquire (base : ℕ) (parts : Book.Parts) (sites : Fin S→Site) (f : ∀i,Room (sites i) G V M A)
    (names : ∀i,(sites i).Name→Word a) (args : ∀i,(sites i).Arg→Word a) (m : Memory w)
    (safe : (Book.expression parts).Fits w base) (nodeEarly : (parts 1).source.Fits w base)
    (issued : Book.Issued parts (fun i=>issue (sites i) (f i) (names i) (args i)) m)
    (space : (layout base S G V M A a verts W B).finish<2^w) :
    let x:=layout base S G V M A a verts W B
    let val:=portTable (G:=G) (V:=V) (M:=M) (A:=A) (a:=a) q
    let e:=Book.expression parts
    let out:=x.after val e m
    (x.program w val e).Exec m out (x.time e) ∧ CheapCode (x.program w val e) ∧
      Reads q W B verts sites (earlyBanks x parts) out ∧ ∀j,j < base ∨ x.finish ≤ j→ out j=m j := by
  intro x val e out
  let bk:=fun i=>issue (sites i) (f i) (names i) (args i)
  obtain ⟨go,cheap,ports,identity,blank,rom,kept⟩:=
    x.run m val e (fun i=>(bk i).bytes) safe (Book.numeric parts bk m issued) space
  refine ⟨go,cheap,⟨?_,?_,identity,fun i=>blank _,?_,?_,?_,?_⟩,kept⟩
  · intro i
    exact (ports i).trans (congrArg (fun n : ℕ=>(n:Word w)) ((portTable_at (q:=q) (bk i)).trans
      (actual_ports (sites i) (f i) (names i) (args i))))
  · intro i
    have prior : (parts 1).source.read out (i.val:Word w)=(parts 1).source.read m (i.val:Word w) := by
      apply kept
      exact .inl ((Nat.add_lt_add_left (Nat.mod_lt _ nodeEarly.1) _).trans_le nodeEarly.2.2)
    exact prior.trans (nodes_value parts m sites f names args issued i)
  · intro j
    exact rom 0 j.val j.isLt
  · intro j
    exact rom 1 j.val j.isLt
  · intro j
    exact rom 2 j.val j.isLt
  · intro j
    exact rom 3 j.val j.isLt

theorem Reads.transfer {sites : Fin S→Site} {banks : Fin 8→Bank} {m n : Memory w}
    (old : Reads q W B V sites banks m) (eqn : ∀j r,(banks j).read n r=(banks j).read m r) :
    Reads q W B V sites banks n :=
  ⟨fun i=>(eqn 0 _).trans (old.ports i),fun i=>(eqn 1 _).trans (old.nodes i),
    fun i=>(eqn 2 _).trans (old.first i),fun i=>(eqn 3 _).trans (old.skip i),
    fun j=>(eqn 4 _).trans (old.countROM j),fun j=>(eqn 5 _).trans (old.modeROM j),
    fun j=>(eqn 6 _).trans (old.skipROM j),fun j=>(eqn 7 _).trans (old.wordROM j)⟩

end
end Hierarchy.DescentTerminalControlProgram

end OAI
