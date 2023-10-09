/-
LAC (COMP2012)

definition of DFAs

-/
import data.fintype.basic
import tactic.derive_fintype
import .languages

section dfa
variable {Sigma : Type}
-- different to the notes we say that Σ is a parameter

-- We define dfas as a record, 
-- I am currently omitting some type classes.
structure dfa(Sigma : Type*) :=
  (Q : Type*)
  [finQ : fintype Q]
  --[decQ : decidable_eq Q]
  (δ : Q → Sigma → Q)
  (init : Q)
  (final : Q → Prop)
  --[decF : decidable_pred final] 


open dfa

-- this is the δ^ function 
def dfa_δ_star (A : dfa Sigma) : A.Q → word Sigma → A.Q
| q [] := q
| q (x :: w) := dfa_δ_star (A.δ q x) w

-- the definition of the language of a dfa
def dfa_lang (A : dfa Sigma) : lang Sigma
:= λ w , A.final (dfa_δ_star A A.init w)

end dfa

section example_dfa 

-- Sigma₂ = {0,1}
@[derive fintype]
inductive Sigma2 : Type
| x0 : Sigma2
| x1 : Sigma2
open Sigma2

def isFin2 : fintype Sigma2 := infer_instance

instance : has_repr Sigma2 :=
  ⟨λ s,
    match s with
    | Sigma2.x0 := "0"
    | Sigma2.x1 := "1"
    end⟩

-- Q₂ = {q0,q1,q2,q3}
@[derive fintype]
inductive Q2 : Type 
| q0 : Q2
| q1 : Q2
| q2 : Q2
| q3 : Q2

open Q2

-- we curry delta
def delta2 : Q2 → Sigma2 → Q2
| q0 x0 := q1 
| q0 x1 := q3
| q1 _ := q2
| q2 _ := q2
| q3 _ := q3

-- F₂ = {q1,q3}
def F2 : Q2 → Prop
:= λ q , q=q1 ∨ q = q3

def A2 : dfa Sigma2 := {
  Q := Q2,
  δ := delta2,
  init := q0,
  final := F2
}
-- need to show that Q2 has decidable equality
-- and F2 is decidable

-- 110 is in the language
example : dfa_lang A2 [x1,x1,x0] :=
begin
  dsimp [A2,dfa_lang,dfa_δ_star,delta2,F2],
  right,
  reflexivity,
end

-- 001 is not.
example : ¬ dfa_lang A2 [x0,x1,x1] :=
begin
  assume h,
  dsimp [A2,dfa_lang,dfa_δ_star,delta2,F2] at h,
  cases h,
  contradiction,
  contradiction,
end

end example_dfa