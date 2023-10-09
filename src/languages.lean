/-
LAC (COMP2012)

translating basic definitions about languages
into lean. 

-/

import data.fintype.basic
import tactic.derive_fintype
import tactic

section basics
variable Sigma : Type

-- Σ* = word Sigma
@[reducible]
def word : Type := list Sigma

def epsilon : word Sigma := []
-- ε the empty word
-- Given w v : word Sigma
-- wv becomes w++v

@[reducible]
def lang : Type := word Sigma → Prop
end basics

-- example 
-- Σ₁ = { a , b , c }

@[derive fintype]
inductive Sigma1 : Type
| a : Sigma1
| b : Sigma1
| c : Sigma1
open Sigma1

def isFin1 : fintype Sigma1 := infer_instance

instance : has_repr Sigma1 :=
  ⟨λ s,
    match s with
    | Sigma1.a := "a"
    | Sigma1.b := "b"
    | Sigma1.c := "c"
    end⟩

-- w = ab : Σ₁*
-- v = bc : Σ₁*

def w : word Sigma1 := [a,b]
def v : word Sigma1 := [b,c]

-- wv = abbc
#eval (w++v)

-- L₁ = {ab, ac } ⊆ word Σ₁
-- L₂ = {abac}

def L1 : lang Sigma1 
  := λ w , w = [a,b] ∨ w = [b,c]

def L2 : lang Sigma1 
  := λ w, w = [a,b,b,c]
#check L2
section lang_op1
variable {Sigma : Type} 

def emptyLang : lang Sigma 
  := λ w , false

def unionLang : lang Sigma → lang Sigma → lang Sigma 
    := λ L M , λ w , L w ∨ M w 

end lang_op1

-- union of languages 
-- L₁ ∪ L₂ = {ab,bc,abbc}

def L1_union_L2 : lang Sigma1 
  := unionLang L1 L2 

section lang_op2
variable {Sigma : Type} 

-- { ε }
def lang_epsilon : lang Sigma 
  := λ w , w = []

-- L₁ L₂
def concatLang : lang Sigma → lang Sigma → lang Sigma 
    := λ L M , λ wv , ∃ w v : word Sigma ,
        L w ∧ M v ∧ wv = w++v

-- alternative definition 
inductive concatLang' (L M : lang Sigma) : lang Sigma 
| inConcat : ∀ w v : word Sigma, 
      L w → M v → concatLang' (w++v) 

end lang_op2

-- concatenation of languages
-- L₁ L₂ = {ababbc, bcabbc}

def L1_concat_L2 : lang Sigma1 
  := concatLang L1 L2 

-- L₁ L₁ = {abab,abbc,bcab,bcbc}
def L1_concat_L1 : lang Sigma1 
  := concatLang L1 L1


section lang_op2
variable {Sigma : Type} 

open nat

def powerLang : lang Sigma → ℕ → lang Sigma 
| L zero := lang_epsilon  
| L (succ n) := concatLang L (powerLang L n)

def starLang : lang Sigma → lang Sigma 
  := λ L w , ∃ n : ℕ, powerLang L n w

-- alternative definition
inductive starLang' (L : lang Sigma) : lang Sigma 
| inStar_epsilon : starLang' []
| inStar_concat : ∀ w v : word Sigma, 
      L w → starLang' v → starLang' (w++v)

end lang_op2 

-- L1* = {ε , ab , ac, abab, abac, acab, acac , ..}
def L1_star : lang Sigma1
:= starLang L1

-- L2* = {ε , abac, abacabac, ...}
def L2_star : lang Sigma1
:= starLang L2





















