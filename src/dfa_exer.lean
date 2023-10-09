import .dfa .languages_exer

set_option pp.structure_projections false

def accepts {Sigma : Type} (A : dfa Sigma) (w : word Sigma) : Prop := 
  w ∈ dfa_lang A
def rejects {Sigma : Type} (A : dfa Sigma) (w : word Sigma) : Prop := 
  w ∉ dfa_lang A
infix ` ACCEPTS `:25 := accepts
infix ` REJECTS `:25 := rejects

-- Proves either (A ACCEPTS w) or (A REJECTS w), whichever it can
--  (w must be computable value, not variable)
meta def dfa_compute : tactic unit := 
`[ constructor <|> {assume h, cases h} ]

-- using snoc because extending the word on the right keeps the
-- initial state the same
lemma dfa_snoc {Sigma : Type} {A : dfa Sigma} : ∀  (w' : word Sigma) (c : Sigma) (q : A.Q),
  dfa_δ_star A q (w'++[c]) = A.δ (dfa_δ_star A q w') c :=
  begin
    assume w' c,
    induction w' with c' w'' ih,
    assume q,
    refl,
    assume q,
    dsimp[dfa_δ_star],
    apply ih,
  end

namespace even_odd
  
  variable {Sigma : Type}

  inductive even_odd {Sigma : Type} : bool → word Sigma → Prop
    | ze: even_odd tt []
    | ne: ∀ c w, even_odd ff w → even_odd tt (w++[c])
    | zo: ∀ c, even_odd ff [c]
    | no: ∀ c w, even_odd tt w → even_odd ff (w++[c])
  def evenLen := @even_odd Sigma tt
  def oddLen := @even_odd Sigma ff

  def even_nil : evenLen [] := @even_odd.ze Sigma
  def even_cons (c : Sigma) (w : word Sigma) (o : oddLen w) : evenLen (w++[c]) := even_odd.ne c w o
  def odd_single (c : Sigma) : oddLen [c] := even_odd.zo c
  def odd_cons (c : Sigma) (w : word Sigma) (e : evenLen w) : oddLen (w++[c]) := even_odd.no c w e
  def evenLen.induction_on {w : word Sigma} (ev : evenLen w) (Ce : word Sigma → Prop) (Co : word Sigma → Prop)
                        (ce_nil : Ce []) (stepe : ∀ c w', Co w' → Ce (w'++[c]))
                        (co_single : ∀ c, Co [c]) (stepo : ∀ c w', Ce w' → Co (w'++[c])) : Ce w :=
    @even_odd.rec Sigma (λ (switch : bool), bool.rec_on switch Co Ce)
                  ce_nil (λ c w' _ co, stepe c w' co)
                  co_single (λ c w' _ ce, stepo c w' ce)
                  tt w ev

  def oddLen.induction_on {w : word Sigma} (od : oddLen w) (Co : word Sigma → Prop) (Ce : word Sigma → Prop)
                      (ce_nil : Ce []) (stepe : ∀ c w', Co w' → Ce (w'++[c]))
                      (co_single : ∀ c, Co [c]) (stepo : ∀ c w', Ce w' → Co (w'++[c])) :=
    @even_odd.rec Sigma (λ (switch : bool), bool.rec_on switch Co Ce)
                  ce_nil (λ c w' _ co, stepe c w' co)
                  co_single (λ c w' _ ce, stepo c w' ce)
                  ff w od
end even_odd

namespace exer3_1

  @[derive fintype]
  def Qₐ : Type := Q2
  open Q2

  instance : has_repr Qₐ :=
    ⟨λ s,
      match s with
      | q0 := "q0"
      | q1 := "q1"
      | q2 := "q2"
      | q3 := "q3"
      end⟩
  def isFinQₐ : fintype Qₐ := infer_instance

  @[derive fintype]
  inductive Sigmaₐ : Type
  | a : Sigmaₐ
  | b : Sigmaₐ
  open Sigmaₐ

  def isFinSigmaₐ : fintype Sigmaₐ := infer_instance

  instance : has_repr Sigmaₐ :=
    ⟨λ s,
      match s with
      | a := "a"
      | b := "b"
      end⟩

  def δₐ : Qₐ → Sigmaₐ → Qₐ 
  | q0 a := q1
  | q0 b := q2
  | q1 a := q0
  | q1 b := q3
  | q2 a := q3
  | q2 b := q0 
  | q3 a := q2
  | q3 b := q1

  def Fₐ : Qₐ → Prop 
  | q1 := true
  | q2 := true
  | _ := false

  def A : dfa Sigmaₐ := {
    Q := Qₐ,
    δ := δₐ,
    init := q0,
    final := Fₐ,
  }
  instance : has_repr A.Q :=
    ⟨λ s,
      match s with
      | q0 := "q0"
      | q1 := "q1"
      | q2 := "q2"
      | q3 := "q3"
      end⟩
  --
  #eval dfa_δ_star A A.init []

  -- Part 2
  lemma reject_nil : A REJECTS [] := by dfa_compute
  example : A ACCEPTS [b] := by dfa_compute
  example : A ACCEPTS [a,b,a,a,b] := by dfa_compute
  example : A REJECTS [b,a,b,a,b,b,b,a] := by dfa_compute

  -- Part 3
  example : (dfa_δ_star A) q0 [a,b,b,a] = q0 :=
  by calc 
    (dfa_δ_star A) q0 [a,b,b,a] 
        = (dfa_δ_star A) (δₐ q0 a) [b,b,a]  : by refl
    ... = (dfa_δ_star A) q1 [b,b,a]         : by refl
    ... = (dfa_δ_star A) (δₐ q1 b) [b,a]    : by refl
    ... = (dfa_δ_star A) q3 [b,a]           : by refl
    ... = (dfa_δ_star A) (δₐ q3 b) [a]      : by refl
    ... = (dfa_δ_star A) q1 [a]             : by refl
    ... = (dfa_δ_star A) (δₐ q1 a) []       : by refl
    ... = (δₐ q1 a)                         : by refl
    ... = q0                                : by refl

  -- Part 4
  open even_odd


  lemma step_out_of_final : ∀ (q : Qₐ) (c : Sigmaₐ),
    A.final q → ¬(A.final (δₐ q c)) := 
    begin
      assume q c qF,
      cases q,
        repeat{cases c,
        {cases qF}<|>{assume h,cases h},
        {cases qF}<|>{assume h,cases h}},
    end
  lemma backstep_out_of_final : ∀ (q : Qₐ) (c : Sigmaₐ),
    A.final (δₐ q c) → ¬(A.final q) := 
    begin
      assume q c qF,
      cases q,
        repeat{cases c,
        {cases qF}<|>{assume h,cases h},
        {cases qF}<|>{assume h,cases h}},
    end
  lemma backstep_into_final : ∀ (q : Qₐ) (c : Sigmaₐ),
    ¬(A.final (δₐ q c)) → A.final q := 
    begin
      assume q c qF,
      cases q,repeat{
        cases c, 
          constructor<|>{have f:false, apply qF,constructor,cases f},
          constructor<|>{have f:false, apply qF,constructor,cases f}},
    end
  lemma step_into_final : ∀ (q : Qₐ) (c : Sigmaₐ),
    ¬(A.final q) → A.final (δₐ q c) := 
    begin
      assume q c qF,
      cases q,repeat{
        cases c, 
          constructor<|>{have f:false, apply qF,constructor,cases f},
          constructor<|>{have f:false, apply qF,constructor,cases f}},
    end

  lemma acceptsOdds : ∀ (w : word Sigmaₐ), oddLen w → A ACCEPTS w :=
  begin
    assume w h,
    apply oddLen.induction_on h (λ w', A ACCEPTS w') (λ w', A REJECTS w'),
    exact reject_nil,
    dsimp,
    assume c w' accept_w',
    let q := dfa_δ_star A A.init w',
    change A ACCEPTS w' with (Fₐ q) at accept_w',
    dsimp[rejects,has_mem.mem,dfa_lang,dfa_δ_star],
    rw dfa_snoc,
    change dfa_δ_star A (dfa.init A) w' with q,
    apply step_out_of_final,
    exact accept_w',

    assume c,
    cases c,
    dfa_compute,
    dfa_compute,

    assume c w' reject_w',
    let q := dfa_δ_star A A.init w',
    change A REJECTS w' with ¬(Fₐ q) at reject_w',
    dsimp[accepts,has_mem.mem,dfa_lang,dfa_δ_star],
    rw dfa_snoc,
    change dfa_δ_star A (dfa.init A) w' with q,
    apply step_into_final,
    exact reject_w',
  end

  lemma oddLenNonempty : ∀ w, @oddLen Sigmaₐ w → w≠[]  := 
  begin
    assume w oddW,
    apply oddLen.induction_on oddW (λ w', w'≠[]) (λ _, true),
    constructor,
    assume c w' w'nonnil, constructor,
    assume c absurd, cases absurd,
    assume c w' _ absurd,
    cases w', cases absurd, cases absurd,
  end 

  example : ∀ (w : word Sigmaₐ), oddLen w ↔ A ACCEPTS w :=
  begin
    assume w,
    constructor,
    apply acceptsOdds,

    have stronger : ∀ w', (A REJECTS w' → evenLen w') 
                         ∧ (A ACCEPTS w'→ oddLen w'),
    assume w',
    apply list.reverse_rec_on w',
    -- nil
      constructor,
      assume _, apply even_nil,
      assume absurd, cases absurd,
    -- w' → w'++[c]
      assume w'' c ih,
      cases ih with ihe iho,
      constructor,
        assume reject_w'c,
        apply even_cons,
        apply iho,
        apply backstep_into_final,
        dsimp[rejects,has_mem.mem,dfa_lang] at reject_w'c,
        rw dfa_snoc at reject_w'c,
        exact reject_w'c,
        ---
        assume accept_w'c,
        apply odd_cons,
        apply ihe,
        apply backstep_out_of_final,
        dsimp[accepts,has_mem.mem,dfa_lang] at accept_w'c,
        rw dfa_snoc at accept_w'c,
        exact accept_w'c,

    exact and.elim_right(stronger w),

  end

end exer3_1

namespace exer3_2
  @[derive fintype]
  inductive mod3 : Type 
  | zero : mod3
  | one  : mod3
  | two  : mod3
  open mod3

  def isFinMod3 : fintype mod3 := infer_instance

  instance : has_repr mod3 :=
    ⟨λ s,
      match s with
      | zero := "0"
      | one := "1"
      | two := "2"
      end⟩

  def incr : mod3 → mod3
  | zero := one
  | one := two
  | two := zero


  @[derive fintype]
  inductive Sigma_B : Type
  | a : Sigma_B
  | b : Sigma_B
  | c : Sigma_B
  open Sigma_B

  def isFinSigmaₐ : fintype Sigma_B := infer_instance

  instance : has_repr Sigma_B :=
    ⟨λ s,
      match s with
      | a := "a"
      | b := "b"
      | c := "b"
      end⟩

  def incr_if_a : Sigma_B → mod3 → mod3
  | a := incr
  | _ := id 

  def count_a_mod3 (w : word Sigma_B) : mod3 :=
    list.reverse_rec_on w zero (λ _ x, incr_if_a x)

  lemma reverse_snoc {T : Type} : ∀ (x : T) (xs acc : list T), 
    list.reverse_core (xs++[x]) acc = x::list.reverse_core xs acc :=
  begin
    assume x xs,
    induction xs with x' xs' ih,
    assume acc,
    refl,
    assume acc,
    dsimp[list.reverse_core],
    rw ih,
  end 

  def step_count_a_mod3 : ∀ w' x, 
    count_a_mod3 (w'++[x]) = incr_if_a x (count_a_mod3 w') :=
  begin
    assume w' x,
    dsimp[count_a_mod3,list.reverse_rec_on,list.reverse],
    rw reverse_snoc,
  end

  #eval count_a_mod3 []
  #eval count_a_mod3 [b,b,a,a]
  #eval count_a_mod3 [b,b,a,a,c,b,a]


  def B : dfa Sigma_B := {
    Q := mod3,
    δ := λ q x, incr_if_a x q,
    init := zero,
    final := λ q, q=zero,
  }
  instance : has_repr B.Q := mod3.has_repr  

  #eval dfa_δ_star B B.init [b,a,a,a]
  
  example : B ACCEPTS [] := by dfa_compute
  example : B REJECTS [b,a] := by dfa_compute 
  example : B ACCEPTS [a,b,a,a,b] := by dfa_compute
  example : B REJECTS [b,a,b,a,b,b,b] := by dfa_compute

  lemma sameFun : dfa_δ_star B zero = count_a_mod3 :=
  begin
    apply funext,
    assume w,
    apply list.reverse_rec_on w,
    refl,
    assume w' x equiv_w',
    rw dfa_snoc,
    rw equiv_w',
    dsimp[B],
    rw step_count_a_mod3,
  end

  lemma correctness : ∀ w, B ACCEPTS w ↔ count_a_mod3 w = zero :=
  begin
    assume w,
    constructor,

    dsimp[accepts,(∈),dfa_lang],
    change dfa.init B with zero,
    rw sameFun,
    exact id,

    rw← sameFun,
    exact id,
  end

end exer3_2

namespace exer3_3
  open exer3_2

  @[derive fintype]
  inductive mod2 : Type 
  | even : mod2
  | odd  : mod2
  open mod2

  def isFinMod2 : fintype mod2 := infer_instance

  instance : has_repr mod2 :=
    ⟨λ s,
      match s with
      | even := "even"
      | odd := "odd"
      end⟩
  
  def rep : mod2 × mod3 → string
  | (x,y) := ("(" ++ repr x ++ "," ++ repr y ++ ")")
  instance : has_repr (mod2 × mod3) := { repr := rep }

  def flip : mod2 → mod2 
  | even := odd
  | odd := even

  #check Sigma_B.b

  def step : mod2 × mod3 → Sigma_B → mod2 × mod3
  | (as,bs) Sigma_B.a := (flip as, bs)
  | (as,bs) Sigma_B.b := (as, incr bs)
  | (as,bs) _ := (as,bs)

  def flip_if_a : Sigma_B → mod2 → mod2
  | Sigma_B.a := flip
  | _ := id
  def incr_if_b : Sigma_B → mod3 → mod3
  | Sigma_B.b := incr
  | _ := id

  def count_b_mod3 (w : word Sigma_B) : mod3 :=
    list.reverse_rec_on w mod3.zero (λ _, incr_if_b)
  def count_a_mod2 (w : word Sigma_B) : mod2 :=
    list.reverse_rec_on w mod2.even (λ _, flip_if_a)

  def a := Sigma_B.a
  def b := Sigma_B.b
  def c := Sigma_B.c

  #eval count_b_mod3 [b,c,c,b,a,b,a,a]
  #eval count_b_mod3 [b,c,c,b,a,b,a,b]
  #eval count_a_mod2 [b,c,c,b,a,b,a,a]
  #eval count_a_mod2 [b,c,c,b,a,b,a,b]

  
  def finalSet : set (mod2 × mod3) → mod2 × mod3 → Prop 
    | Z z := z ∈ Z

  def C : dfa Sigma_B := {
    Q := mod2 × mod3,
    δ := step,
    init := (mod2.even, mod3.zero),
    final := finalSet {(mod2.odd, mod3.zero)}
  }
  
  instance : has_repr C.Q := {repr := rep}

  #eval dfa_δ_star C C.init [a]
  #eval dfa_δ_star C C.init [b]
  #eval dfa_δ_star C C.init [a,b]
  #eval dfa_δ_star C C.init [a,b,a,a,b,b]
  #eval dfa_δ_star C C.init [b,a,b,a,b,b,b]

  example : C REJECTS [] := by dfa_compute
  example : C ACCEPTS [a] := by dfa_compute 
  example : C ACCEPTS [a,b,a,a,b,b] := by dfa_compute
  example : C REJECTS [b,a,b,a,b,b,b] := by dfa_compute

  def count_b_mod3_snoc : ∀ w' x, 
    count_b_mod3 (w'++[x]) = incr_if_b x (count_b_mod3 w') :=
  begin
    assume w' x,
    dsimp[count_b_mod3,list.reverse_rec_on,list.reverse],
    rw reverse_snoc,
  end
  def count_a_mod2_snoc : ∀ w' x, 
    count_a_mod2 (w'++[x]) = flip_if_a x (count_a_mod2 w') :=
  begin
    assume w' x,
    dsimp[count_a_mod2,list.reverse_rec_on,list.reverse],
    rw reverse_snoc,
  end
  
  lemma sameFun : ∀ w, dfa_δ_star C C.init w = (count_a_mod2 w, count_b_mod3 w) :=
  begin
    assume w,
    apply list.reverse_rec_on w,
    refl,
    assume w' x ih,
    rw dfa_snoc,
    rw ih, 
    rw count_b_mod3_snoc, rw count_a_mod2_snoc,
    cases x,
      refl,
      refl,
      refl,
  end

  lemma correctness : ∀ w : word Sigma_B, 
    C ACCEPTS w ↔ (count_a_mod2 w = mod2.odd ∧ count_b_mod3 w = mod3.zero) :=
  begin
    assume w,
    dsimp[accepts,(∈),dfa_lang],
    rw sameFun,
    change dfa.final C (count_a_mod2 w, count_b_mod3 w) 
    with (count_a_mod2 w, count_b_mod3 w)=(mod2.odd, mod3.zero),
    exact prod.ext_iff,
  end

end exer3_3

namespace exer3_4
  @[derive fintype]
  inductive mod5 : Type 
  | yes  : mod5
  | no1  : mod5
  | no2  : mod5
  | no3  : mod5
  | no4  : mod5
  open mod5

  def isFinMod5 : fintype mod5 := infer_instance

  instance : has_repr mod5 :=
    ⟨λ s,
      match s with
      | yes := "0"
      | no1 := "1"
      | no2 := "2"
      | no3 := "3"
      | no4 := "4"
      end⟩


  def finalSet : set (mod5) → mod5 → Prop 
    | Z z := z ∈ Z

  open nat

  def incr : mod5 → mod5
  | yes := no1
  | no1 := no2
  | no2 := no3
  | no3 := no4
  | no4 := yes



  @[derive fintype]
  inductive Sigma : Type 
  | σ₀  : Sigma
  | σ₁  : Sigma
  | σ₂  : Sigma
  | σ₃  : Sigma
  open Sigma

  def isFinSigma : fintype Sigma := infer_instance

  instance : has_repr Sigma :=
    ⟨λ s,
      match s with
      | σ₀ := "0"
      | σ₁ := "1"
      | σ₂ := "2"
      | σ₃ := "3"
      end⟩


  def incrN : ℕ → mod5 → mod5
  | 0 m := m
  | (succ n) m := incr(incrN n m)

  def incrSigma : mod5 → Sigma → mod5
  | m σ₀ := incrN 0 m
  | m σ₁ := incrN 1 m
  | m σ₂ := incrN 2 m
  | m σ₃ := incrN 3 m

  def D : dfa Sigma := {
    Q := mod5,
    δ := incrSigma,
    init := yes,
    final := finalSet {yes}
  }
  instance : has_repr D.Q := mod5.has_repr


  -- c must be '0', '1', '2', or '3'
  def decodeSigma : char → Sigma 
  | '0' := σ₀
  | '1' := σ₁
  | '2' := σ₂
  | '3' := σ₃
  | _ := σ₀ -- shouldn't happen

  notation (name := decodeWord) ⟦s⟧ := list.map decodeSigma (string.to_list s)

  #eval ⟦"23131"⟧

  #eval dfa_δ_star D D.init ⟦""⟧
  #eval dfa_δ_star D D.init ⟦"0"⟧
  #eval dfa_δ_star D D.init ⟦"23131"⟧
  #eval dfa_δ_star D D.init ⟦"133"⟧

  example : D ACCEPTS ⟦""⟧ := by dfa_compute
  example : D ACCEPTS ⟦"0"⟧ := by dfa_compute
  example : D ACCEPTS ⟦"23131"⟧ := by dfa_compute
  example : D REJECTS ⟦"133"⟧ := by dfa_compute

  def sum : list Sigma → ℕ
  | [] := 0
  | (σ₀::xs) := sum xs
  | (σ₁::xs) := 1 + sum xs
  | (σ₂::xs) := 2 + sum xs
  | (σ₃::xs) := 3 + sum xs

  def Mod5 : ℕ → mod5
  | 0 := yes
  | (succ n) := incr (Mod5 n)

  def plus5 : mod5 → mod5 → mod5
  | m yes := incrN 0 m
  | m no1 := incrN 1 m
  | m no2 := incrN 2 m
  | m no3 := incrN 3 m
  | m no4 := incrN 4 m

  lemma plus5_lneutr : ∀ m : mod5, plus5 yes m = m :=
  begin 
    assume m,
    cases m,
    repeat{refl},
  end 

  lemma incr_plus5_r : ∀ m m', incr(plus5 m m') = plus5 m (incr m') :=
  begin
    assume m m',
    cases m',
    repeat{refl},
    cases m,
    repeat{refl},
  end 
  lemma incr_plus5_l : ∀ m m', incr(plus5 m m') = plus5 (incr m) m' :=
  begin
    assume m m',
    cases m',
    repeat{refl},
  end 
  lemma plus5_incrN : ∀ (n : ℕ) (m : mod5), incrN n m = plus5 (Mod5 n) m :=
  begin
    assume n m,
    induction n with n ih,
    dsimp[Mod5,incrN],
    rw plus5_lneutr,
    dsimp[incrN],
    rw ih,
    dsimp[Mod5],
    rw← incr_plus5_l,
  end

  lemma mod_plus : ∀ (n n': ℕ), Mod5(n + n') = plus5 (Mod5 n) (Mod5 n') :=
  begin
    assume n n',
    induction n' with n' ih,
    rw nat.add_zero,
    dsimp[Mod5,plus5,incrN],
    refl,
    calc 
      Mod5 (n + succ n') 
          = Mod5 (succ( n + n')) : by refl
      ... = incr (Mod5 (n + n')) : by refl
      ... = incr (plus5 (Mod5 n) (Mod5 n')) : by rw ih
      ... = plus5 (Mod5 n) (incr(Mod5 n')) : by rw incr_plus5_r
      ... = plus5 (Mod5 n) (Mod5 (succ n')) : by refl,
  end 

  lemma plus5_comm : ∀ m m', plus5 m m' = plus5 m' m :=
  begin
    assume m m',
    cases m',repeat{cases m,repeat{refl}},
  end 
  lemma plus5_assoc : ∀ m m' m'', plus5 (plus5 m m') m'' = plus5 m (plus5 m' m'') :=
  begin
    assume m m' m'',
    cases m, repeat{cases m', repeat{cases m'', repeat{refl}}},
  end 

  lemma plus5_calc : ∀ n s q, 
    plus5 (plus5 (Mod5 n) (Mod5 s)) q = plus5 (Mod5 s) (incrN n q):=
  begin 
    assume n s q,
    calc 
      plus5 (plus5 (Mod5 n) (Mod5 s)) q
          = plus5 (plus5  (Mod5 s) (Mod5 n)) q : by rw plus5_comm (Mod5 n)
      ... = plus5 (Mod5 s) (plus5 (Mod5 n) q) : by rw plus5_assoc
      ... = plus5 (Mod5 s) (incrN n q) : by rw plus5_incrN n q,
  end

  lemma D_computes_mod5sum : ∀ w q, plus5 (Mod5 (sum w)) q = dfa_δ_star D q w :=
  begin
    assume w,
    induction w with c w' ih,
    assume q,
    dsimp[sum,Mod5,dfa_δ_star],
    rw plus5_lneutr,
    assume q,
    cases c,

    dsimp[sum],
    rw ih,
    refl,

    repeat{
      dsimp[sum],
      rw mod_plus,
      dsimp[dfa_δ_star,incrSigma,incrN,incr,dfa_δ_star],
      rw← ih,
      apply plus5_calc
    },
  end

  example : ∀ w : word Sigma, D ACCEPTS w ↔ Mod5 (sum w) = yes :=
  begin
    assume w,
    dsimp[accepts,has_mem.mem,dfa_lang],
    rw←  D_computes_mod5sum,
    dsimp[D,finalSet],
    apply iff.refl,
  end
end exer3_4