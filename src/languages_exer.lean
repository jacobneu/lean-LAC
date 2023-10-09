import .languages
set_option pp.structure_projections false


def le(m n : ℕ) : Prop :=
  ∃ k : ℕ , k + m = n
local notation (name := le) x ≤ y := le x y


lemma le_refl_ : ∀ n, n ≤ n := begin assume n, existsi 0, rw nat.zero_add, end 
lemma one_le_two_ : 1 ≤ 2 := begin existsi 1, refl, end 

namespace lang_lemmas 
  variable {Sigma : Type}

  open nat

  -- Define w ∈ L
  instance : has_mem (word Sigma) (lang Sigma) :=
  ⟨ λ w L, L w ⟩ 
  -- Define ∩ on languages
  instance : has_inter (lang Sigma) :=
    ⟨ λ L L' w, w ∈ L ∧ w ∈ L' ⟩
  -- Define ∪ on languages
  instance : has_union (lang Sigma) :=
    ⟨ unionLang ⟩
  -- Use ++ for concatLang
  instance : has_append (lang Sigma) :=
    ⟨ concatLang ⟩ 
  -- singleton languages: if w : word Sigma, {w} : lang Sigma 
  instance : has_singleton (word Sigma) (lang Sigma) :=
    ⟨ λ w w', w' = w ⟩ 
  -- use ∅ for the empty language
  instance : has_emptyc (lang Sigma) :=
    ⟨ emptyLang ⟩ 
  -- insert (allows for enumerating finite langs like {[], [a]} )
  instance : has_insert (word Sigma) (lang Sigma) :=
    ⟨ λ w L w', w' = w ∨ L w' ⟩
  -- sep ( {w ∈ L | Φ} )
  instance : has_sep (word Sigma) (lang Sigma) :=
    ⟨ λ Φ L w, w ∈ L ∧ Φ w ⟩ 
  instance : has_subset (lang Sigma) :=
    ⟨ λ sub sup, ∀ w : word Sigma, w ∈ sub → w ∈ sup ⟩ 
  

  def len {Sigma : Type} : word Sigma → ℕ 
  | [] := 0
  | (_::xs) := 1 + len xs


  lemma langext : ∀ L L' : lang Sigma, 
    (∀ w : word Sigma, w ∈ L ↔ w ∈ L') → L = L' :=
  begin
    assume L L' foralliff,
    apply funext,
    assume w,
    apply propext,
    apply foralliff,
  end

  lemma union_assoc : ∀ L1 L2 L3 : lang Sigma,
    unionLang L1 (unionLang L2 L3) = unionLang (unionLang L1 L2) L3 :=
  begin
    assume L1 L2 L3,
    apply langext,
    assume w,
    constructor,
    assume h,
    cases h, 
      left, left, exact h,
      cases h, 
        left, right, exact h,
        right, exact h,
    assume h,
    cases h,
      cases h,
        left, exact h,
        right, left, exact h,
      right, right, exact h,
  end

  lemma union_comm : ∀ L1 L2 : lang Sigma,
    unionLang L1 L2 = unionLang L2 L1 :=
  begin
    assume L1 L2,
    apply langext,
    assume w,
    constructor,
    assume h,
    cases h, right, exact h, left, exact h,
    assume h,
    cases h, right, exact h, left, exact h,
  end

  lemma concat_assoc : ∀ L1 L2 L3 : lang Sigma,
    L1 ++ (L2 ++ L3) = (L1 ++ L2) ++ L3 :=
  begin
    assume L1 L2 L3,
    apply langext,
    assume w,
    constructor,

    assume h,
    cases h with w1 h, cases h with w23 h, cases h with L1w1 h, cases h with h' h,
    cases h' with w2 h', cases h' with w3 h', cases h' with L2w2 h', cases h' with L3w3 h',
    existsi (w1++w2), existsi w3,
    constructor,
      {
        existsi w1, existsi w2,
        constructor,
          exact L1w1, 
          constructor,
            exact L2w2, 
            refl,
      },
      {
        constructor,
          exact L3w3,
          {
            rewrite h, 
            rewrite h', 
            rewrite list.append_assoc,
          },
      },

    assume h',
    cases h' with w12 h', cases h' with w3 h', cases h' with h h', cases h' with L3w3 h',
    cases h with w1 h, cases h with w2 h, cases h with L1w1 h, cases h with L2w2 h,
    existsi w1, existsi (w2 ++ w3),
    constructor, 
      exact L1w1,
      {
        constructor,
        {
          existsi w2, 
          existsi w3,
          constructor,
          exact L2w2,
          constructor, 
          exact L3w3, 
          refl
        },
        {
          rewrite h', 
          rewrite h, 
          rewrite list.append_assoc
        }
      },
    
  end

  lemma concat_lzero : ∀ L : lang Sigma, ∅ ++ L = ∅ :=
  begin
    assume L,
    apply langext,
    assume w,
    constructor,
    assume h,
    dsimp[(∈),concatLang] at h,
    cases h with w' h, cases h with w'' h,
    cases h with absurdity rest,
    dsimp[has_emptyc.emptyc,emptyLang] at absurdity,
    contradiction,

    assume w_in_empty,
    dsimp[has_mem.mem,has_emptyc.emptyc,emptyLang] at w_in_empty,
    contradiction,
  end 

  lemma concat_rzero : ∀ L : lang Sigma, L ++ ∅ = ∅ :=
  begin
    assume L,
    apply langext,
    assume w,
    constructor,
    assume h,
    dsimp[(∈),concatLang] at h,
    cases h with w' h, cases h with w'' h,
    cases h with _ h, cases h with absurdity rest,
    dsimp[has_emptyc.emptyc,emptyLang] at absurdity,
    contradiction,

    assume w_in_empty,
    dsimp[has_mem.mem,has_emptyc.emptyc,emptyLang] at w_in_empty,
    contradiction,
  end 

  lemma concat_lneutr : ∀ L : lang Sigma, {[]} ++ L = L :=
  begin
    assume L,
    apply langext,
    assume w,
    constructor,
    assume h,
    dsimp[has_mem.mem,concatLang] at h,
    cases h with must_be_empty h, cases h with must_be_w h, 
    cases h with proof_isempty h, cases h with L_mbw h,
    dsimp[has_singleton.singleton] at proof_isempty,
    rw proof_isempty at h,
    rw list.nil_append at h,
    rw← h at L_mbw,
    exact L_mbw,

    assume h,
    -- existsi [],
    dsimp[has_mem.mem,concatLang],
      -- not sure why it's not accepting existsi here (for me at least)
    constructor, tactic.swap, exact [],
    existsi w,
    constructor,
    dsimp[has_singleton.singleton],
    refl,
    constructor,
    exact h,
    rw list.nil_append,
  end

  lemma concat_rneutr : ∀ L : lang Sigma, L ++ {[]} = L :=
  begin
    assume L,
    apply langext,
    assume w,
    constructor,
    assume h,
    dsimp[has_mem.mem,concatLang] at h,
    cases h with must_be_w h, cases h with must_be_empty h, 
    cases h with L_mbw h, cases h with proof_isempty h,
    dsimp[has_singleton.singleton] at proof_isempty,
    rw proof_isempty at h,
    rw list.append_nil at h,
    rw← h at L_mbw,
    exact L_mbw,

    assume h,
    -- existsi [],
    dsimp[has_mem.mem,concatLang],
    existsi w,
      -- not sure why it's not accepting existsi here (for me at least)
    constructor, tactic.swap, exact [],
    constructor,
    exact h,
    constructor,
    dsimp[has_singleton.singleton],
    refl,
    rw list.append_nil,
  end

  open starLang'

  lemma pow1Lemma : ∀ {L : lang Sigma}, powerLang L 1 = L :=
  begin
    assume L,
    apply langext,
    assume w,
    constructor,
    assume h,
    cases h with w' rest, cases rest with v rest, cases rest with Lw' rest, cases rest with v_empty h,
    dsimp[powerLang,lang_epsilon] at v_empty,
    rw v_empty at h, rw list.append_nil at h, rw h,
    exact Lw',

    assume Lw,
    existsi [w,[]],
    constructor,
    exact Lw,
    constructor,
    dsimp[powerLang,lang_epsilon],refl,
    rw list.append_nil,
  end
  lemma pow2Lemma : ∀ {L : lang Sigma}, powerLang L 2 = concatLang L L :=
  begin
    assume L,
    change concatLang L (powerLang L 1) = concatLang L L,
    rw pow1Lemma,
  end 

  lemma powerLemma : ∀ {L : lang Sigma} (n : ℕ) (w : word Sigma), 
    w ∈ powerLang L n → w ∈ starLang' L :=
  begin
    assume L n,
    induction n with n' IH,
    assume w hw,
    dsimp[powerLang,lang_epsilon,(∈)] at hw,
    rw hw,
    apply inStar_epsilon,
    assume w hw,
    cases hw with w' rest, cases rest with v rest, cases rest with Lw' rest,
    cases rest with hv hww'v,
    rw hww'v,
    apply inStar_concat,
    exact Lw',
    apply IH,
    exact hv,
  end

  lemma starLang_equiv : @starLang = @starLang' :=
  begin
    apply funext, assume Sigma,
    apply funext, assume L,
    apply langext,
    assume w,
    constructor,

    assume h,
    cases h with n hw,
    cases n,
    dsimp[powerLang,lang_epsilon] at hw,
    rw hw,
    apply inStar_epsilon,
    cases hw with w' rest, cases rest with v rest, cases rest with Lw' rest,
    cases rest with hv hww'v,
    rw hww'v,
    apply inStar_concat,
    exact Lw',
    apply powerLemma,
    exact hv,

    -- other direction
    assume h,
    induction h with w' v Lw' hv ih,
    existsi 0,
    dsimp[powerLang,lang_epsilon],
    refl,
    cases ih with n pLnv,
    existsi (succ n),
    dsimp[powerLang],
    existsi w',
    existsi v,
    constructor,
    exact Lw',
    constructor,
    exact pLnv,
    refl,
  end

  lemma starLang_closed : ∀ {L : lang Sigma} (w w₁ : word Sigma),
    w ∈ starLang' L → w₁ ∈ starLang' L → (w++w₁) ∈ starLang' L :=
    begin
      assume L w w₁ hw h₁,
      induction hw with w' v Lw' hv ih,
      exact h₁,
      rw list.append_assoc,
      apply starLang'.inStar_concat,
      exact Lw',
      exact ih,
    end

  -- To prove x ∈ { ..., x', ...}
  -- T is a tactic for proving x=x' (e.g. refl)
  meta def in_enumerated_set (T : tactic unit): tactic unit :=
    `[ solve1{repeat{{left,T} <|> right},
       try{dsimp[has_singleton.singleton]}, 
       try{T}}
     ]
  meta def in_enumerated_or_lie (T T' : tactic unit) : tactic unit :=
    `[ solve1{ {in_enumerated_set T} <|> repeat{T'}  }  ]
  
end lang_lemmas


namespace exer2_1

  open lang_lemmas


  -- def pow {Sigma : Type} : word Sigma

  @[derive fintype]
  inductive Sigma : Type
  | three : Sigma
  | five : Sigma
  | seven : Sigma
  | nine : Sigma
  open Sigma

  def isFinSigma : fintype Sigma := infer_instance

  instance : has_repr Sigma :=
    ⟨λ s,
      match s with
      | three := "3"
      | five := "5"
      | seven := "7"
      | nine := "9"
      end⟩

  def w3 : word Sigma := [three]
  def w5 : word Sigma := [five]
  def w7 : word Sigma := [seven]
  def w9 : word Sigma := [nine]
  def w33 : word Sigma := [three,three]
  def w35 : word Sigma := [three,five]
  def w37 : word Sigma := [three,seven]
  def w39 : word Sigma := [three,nine]
  def w53 : word Sigma := [five,three]
  def w55 : word Sigma := [five,five]
  def w57 : word Sigma := [five,seven]
  def w59 : word Sigma := [five,nine]
  def w73 : word Sigma := [seven,three]
  def w75 : word Sigma := [seven,five]
  def w77 : word Sigma := [seven,seven]
  def w79 : word Sigma := [seven,nine]
  def w93 : word Sigma := [nine,three]
  def w95 : word Sigma := [nine,five]
  def w97 : word Sigma := [nine,seven]
  def w99 : word Sigma := [nine,nine]



  def L : lang Sigma  := λ w, 1 ≤ len w ∧ len w ≤ 2

  example : L w99 :=
  begin
    constructor,
    existsi 1,
    refl,
    existsi 0,
    refl,
  end

  lemma fact : ∀ m n, m + (1 + (1 + (1 + n))) ≠ 2 := sorry


  lemma getWord_L : ∀ w : word Sigma, L w → 
    (∃ c : Sigma, w = [c]) ∨ (∃ c c' : Sigma, w = [c,c']) :=
  begin
    assume w Lw,
    cases w with c₀ w',
    -- w=[], contradiction
      cases Lw with one_le_zero _,
      cases one_le_zero, contradiction,
    cases w' with c₁ w'',
    -- |w|=1
      left, existsi c₀, refl,
    cases w'' with c₂ w''',
    -- |w|=2
      right, existsi c₀, existsi c₁, refl,
    -- |w|>2, contradiction
      cases Lw with _ three_le_two,
      dsimp[len] at three_le_two,
      cases three_le_two with m absurdity, 
      have f : false,
      apply (fact m (len w''')),
      exact absurdity,
      cases f,
  end 

  example : L = {w3,w5,w7,w9,w33,w35,w37,w39,w53,w55,w57,w59,w73,w75,w75,w77,w79,w93,w95,w97,w99} :=
  begin
    apply langext,
    assume w, 
    constructor,
    assume Lw,
    cases (getWord_L w Lw) with h,
    -- singleton
    cases h with c hc,
    cases c,
    repeat{in_enumerated_set `[ exact hc ]},
    -- 2-letter word
    cases h with c rest,
    cases rest with c' hcc',
    cases c, 
      /- For each c and each c', 
         keep going right until it works to go left -/
      repeat{
        cases c',
        repeat{in_enumerated_set `[ exact hcc' ]},
      },


    assume h,
    -- prove 1-char words are in L
    repeat{cases h, rw h, constructor, apply le_refl_, exact one_le_two_},
    -- prove 2-char words are in L
    repeat{cases h, try{dsimp[has_singleton.singleton] at h},rw h, constructor, exact one_le_two_, apply le_refl_},
  end

end exer2_1

namespace exer2_2

  open lang_lemmas

  -- Σ = {a,b,c}
  def Sigma : Type := Sigma1
  open Sigma1

  def L1 : lang Sigma := { [], [b], [a,c]}

  def L2 : lang Sigma := { [a], [b], [c,a]}

  example : L1 ∪ L2 = {[], [b], [a,c], [a], [c,a]} :=
  begin
    apply langext,
    assume w,
    constructor,
    assume h,
      -- boring casework (could probably automate)
      cases h, cases h, left, exact h,
      cases h, right, left, exact h,
      right, right, left, exact h,
      cases h, right, right, right, left, exact h,
      cases h, right, left, exact h,
      right, right, right, right, exact h,

    assume h,
      cases h, left, rw h, left, refl, -- [] ∈ L1
      cases h, left, rw h, right, left, refl, -- [b] ∈ L1
      cases h, left, rw h, right, right, dsimp[has_singleton.singleton], refl, -- [a,c] ∈ L1
      cases h, right, left, exact h, -- [a] ∈ L2
      dsimp[has_singleton.singleton], right, right, right, exact h, -- [c,a] ∈ L2
  end

  lemma L1_inter_L2 : L1 ∩ L2 = {[b]} :=
  begin
    apply langext,
    assume w,
    constructor,
    dsimp[has_mem.mem,has_singleton.singleton],
    assume h,
    dsimp[has_inter.inter] at h,
    cases h with h1 h2,
    -- boring casework
      cases h1, cases h2,rw h1 at h2,cases h2, cases h2,
      exact h2, rw h1 at h2, cases h2, cases h1, exact h1,
      cases h2, dsimp[has_singleton.singleton] at h1, rw h1 at h2, cases h2,
      cases h2, dsimp[has_singleton.singleton] at h1, rw h1 at h2,
      cases h2, dsimp[has_singleton.singleton] at h1, rw h1 at h2, cases h2, 

    assume h,
    dsimp[has_mem.mem,has_singleton.singleton] at h,
    rw h,
    constructor,
    right,left,refl,
    right,left,refl,

  end  

  lemma postapp_b : L1 ++ {[b]} = {[b], [b, b], [a, c, b]} :=
  begin

    apply langext,
    assume w,
    constructor,

    -- L1 ++ {[b]} ⊆ {[b], [b, b], [a, c, b]}
    assume h, cases h with w1 h, cases h with justb h, 
    cases h with L1w1 h, cases h with is_b h, dsimp[has_singleton.singleton] at is_b,
    cases L1w1, 
      -- w1 = []
      rw L1w1 at h, rw list.nil_append at h, rw is_b at h,
      left, exact h,
    cases L1w1,
      -- w1 = [b]
      rw L1w1 at h, rw is_b at h,
      right, left, rw h, refl,
      -- w1 = [a,c]
      dsimp[has_singleton.singleton] at L1w1, rw L1w1 at h, rw is_b at h,
      right, right, dsimp[has_singleton.singleton], rw h, refl,
    
    -- {[b], [b, b], [a, c, b]} ⊆ L1 ++ {[b]}
    assume h,
    cases h,
    -- existsi [], existsi [b]
    constructor, tactic.swap, exact [],
    constructor, tactic.swap, exact [b],
    constructor,
    left, refl,
    constructor,
    dsimp[has_singleton.singleton], refl,
    rw h, rw list.nil_append,
    cases h,
    constructor, tactic.swap, exact [b],
    constructor, tactic.swap, exact [b],
    constructor,
    right, left, refl,
    constructor,
    dsimp[has_singleton.singleton], refl,
    rw h, refl,
    dsimp[has_singleton.singleton] at h, rw h,
    constructor, tactic.swap, exact [a,c],
    constructor, tactic.swap, exact [b],
    constructor,
    right, right,dsimp[has_singleton.singleton], refl,
    constructor,
    dsimp[has_singleton.singleton], refl,
    refl,
  end

  example : L1 ++ {[]} ++ (L1 ∩ L2) = {[b], [b,b], [a,c,b]} :=
  begin
    calc
      L1 ++ {list.nil} ++ L1 ∩ L2 
          = L1 ++ L1 ∩ L2 : by rw concat_rneutr
      ... = L1 ++ {[b]} : by rw L1_inter_L2
      ... = {[b], [b, b], [a, c, b]} : by rw postapp_b,
  end


end exer2_2

namespace exer2_4
  open lang_lemmas
  open nat

  def Sigma := Sigma1
  open Sigma1

  def fullLang : lang Sigma := starLang' ({[],[a],[b],[b,c]})

  meta def obviouslyNot : tactic unit :=
    `[ assume h, cases h, cases h_h ]

  lemma append_len : ∀ (w1 w2 : word Sigma), len (w1 ++ w2) = (len w1) + (len w2) := sorry
  lemma add_le : ∀ (m n p : ℕ), m + n ≤ p → n ≤ p
   | zero n p := begin rw nat.zero_add, assume h, exact h, end
   | (succ m) zero p := begin assume _, existsi p, rw nat.add_zero, end
   | (succ m) (succ n) p := 
      begin 
        assume h,
        cases h with d proof, 
        existsi (d + succ m), 
        rw add_assoc,
        exact proof, 
      end 
  lemma four_nle_three : ¬(4 ≤ 3) := by obviouslyNot
  lemma five_nle_three : ¬(5 ≤ 3) := by obviouslyNot

  lemma zero_le_three : 0 ≤ 3 := begin existsi 3, refl end 
  lemma one_le_three : 1 ≤ 3 := begin existsi 2, refl, end
  lemma two_le_three : 2 ≤ 3 := begin existsi 1, refl, end

  def L : lang Sigma := { w ∈ fullLang | len w ≤ 3 }
  def Lx : lang Sigma := { [], [a], [b], [a,a], [a,b], [b,a], [b,b], [b,c], 
    [a,a,a], [a,a,b], [a,b,a], [a,b,b], [a,b,c], 
    [b,a,a], [b,a,b], [b,b,a], [b,b,b], [b,b,c],
    [b,c,a], [b,c,b]}
  
  lemma no_single_c : [c] ∉ Lx :=
    begin 
      assume abs,
      repeat{cases abs}, 
    end
  lemma singles_in_Lx : ∀ x : Sigma, [x] ∈ Lx → [x]=[a] ∨ [x]=[b] :=
  begin
    assume x h,
    cases h,
    cases h,
    cases h,
    left,
    exact h,
    cases h,
    right,
    exact h,
    repeat{cases h},
  end
  lemma doubles_in_Lx : ∀ (x y : Sigma), [x,y] ∈ Lx → [x,y]=[b,c] ∨ ([x]∈Lx ∧ [y]∈Lx) :=
  begin
    assume x y h,
    cases y,
      cases x,
      right,solve1{constructor, in_enumerated_set `[refl], in_enumerated_set `[refl]},
      right,solve1{constructor, in_enumerated_set `[refl], in_enumerated_set `[refl]},
      solve1{repeat{cases h}},
 
      cases x,
      right,solve1{constructor, in_enumerated_set `[refl], in_enumerated_set `[refl]},
      right,solve1{constructor, in_enumerated_set `[refl], in_enumerated_set `[refl]},
      solve1{repeat{cases h}},

      cases x,
        solve1{repeat{cases h}},
        left, refl,
        solve1{repeat{cases h}},
  end
  lemma triples_in_Lx : ∀ (x y z : Sigma), [x,y,z] ∈ Lx → 
    ([x] ∈ Lx ∧ [y,z] ∈ Lx) ∨ ([x,y] ∈ Lx ∧ [z] ∈ Lx) :=
  begin
    assume x y z h,
    cases x,

      solve1{
        -- x=a, so prove [a]∈Lx and (either [y,z]∈Lx or [a,y,z]∉Lx)
        left,
        constructor,
        in_enumerated_set `[refl], -- check directly that [a]∈Lx
        -- For each y and each z, either [y,z]∈Lx, or else h:[a,y,z]∈Lx is a contradiction
        cases y, 
        repeat{
          cases z,
          repeat{in_enumerated_or_lie `[refl] `[cases h]}
        }
      },

      cases y,
        -- x=b, y=a, so prove [b]∈Lx and (either [a,z]∈Lx or [b,a,z]∉Lx)
        solve1{
        left, 
        constructor,
        in_enumerated_set `[refl],
        cases z,
        repeat{in_enumerated_or_lie `[refl] `[cases h]}
        },
      
        -- x=b, y=b, so prove [b]∈Lx and [b,z]∈Lx for any z
        solve1{
        left,
        constructor,
        in_enumerated_set `[refl],
        cases z,
        repeat{in_enumerated_set `[refl]}
        },

        -- x=b, y=c, so prove [b,c]∈Lx and (either [z]∈Lx or [b,c,z]∉Lx)
        solve1{
        right,
        constructor,
        in_enumerated_set `[refl],
        cases z,
        repeat{in_enumerated_or_lie `[refl] `[cases h]}
        },
      
      -- x=c, so h:[c,y,z]∈Lx is a contradiction
      repeat{cases h},
  end  

  lemma completeness1 : ∀ x : Sigma, [x] ∈ Lx → [x] ∈ L
    | c h := begin have f : false, apply no_single_c, exact h, cases f, end
    | x h := 
      begin 
        constructor,
        apply powerLemma 1,
        rw pow1Lemma,
        cases (singles_in_Lx x h) with isA isB,
        in_enumerated_set `[exact isA],
        in_enumerated_set `[exact isB],
        exact one_le_three,
      end
  lemma completeness2 : ∀ (x y : Sigma), [x,y] ∈ Lx → [x,y] ∈ L :=
  begin 
    assume x y h,
    cases (doubles_in_Lx x y h) with isBC singlesIn,
    rw isBC,
    constructor,
    apply powerLemma 1,
    rw pow1Lemma,
    in_enumerated_set `[refl],
    exact two_le_three,
    cases singlesIn with hx hy,
    change [x,y] with [x]++[y],
    constructor,
    apply starLang_closed,
    cases (completeness1 x hx) with Lx _,
    exact Lx,
    cases (completeness1 y hy) with Ly _,
    exact Ly,
    exact two_le_three,
  end   
  lemma completeness : ∀ (w : word Sigma), w ∈ Lx → w ∈ L
    | [] _ := 
      begin 
        constructor, 
        apply starLang'.inStar_epsilon,
        exact zero_le_three 
      end
    | [x] h := completeness1 x h
    | [x,y] h := completeness2 x y h
    | [x,y,z] h :=
      begin 
        cases (triples_in_Lx x y z h) with lastTwo firstTwo,

        change [x,y,z] with [x]++[y,z],
        cases lastTwo with first last,
        constructor,
        apply starLang_closed,
        cases (completeness1 x first) with hx _,
        exact hx,
        cases (completeness2 y z last) with hyz _,
        exact hyz,
        apply le_refl_,

        change [x,y,z] with [x,y]++[z],
        cases firstTwo with first last,
        constructor,
        apply starLang_closed,
        cases (completeness2 x y first) with hxy _,
        exact hxy,
        cases (completeness1 z last) with hz _,
        exact hz,
        apply le_refl_,
      end
    | (_::_::_::_::_) h := begin repeat{cases h}, end

  example : L = 
      { [], [a], [b], [a,a], [a,b], [b,a], [b,b], [b,c], 
        [a,a,a], [a,a,b], [a,b,a], [a,b,b], [a,b,c], 
        [b,a,a], [b,a,b], [b,b,a], [b,b,b], [b,b,c],
        [b,c,a], [b,c,b]} :=
  begin
    let RHS : lang Sigma := { [], [a], [b], [a,a], [a,b], [b,a], [b,b], [b,c], [a,a,a], [a,a,b], [a,b,a], [a,b,b], [a,b,c], [b,a,a], [b,a,b], [b,b,a], [b,b,b], [b,b,c], [b,c,a], [b,c,b]},
    
    apply langext,
    assume w,
    constructor,

    -- { w ∈ fullLang | len w ≤ 3 } ⊆ {[], [a], [a,a], [a,b], ... }
    assume h, cases h with h hlen,
    induction h with w' v Lw' starv ih,
    -- BC: w = []
      left, refl,
    -- IS: w = w' ++ v, for w' ∈ L and v ∈ L* s.t. |w'++v|≤3
      -- Quick lemma
      have vin : v ∈ RHS,
      rw append_len at hlen,
      apply ih, apply add_le, exact hlen,

      cases Lw',
      -- w' = []
      rw Lw', 
      rw list.nil_append,
      rw Lw' at hlen, 
      rw list.nil_append at hlen, 
      apply ih, 
      exact hlen,

      cases Lw',
      -- w' = [a]
        rw Lw',
        -- show that [a],[a,a],[a,b],[a,a,a],[a,a,b],[a,b,a],[a,b,b],[a,b,c] ∈ RHS
        repeat{
          cases vin, 
          rw vin, 
          in_enumerated_set `[ refl ]
        },
        -- show that [a] ++ v ∉ RHS if |v|=3
        repeat{
          cases vin, 
          try{dsimp[has_singleton.singleton] at vin},
          rw vin, rw Lw' at hlen, rw vin at hlen, 
          have f : false,
          apply four_nle_three, 
          exact hlen,
          cases f,
        },

      cases Lw',
      -- w' = [b]
        rw Lw',
        -- show that [b],[b,a],[b,b],[b,a,a],[b,a,b],[b,b,a],[b,b,b],[b,b,c] ∈ RHS
        repeat{
          cases vin, 
          rw vin, 
          in_enumerated_set `[ refl ]
        },
        -- show that [b] ++ v ∉ RHS if |v|=3
        repeat{
          cases vin, 
          try{dsimp[has_singleton.singleton] at vin},
          rw vin, rw Lw' at hlen, rw vin at hlen, 
          have f : false,
          apply four_nle_three, 
          exact hlen,
          cases f,
        },

      dsimp[has_singleton.singleton] at Lw',
      -- w' = [b,c]
      rw Lw', 
        -- show that [b,c], [b,c,a], [b,c,b] ∈ RHS
        repeat{
          cases vin, 
          rw vin, 
          in_enumerated_set `[ refl ]
        },
        -- show that [b,c] ++ v ∉ RHS if |v|>1
        repeat{
          cases vin, 
          try{dsimp[has_singleton.singleton] at vin},
          rw vin, rw Lw' at hlen, rw vin at hlen, 
          have f : false,
          {apply four_nle_three, exact hlen}
          <|> {apply five_nle_three, exact hlen},
          cases f,
        },

    -- Other side already done!
    apply completeness,
 
  end
end exer2_4