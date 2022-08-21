%%
%% Agda setup
%%

\begin{code}[hide]

module sections.1-introduction where

open import Level as L hiding (_⊔_)
open import Function using (case_of_; _↔_)
open import Relation.Binary.PropositionalEquality renaming ([_] to P[_])
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Unary using (Pred; IUniversal; _⇒_; _∈_)
open import Data.Empty
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Nat using (ℕ; suc; zero)
--open import Data.List as L using (List
-- open import Data.List.Properties
-- open import Data.List.Relation.Unary.All
-- open import Data.List.Membership.Propositional using (_∉_)
open import Algebra using (Op₂)
open import Algebra.Definitions

\end{code}

\section{Introduction}

Pro of explicit substitution strategy: ease of pretty-printing; debugging

\begin{code}
record NameIntf (Name : Set) : Set₁ where
  field
    _≡?_ : (x y : Name) → Dec (x ≡ y)

    Names : Set
    ∅ : Names
    _ᶜ : Names → Names
    ｛_｝ : Name → Names
    _∪_ _∩_ : Op₂ Names

    ∅-non-empty : (a : Name) → ∅ ≢ ｛ a ｝
    ∅-∪ : (x y : Names) → x ∪ y ≡ ∅ → x ≡ ∅ × y ≡ ∅
    ∅-idˡ : LeftIdentity _≡_ ∅ _∪_
    ∅-zeroˡ : LeftZero _≡_ ∅ _∩_
    ∪-comm : Commutative _≡_ _∪_
    ∩-comm : Commutative _≡_ _∩_
    ∪-assoc : Associative _≡_ _∪_
    ∩-assoc : Associative _≡_ _∩_
    ∪-distrˡ : _DistributesOverˡ_  _≡_ _∪_ _∩_
    ∩-distrˡ : _DistributesOverˡ_ _≡_ _∩_ _∪_
    ∪-distrʳ : _DistributesOverʳ_ _≡_ _∪_ _∩_
    ∩-distrʳ : _DistributesOverʳ_ _≡_ _∩_ _∪_
    ᶜ-inv   : Involutive _≡_ _ᶜ
    ᶜ-invˡ   : LeftInverse _≡_ ∅ _ᶜ _∩_
    ᶜ-single : (a b : Name) → a ≢ b → (｛ a ｝ ∩ (｛ b ｝ ᶜ)) ≡ ｛ a ｝
    ∪-DM    : (x y : Names) → (x ∪ y) ᶜ ≡ (x ᶜ) ∩ (y ᶜ)
    ∩-DM    : (x y : Names) → (x ∩ y) ᶜ ≡ (x ᶜ) ∪ (y ᶜ)
    ∪-idem : Idempotent _≡_ _∪_
    ∩-idem : Idempotent _≡_ _∩_

  ∅-idʳ : RightIdentity _≡_ ∅ _∪_
  ∅-idʳ x rewrite ∪-comm x ∅ = ∅-idˡ x

  ∅-zeroʳ : RightZero _≡_ ∅ _∩_
  ∅-zeroʳ x rewrite ∩-comm x ∅ = ∅-zeroˡ x

  ᶜ-invʳ : RightInverse _≡_ ∅ _ᶜ _∩_
  ᶜ-invʳ x rewrite ∩-comm x (x ᶜ) = ᶜ-invˡ x

  _∖_ : Op₂ Names
  x ∖ y = x ∩ (y ᶜ)

  record _⊔_ (P Q : Pred Names L.zero) (x : Names) : Set where
    constructor _⊔⟨_⟩_
    field {y z} : Names
          px : P y
          φ  : x ≡ y ∪ z
          qx : Q z

  record _⊓_ (P Q : Pred Names L.zero) (x : Names) : Set where
    constructor _⊓⟨_⟩_
    field {y z} : Names
          px : P y
          φ  : x ≡ y ∩ z
          qx : Q z

  record _─_ (P Q : Pred Names L.zero) (x : Names) : Set where
    constructor _─⟨_⟩_
    field {y z} : Names
          px : P y
          φ  : x ≡ y ∖ z
          qx : Q z

  ε[_] : Pred Names L.zero → Set
  ε[ P ] = ∀ {x} → x ≡ ∅ → P x

  Emp : Pred Names L.zero
  Emp = _≡ ∅

  One : Name → Pred Names L.zero
  One x = _≡ ｛ x ｝

module _ {Name : Set} {NI : NameIntf Name} where

  open NameIntf NI
 
  data Expr : Set where
    lam : Name → Expr → Expr
    var : Name → Expr
    app : (e₁ e₂ : Expr) → Expr

  [_/_]_ : Expr → Name → Expr → Expr
  [ e′ / y ] (lam x e) = case (x ≡? y) of λ where
    (yes _) → lam x e
    (no  _) → lam x ([ e′ / y ] e)
  [ e′ / x ] (var y) = case (x ≡? y) of λ where
    (yes _) → e′
    (no  _) → var y
  [ e′ / x ] (app e₁ e₂) = app ([ e′ / x ] e₁) ([ e′ / x ] e₂)
\end{code}

-- Substitution function for closed, untyped lambda expressions 

-- To define the language, we define a type of lambda expressions with free variables

\begin{code}
  data FV : Names → Set where
    app : ∀[ (FV ⊔ FV) ⇒ FV ]
    lam : (x : Name) → ∀[ (FV ─ One x) ⇒ FV ]
    var : (x : Name) → ∀[ One x ⇒ FV ]

  names : {x : Names} → FV x → Names
  names {x} _ = x

  ⟦_/_⟧_ : FV ∅ → (a : Name)
         → {x : Names} → FV x → FV (x ∖ ｛ a ｝)
  ⟦ e′ / y ⟧ (app (e₁ ⊔⟨ φ ⟩ e₂)) =
    app ( (⟦ e′ / y ⟧ e₁)
        ⊔⟨ begin
             _ ∖ ｛ y ｝
           ≡⟨ cong (_∖ _) φ ⟩
             (_ ∪ _) ∖ ｛ y ｝
           ≡⟨ ∩-distrʳ _ _ _ ⟩
             _
           ∎ ⟩
          (⟦ e′ / y ⟧ e₂) )
  ⟦ e′ / y ⟧ (lam x (e ─⟨ φ₁ ⟩ φ₂)) with x ≡? y
  ... | yes refl =
    lam x (e ─⟨ begin
                  _ ∩ (｛ y ｝ ᶜ)
                ≡⟨ cong (_∩ _) φ₁ ⟩
                  _ ∩ (｛ y ｝ ᶜ)
                ≡⟨ cong (λ ■ → (_ ∩ (■ ᶜ)) ∩ _) φ₂ ⟩
                  _
                ≡⟨ ∩-assoc _ _ _ ⟩
                  _
                ≡⟨ cong (_ ∩_) (∩-idem _) ⟩
                  _
                ∎ ⟩ refl)
  ... | no p = 
   lam x ( (⟦ e′ / y ⟧ e)
         ─⟨ begin
              _
            ≡⟨ cong (_∩ _) φ₁ ⟩
              _
            ≡⟨ cong (λ ■ → (_ ∩ (■ ᶜ)) ∩ _) φ₂ ⟩
              _
            ≡⟨ ∩-assoc _ _ _ ⟩
              _
            ≡⟨ cong (_ ∩_) (∩-comm _ _) ⟩
              _
            ≡˘⟨ ∩-assoc _ _ _ ⟩
              _
            ∎ ⟩
           refl )
  ⟦ e′ / y ⟧ (var x refl) with x ≡? y
  ... | yes refl rewrite ᶜ-invʳ ｛ y ｝ = e′
  ... | no  p =
    var x (begin
             ｛ x ｝ ∩ (｛ y ｝ ᶜ)
           ≡⟨ ᶜ-single _ _ p ⟩
             ｛ x ｝
           ∎)

  data βh-Res : Set where
    lam      : (x : Name) → (FV ─ One x) ∅ → βh-Res
    timeout  :                                βh-Res

  βh-normalize : ℕ → FV ∅ → βh-Res
  βh-normalize zero _    = timeout
  βh-normalize (suc n) (app (e₁ ⊔⟨ φ ⟩ e₂)) with ∅-∪ _ _ (sym φ)
  ... | (refl , refl) = case βh-normalize n e₁ of λ where
      (lam x (e ─⟨ φ ⟩ refl)) → case βh-normalize n e₂ of λ where
        (lam y e′) → βh-normalize n (subst FV (sym φ) (⟦ (lam y e′) / x ⟧ e)) 
        timeout → timeout
      timeout → timeout
  βh-normalize (suc n) (lam x e) = lam x e
  βh-normalize (suc n) (var x eq) = ⊥-elim (∅-non-empty x eq)

-- --   _[_/⟨_⟩_] : (e e′ : Expr) → FV e′ ≡ [] → (x : Name)
-- --             → ∃ λ (eᵣ : Expr) → FV eᵣ ≡ filterᵇ (λ y → not (does (x ≡? y))) (FV e)
-- --   (lam x e)    [ e′ /⟨ φ ⟩ y ] = case (x ≡? y) of λ where
-- --     (yes refl) → (lam x e , sym (filterᵇ-idem (λ y → not (does (x ≡? y))) (FV e)))
-- --     (no  p)    → let (eᵣ , φᵣ) = e [ e′ /⟨ φ ⟩ y ] in
-- --       (lam x eᵣ , (begin
-- --           filterᵇ (not ∘ does ∘ (x ≡?_))
-- --             (FV (proj₁ (e [ e′ /⟨ φ ⟩ y ])))
-- --         ≡⟨ cong (filterᵇ _) φᵣ ⟩
-- --           filterᵇ (not ∘ does ∘ (x ≡?_))
-- --             (filterᵇ (not ∘ does ∘ (y ≡?_)) (FV e))
-- --         ≡⟨ filterᵇ-swap (FV e) ⟩
-- --           filterᵇ (not ∘ does ∘ (y ≡?_))
-- --             (filterᵇ (not ∘ does ∘ (x ≡?_)) (FV e))
-- --         ∎) )
-- --   -- (var y)      [ e′ /⟨ φ ⟩ x ] = case (x ≡? y) of λ where
-- --   --   (yes _) → e′
-- --   --   (no  _) → var y
-- --   -- (app e₁ e₂)  [ e′ /⟨ φ ⟩ x ] = app (e₁ [ e′ /⟨ φ ⟩ x ]) (e₂ [ e′ / x ])
-- -- \end{code}

-- -- Works for lambda calculus with closed terms

-- -- \begin{code}
-- --   data βh-Res : Set where
-- --     lam      : (x : Name) (e : Expr) → (All (x ≡_) (FV e) ⊎ FV e ≡ []) → βh-Res
-- --     timeout  : βh-Res

-- --   lem : (x : Name) (xs : List Name)
-- --       → filterᵇ (λ y → not (does (x ≡? y))) xs ≡ []
-- --       → All (x ≡_) xs ⊎ xs ≡ []
-- --   lem _ [] eq = inj₂ eq
-- --   lem x (y ∷ xs) eq with x ≡? y
-- --   ... | yes refl = case (lem x xs) eq of λ where
-- --     (inj₁ p) → inj₁ (refl ∷ p)
-- --     (inj₂ refl) → inj₁ (refl ∷ [])

-- --   βh-normalize : (e : Expr) → FV e ≡ [] → ℕ → βh-Res
-- --   βh-normalize _ _ zero = timeout
-- --   βh-normalize (lam x e) φ (suc n) = lam x e (lem x (FV e) φ)
-- --   βh-normalize (app e₁ e₂) φ (suc n) = case (βh-normalize e₁ ) (++-conicalˡ _ _ φ) n of λ where
-- --     (lam x e φ′) → case βh-normalize e₂ (++-conicalʳ _ _ φ) n of λ where
-- --       (lam x e φ₂) → {!!}
-- --       timeout → {!!}
-- --     r → r
-- -- \end{code}

-- -- Problem: does not work for untyped lambda calculus, which can have open expressions

-- -- However, untyped lambda calculus generally compute to normal forms

-- -- It is fruitless to substitute into terms in NF

-- -- Since it is fruitless, we mark terms in HNF, and only substitute into terms that are not already in HNF

-- -- Using syntax that distinguishes terms in HNF lets us use our substitution function for closed expressions to compute with open terms

-- -- \begin{code}
-- --   data ExprG : Set where
-- --     lam : Name → ExprG → ExprG
-- --     var : Name → ExprG
-- --     app : (e₁ e₂ : ExprG) → ExprG
-- --     clo : ExprG → ExprG

-- --   FVG : ExprG → List Name
-- --   FVG (lam x e) = filter (x ≡?_) (FVG e)
-- --   FVG (var x) = x ∷ []
-- --   FVG (app e₁ e₂) = FVG e₁ ++ FVG e₂
-- --   FVG (clo x) = []

-- --   -- _⟨_/_⟩ : ExprG → (∃ λ (e : ExprG) → FVG e ≡ []) → Name → ExprG
-- --   -- (lam y e)    ⟨ e′ / x ⟩  =  ≡?[ (λ _ → lam y e)
-- --   --                               , (λ _ → lam y (e ⟨ e′ / x ⟩)) ]
-- --   --                               (x ≡? y)
-- --   -- (var y)      ⟨ e′ / x ⟩  =  ≡?[ (λ _ → proj₁ e′)
-- --   --                               , (λ _ → var y) ]
-- --   --                               (x ≡? y)
-- --   -- (app e₁ e₂)  ⟨ e′ / x ⟩  = app (e₁ ⟨ e′ / x ⟩) (e₂ ⟨ e′ / x ⟩)
-- --   -- (clo e)      ⟨ e′ / x ⟩  = clo e
-- -- \end{code}

-- -- \begin{code}
-- --   -- data _↭_ : Expr → ExprG → Set where
-- --   --   lam↭ : {x : Name} {e : Expr} {g : ExprG}
-- --   --        → 
-- --   --        → (lam x e) ↭ (lam x g)
-- -- \end{code}

-- -- \begin{code}
-- --   -- {-# TERMINATING #-}
-- --   -- unclose : ExprG → Expr
-- --   -- unclose (lam x e) =
-- --   --   let (z , _) = fresh (FVG e) in
-- --   --   lam z (unclose (e ⟨ (clo (var z) , refl) / x ⟩))
-- --   -- unclose (var x) = var x
-- --   -- unclose (app e₁ e₂) = app (unclose e₁) (unclose e₂)
-- --   -- unclose (clo e) = unclose e
-- -- \end{code}

-- -- \begin{code}
-- --   -- thm : (e e′ : ExprG) (x : Name) (P : FVG e′ ≡ [])
-- --   --     → (unclose e) [ unclose e′ / x ] ≡ unclose (e ⟨ (e′ , P) / x ⟩)
-- --   -- -- thm (lam x e) e′ y P with (x ≡? proj₁ (fresh (FVG e)))
-- --   -- -- ... | p = {!!}
-- --   -- thm (var x) e′ x₁ P with (x₁ ≡? x)
-- --   -- ... | no ¬p = refl
-- --   -- ... | yes p = refl
-- --   -- thm (app e e₁) e′ x P = cong₂ app (thm e e′ x P) (thm e₁ e′ x P)
-- --   -- thm (clo e) e′ x P = {!!}
-- -- \end{code}

-- -- \cite{}

-- -- %%% Local Variables:
-- -- %%% reftex-default-bibliography: ("../references.bib")
-- -- %%% End:
