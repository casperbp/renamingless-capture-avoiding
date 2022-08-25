\begin{code}[hide]

module sections.3-normalization where

open import Function using (case_of_; const)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Unary using (Pred; IUniversal; _⇒_; _∈_)
open import Data.Product
open import Data.Maybe
open import Data.List using (List; []; _∷_; [_])
open import Algebra using (Op₂)
open import Algebra.Definitions
open import sections.2-interpretation
\end{code}

\section{Normalization}
\label{sec:normalization}

\begin{code}
record NameSetIntf (Name : Set) : Set₁ where
  field
    _∙_ : Op₂ (List Name)

    -- ∙ is commutative-monoidal
    ∙-id : (xs ys : List Name) → xs ∙ ys ≡ [] → xs ≡ [] × ys ≡ []
    []-idˡ : LeftIdentity _≡_ [] _∙_
    ∙-comm : Commutative _≡_ _∙_
    ∙-assoc : Associative _≡_ _∙_

    -- ─ is a difference operation for ∙
    _─_ : Op₂ (List Name)
    ─-distrʳ : _DistributesOverʳ_ _≡_ _─_ _∙_
    ─-subtractive : (xs : List Name) → xs ─ xs ≡ []
    ─-idemʳ : (xs ys : List Name) → (xs ─ ys) ─ ys ≡ xs ─ ys
    ─-swapʳ : (xs ys zs : List Name) → (xs ─ ys) ─ zs ≡ (xs ─ zs) ─ ys
    ─-single : (x y : Name) → [ x ] ─ [ y ] ≡ [ x ]
    ─[]-idʳ : RightIdentity _≡_ [] _─_
    ─-zeroˡ : LeftZero _≡_ [] _─_

  []-idʳ : RightIdentity _≡_ [] _∙_
  []-idʳ x rewrite ∙-comm x [] = []-idˡ x

  record _∧_ (P Q : List Name → Set) (xs : List Name) : Set where
    constructor _∧_∣_
    field {ys zs} : List Name
          px : P ys
          qx : Q zs
          φ  : xs ≡ ys ∙ zs


  _∖_ : (List Name → Set) → Name → List Name → Set
  (P ∖ x) xs = P (xs ─ [ x ])

  Emp : List Name → Set
  Emp = _≡ []

  ε[_] : (List Name → Set) → Set
  ε[ P ] = P []

  One : Name → List Name → Set
  One x = _≡ [ x ]
\end{code}

\begin{code}[hide]
module Normalizer (Name : Set) (_≡?_ : (x y : Name) → Dec (x ≡ y)) (NSI : NameSetIntf Name) where

  open NameSetIntf NSI
\end{code}

\begin{code}
  subst′ = subst
  syntax subst′ P eq e = e ∶ P ∣ eq

  data FV : List Name → Set where
    app : ∀[ (FV ∧ FV) ⇒ FV ]
    lam : (x : Name) → ∀[ (FV ∖ x) ⇒ FV ]
    var : (x : Name) → ∀[ One x ⇒ FV ]

  ⟦_/_⟧_ : ε[ FV ] → (x : Name) → ∀[ FV ⇒ (FV ∖ x) ]
  ⟦ e′ / y ⟧ (app (e₁ ∧ e₂ ∣ φ)) =
    app ( (⟦ e′ / y ⟧ e₁)
        ∧ (⟦ e′ / y ⟧ e₂)
        ∣ (begin
              _
            ≡⟨ cong (_─ _) φ ⟩
              _
            ≡⟨ ─-distrʳ _ _ _ ⟩
              _
            ∎) )
  ⟦ e′ / y ⟧ (lam x e) = case (x ≡? y) of λ where
    (yes refl) → lam x (e ∶ FV ∣ (sym (─-idemʳ _ _)))
    (no p)     → lam x ((⟦ e′ / y ⟧ e) ∶ FV ∣ (─-swapʳ _ _ _))
  ⟦ e′ / y ⟧ (var x φ) = case (x ≡? y) of λ where
    (yes refl) → e′ ∶ FV ∣ (begin
                              []
                            ≡˘⟨ ─-subtractive _ ⟩
                              _
                            ≡˘⟨ cong (_─ _) φ ⟩
                              _
                            ∎)
    (no  p) → var x (begin
                        _
                     ≡⟨ cong (_─ _) φ ⟩
                       _
                     ≡⟨ ─-single _ _ ⟩
                       _
                     ∎)

  data NF : Set where
    lam : (x : Name) → ε[ FV ∖ x ] → NF

  NF2FV : NF → FV []
  NF2FV (lam x e) = lam x e

  {-# NON_TERMINATING #-}
  normalize : FV [] → NF
  normalize (app (e₁ ∧ e₂ ∣ φ)) = case (∙-id _ _ (sym φ)) of λ where
    (refl , refl) → case normalize e₁ of λ where
      (lam x e) →
        let v = NF2FV (normalize e₂) in
        normalize ((⟦ v / x ⟧ e) ∶ FV ∣ (begin
                                          _
                                         ≡⟨ cong (_─ _) (─-zeroˡ _) ⟩
                                           _
                                         ≡⟨ ─-zeroˡ _ ⟩
                                           _
                                         ∎))
  normalize (lam x e) = lam x e
  normalize (var x ())  
\end{code}

\begin{code}
  data FVC (N : Set) : List Name → Set where
    app : ∀[ (FVC N ∧ FVC N) ⇒ FVC N ]
    lam : (x : Name) → ∀[ (FVC N ∖ x) ⇒ FVC N ]
    var : (x : Name) → ∀[ One x ⇒ FVC N ]
    nf  : N → ε[ FVC N ]

  ⦉_/_⦊_ : {N : Set} → ε[ FVC N ] → (x : Name) → ∀[ FVC N ⇒ (FVC N ∖ x) ]
  ⦉ e′ / y ⦊ (app (e₁ ∧ e₂ ∣ φ)) =
    app ( (⦉ e′ / y ⦊ e₁)
        ∧ (⦉ e′ / y ⦊ e₂)
        ∣ (begin
              _
            ≡⟨ cong (_─ _) φ ⟩
              _
            ≡⟨ ─-distrʳ _ _ _ ⟩
              _
            ∎) )
  ⦉ e′ / y ⦊ (lam x e) = case (x ≡? y) of λ where
    (yes refl) → lam x (e ∶ FVC _ ∣ (sym (─-idemʳ _ _)))
    (no p)     → lam x ((⦉ e′ / y ⦊ e) ∶ FVC _ ∣ (─-swapʳ _ _ _))
  ⦉ e′ / y ⦊ (var x φ) = case (x ≡? y) of λ where
    (yes refl) → e′ ∶ FVC _ ∣ (begin
                                 []
                               ≡˘⟨ ─-subtractive _ ⟩
                                 _
                               ≡˘⟨ cong (_─ _) φ ⟩
                                 _
                               ∎)
    (no  p) → var x (begin
                        _
                     ≡⟨ cong (_─ _) φ ⟩
                       _
                     ≡⟨ ─-single _ _ ⟩
                       _
                     ∎)
  ⦉ e′ / y ⦊ (nf e) = nf e ∶ FVC _ ∣ sym (─-zeroˡ _)

  data NFC : Set where
    lam : {xs : List Name} → (x : Name) → (FVC NFC ∖ x) xs → NFC
    var : Name → NFC

  {-# NON_TERMINATING #-}
  normalizeC : ∀[ FVC NFC ⇒ const (Maybe NFC) ]
  normalizeC (app (e₁ ∧ e₂ ∣ φ)) =
    case (normalizeC e₁) of λ where
      (just (lam x e)) → case (normalizeC e₂) of λ where
        (just v) → 
          normalizeC ((⦉ nf v / x ⦊ e) ∶ FVC _ ∣ ─-idemʳ _ _)
        _ → nothing
      _ → nothing
  normalizeC (lam x e) = just (lam x e)
  normalizeC (nf v)    = just v
  normalizeC (var x φ) = just (var x)
\end{code}
