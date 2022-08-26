\begin{code}[hide]

module sections.3-normalization where

open import Function using (case_of_; const; _$_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary
--open import Relation.Unary using (Pred; IUniversal; _⇒_; _∈_)
open import Data.Product
open import Data.Maybe
open import Data.List using (List; []; _∷_; [_])
open import Algebra using (Op₂)
open import Algebra.Definitions
open import sections.2-interpretation
\end{code}

\section{Renamingless Capture Avoiding Substitution using Intrinsic Typing}
\label{sec:normalization}

We show that both of the substitution functions from \cref{sec:interpretation} are capture avoiding because they only ever substitute closed terms under $\lambda$ binders.
We do so by strengthening the type of our substitution functions and normalizers to reflect the invariants that they are subject to, using \emph{intrinsic typing}~\citep{AltenkirchR99,Augustsson99anexercise}.
Our approach to intrinsic typing is inspired by the Agda standard library\footnote{E.g., \url{https://github.com/agda/agda-stdlib/blob/v1.7.1/src/Relation/Unary.agda}} and the work of~\citet{RouvoetPKV20}.

\subsection{Prelude to Intrinsic Typing}

We will be intrinsically typing untyped $\lambda$ terms by their set of free variables.
For example, $\lambda x .\, y$ where $x \neq y$ will be typed as a term whose free variable set is $\{ y \}$.
On other words, terms will be given by \emph{predicates over free variables}.
\Cref{fig:connectives} introduces some logical connectives for such predicates.
We will make use of these connectives to write concise type signatures and normalizers, akin to the ones in the previous section, but which Agda can check are safe-by-construction.
For example, in \cref{sec:interpreting-closed-intrinsic} we use the connectives to assert and verify that the closed substitution function from \cref{sec:interpreting-closed} only substitutes for closed terms, that substitution eliminates a free variable, and that normalization of closed terms only applies closed substitutions to compute closed $\lambda$ terms as a result.
In \cref{sec:interpreting-open-intrinsic} we apply the same approach to the substitution function and normalizer from \cref{sec:interpreting-open}.

The logical connectives in \cref{fig:connectives} assume the existence of a union-like operation for lists of names
%
\begin{code}[hide]
record NameSetIntf (Name : Set) : Set₁ where
  field
\end{code}
\begin{code}[inline]
    _⊔_ : List Name → List Name → List Name
\end{code}
%
\ with accompanying laws proving that the operation is \emph{commutative} and \emph{monoidal} (i.e., \emph{associative} and the empty list is the \emph{identity element} w.r.t. \aF{⊔}).
It also assumes a difference-like operation
%
\begin{code}[hide]
    -- ⊔ is commutative-monoidal
    ⊔-id : (xs ys : List Name) → xs ⊔ ys ≡ [] → xs ≡ [] × ys ≡ []
    []-idˡ : LeftIdentity _≡_ [] _⊔_
    ⊔-comm : Commutative _≡_ _⊔_
    ⊔-assoc : Associative _≡_ _⊔_
\end{code}
\begin{code}[inline]
    _∖_ : List Name → List Name → List Name
\end{code}
%
\ with accompanying laws that characterize its difference-like nature (the laws can be found in the source code of the paper).
%
\begin{code}[hide]
    -- ∖ is difference-like
    ∖-distrʳ : _DistributesOverʳ_ _≡_ _∖_ _⊔_
    ∖-subtractive : (xs : List Name) → xs ∖ xs ≡ []
    ∖-idemʳ : (xs ys : List Name) → (xs ∖ ys) ∖ ys ≡ xs ∖ ys
    ∖-swapʳ : (xs ys zs : List Name) → (xs ∖ ys) ∖ zs ≡ (xs ∖ zs) ∖ ys
    ∖-single : (x y : Name) → [ x ] ∖ [ y ] ≡ [ x ]
    ∖[]-idʳ : RightIdentity _≡_ [] _∖_
    ∖-zeroˡ : LeftZero _≡_ [] _∖_

  []-idʳ : RightIdentity _≡_ [] _⊔_
  []-idʳ x rewrite ⊔-comm x [] = []-idˡ x
\end{code}
%
\begin{figure}
\centering
\begin{minipage}{0.495\linewidth}
\footnotesize
\begin{code}
  FVPred = List Name → Set

  _⇒_ : FVPred → FVPred → FVPred
  (P ⇒ Q) xs = P xs → Q xs
  
  ∀[_] : FVPred → Set
  ∀[ P ] = {xs : List Name} → P xs
  
  ε[_] : FVPred → Set
  ε[ P ] = P []

  One : Name → List Name → Set
  One x xs = xs ≡ [ x ]
\end{code}
\end{minipage}
\vline
\begin{minipage}{0.495\linewidth}
\footnotesize
\begin{code}
  record _∧_  (P Q : FVPred)
              (xs : List Name) : Set where
    constructor _∧_∣_
    field  {ys zs} : List Name
           px : P ys
           qx : Q zs
           φ  : xs ≡ ys ⊔ zs




  _─_ : FVPred → Name → FVPred
  (P ─ x) xs = P (xs ∖ [ x ])
\end{code}
\end{minipage}
\caption{Logical connectives for predicates over free variables}
\label{fig:connectives}
\end{figure}
%
\begin{code}[hide]
module TypedNormalizer (Name : Set) (_≡?_ : (x y : Name) → Dec (x ≡ y)) (NSI : NameSetIntf Name) where

  open NameSetIntf NSI

  subst′ = subst
  syntax subst′ P eq e = e ∶ P ∣ eq
\end{code}


\subsection{Normalizing Closed $\lambda$ Terms using Intrinsic Typing}
\label{sec:interpreting-closed-intrinsic}

Using the operations in \cref{fig:connectives}, we define a data type of $\lambda$ terms that is intrinsically typed by the set of free variables of the term:
%
\begin{code}
  data FV : List Name → Set where
    lam  : (x : Name) → ∀[ (FV ─ x)  ⇒ FV ]
    var  : (x : Name) → ∀[ One x     ⇒ FV ]
    app  : ∀[ (FV ∧ FV)              ⇒ FV ]
\end{code}
%
The only inhabitants of the type \ad{FV}~\ab{xs} are terms whose set of free variables is exactly \ab{xs}.

Using the \ad{FV} type, we can refine the type of the substitution function from \cref{sec:interpreting-closed} to make explicit the assumptions about closedness that were previously implicit.
The type and implementation of the function is given below, where each \af{⋯} represents an elided (but straightforward) Agda proof term which uses the laws about the \aF{⊔} and \aF{∖} operations to prove to Agda that the intrinsic typing is valid.\footnote{The \af{\$} operation is an infix operation for function application (akin to the operation by the same name in Haskell).}
\begin{AgdaAlign}
\begin{AgdaSuppressSpace}
\begin{code}[hide]
  ⋯ = Function.id
\end{code}
\begin{code}
  ⟦_/_⟧_ : ε[ FV ] → (x : Name) → ∀[ FV ⇒ (FV ─ x) ]
  ⟦ s / y ⟧ (lam x t) = case (x ≡? y) of λ where
    (yes φ)  → lam x $ t ∶ FV ∣ ⋯
\end{code}
\begin{code}[hide]
                                  (begin
                                     _
                                   ≡˘⟨ ∖-idemʳ _ _ ⟩
                                     _
                                   ≡˘⟨ cong (λ ■ → ((_ ∖ [ ■ ]) ∖ _)) (sym φ) ⟩
                                     _
                                   ∎)
\end{code}
\begin{code}
    (no ¬φ)  → lam x $ (⟦ s / y ⟧ t) ∶ FV ∣ ⋯
\end{code}
\begin{code}[hide]
                                            ∖-swapʳ _ _ _
\end{code}
\begin{code}
  ⟦ s / y ⟧ (var x φ₁) = case (x ≡? y) of λ where
    (yes φ₂)   → s ∶ FV   ∣  ⋯
\end{code}
\begin{code}[hide]

                              (begin
                                 []
                               ≡˘⟨ ∖-subtractive _ ⟩
                                 _
                               ≡˘⟨ cong (_∖ _) φ₁ ⟩
                                 _
                               ≡⟨ cong (λ ■ → _ ∖ [ ■ ]) φ₂ ⟩
                                 _
                               ∎)
\end{code}
\begin{code}
    (no  ¬φ₂)  → var x $ ⋯
\end{code}
\begin{code}[hide]
                              (begin
                                  _
                               ≡⟨ cong (_∖ _) φ₁ ⟩
                                 _
                               ≡⟨ ∖-single _ _ ⟩
                                 _
                               ∎)
  ⟦ s / y ⟧ (app (t₁ ∧ t₂ ∣ φ)) =
    app $ (⟦ s / y ⟧ t₁) ∧ (⟦ s / y ⟧ t₂)  ∣  ⋯
\end{code}
\begin{code}[hide]
                               (begin
                                 _
                               ≡⟨ cong (_∖ _) φ ⟩
                                 _
                               ≡⟨ ∖-distrʳ _ _ _ ⟩
                                 _
                               ∎)
\end{code}
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%
The type signature of the substitution function above says that the term being substituted for has no free variables (\af{ε[~FV~]}), and that the final set of free variables is the set of free variables of the term being substituted in minus the variable $x$ that was substituted (\af{∀[~FV~⇒~}\as{(}\af{FV}~─~\ab{x}\as{)}~\af{]}).
Agda automatically checks for us that the substitution function inhabits this type, thereby showing that the substitution function is capture avoiding by construction.

The normalizer from \cref{sec:interpreting-closed} can be similarly generalized to show that normalizing a closed term is guaranteed to yield a normal form (value), where a normal form is a (closed) $\lambda$ value given by the \ad{NF} type:
\begin{code}
  data Val : Set where
    lam : (x : Name) → ε[ FV ─ x ] → Val
\end{code}
%
The type signature of the generalized normalizer is given below.
Its definition is case-by-case similar to the normalizer from \cref{sec:interpreting-closed}, and is elided for brevity.
%
\begin{code}
  {-# NON_TERMINATING #-}
  normalize : ε[ FV ] → Val
\end{code}
%
Unlike the normalizer from \cref{sec:interpreting-closed}, which was partial, \af{normalize} is a \emph{total}, possibly non-terminating function, because the type \af{ε[~FV~]} intrinsically guarantees that the input term has no free variables.
%
\begin{code}[hide]
  normalize (lam x e) = lam x e
  normalize (var x ()) 
  normalize (app (e₁ ∧ e₂ ∣ φ)) = case (normalize (e₁ ∶ FV ∣ proj₁ (⊔-id _ _ (sym φ))))
                                    of λ where
      (lam x e) →
        let v = Val2FV (normalize (e₂ ∶ FV ∣ proj₂ (⊔-id _ _ (sym φ))))
        in normalize ((⟦ v / x ⟧ e) ∶ FV ∣ (begin
                                             _
                                            ≡⟨ cong (_∖ _) (∖-zeroˡ _) ⟩
                                              _
                                            ≡⟨ ∖-zeroˡ _ ⟩
                                              _
                                            ∎))
        where
          Val2FV : Val → ε[ FV ]
          Val2FV (lam x e) = lam x e
\end{code}


\subsection{Normalizing Open $\lambda$ Terms using Intrinsic Typing}
\label{sec:interpreting-open-intrinsic}

We now show that our normalizer from \cref{sec:interpreting-open} provides similar guarantees as the normalizer for closed terms in \cref{sec:interpreting-closed-intrinsic}.
To this end we enrich the \ad{FV} type from before by an additional constructor for values given by a type parameter \ab{V}~\as{:}~\ad{Set}:\footnote{Here \af{const}~\as{:~\{}\ab{A~B}~\as{:}~\ad{Set}\as{\}~→}~\ab{A}~\as{→}~\ab{B}~\as{→}~\ab{A} is the \emph{constant function} which ignores its second argument, and always returns its first argument.}
%
\begin{code}
  data FVV (V : Set) : List Name → Set where
    lam  : (x : Name) → ∀[ (FVV V ─ x)  ⇒ FVV V ]
    var  : (x : Name) → ∀[ One x        ⇒ FVV V ]
    app  : ∀[ (FVV V ∧ FVV V)           ⇒ FVV V ]
    val  : ε[ const V                   ⇒ FVV V ]
\end{code}
%
The \ac{val} case says that values have \emph{no free variables}.

Using this type of terms, we define a substitution function with a similar type signature as the substitution function from \cref{sec:interpreting-closed-intrinsic}.
It also has similar cases which we elide, except for the case for the \ac{val} constructor:\footnote{The \as{\_} in \af{FVV}~\as{\_} represents a term that we ask Agda to automatically infer for us.  In this case, Agda infers that it is the implicitly parameter type \ab{V}~\as{:}~\ad{Set}.}
%
\begin{AgdaAlign}
\begin{AgdaSuppressSpace}
\begin{code}
  ⦉_/_⦊_  : {V : Set}
          → ε[ FVV V ] → (x : Name) → ∀[ FVV V ⇒ (FVV V ─ x) ]
\end{code}
\begin{code}[hide]
  ⦉ s / y ⦊ (app (t₁ ∧ t₂ ∣ φ)) =
    app ( (⦉ s / y ⦊ t₁)
        ∧ (⦉ s / y ⦊ t₂)
        ∣ (begin
              _
            ≡⟨ cong (_∖ _) φ ⟩
              _
            ≡⟨ ∖-distrʳ _ _ _ ⟩
              _
            ∎) )
  ⦉ s / y ⦊ (lam x t) = case (x ≡? y) of λ where
    (yes φ) → lam x (t ∶ FVV _ ∣ (begin
                                    _
                                  ≡˘⟨ ∖-idemʳ _ _ ⟩
                                    _
                                  ≡˘⟨ cong (λ ■ → ((_ ∖ [ ■ ]) ∖ _)) (sym φ) ⟩
                                    _
                                  ∎))
    (no ¬φ) → lam x ((⦉ s / y ⦊ t) ∶ FVV _ ∣ (∖-swapʳ _ _ _))
  ⦉ s / y ⦊ (var x φ₁) = case (x ≡? y) of λ where
    (yes φ₂) → s ∶ FVV _ ∣ (begin
                                 []
                               ≡˘⟨ ∖-subtractive _ ⟩
                                 _
                               ≡˘⟨ cong (_∖ _) φ₁ ⟩
                                 _
                               ≡⟨ cong (λ ■ → _ ∖ [ ■ ]) φ₂ ⟩
                                 _
                               ∎)
    (no ¬φ₂) → var x (begin
                         _
                      ≡⟨ cong (_∖ _) φ₁ ⟩
                        _
                      ≡⟨ ∖-single _ _ ⟩
                        _
                      ∎)
\end{code}
\begin{code}
  ⦉ s / y ⦊ (val v) = val v ∶ FVV _ ∣ ⋯
\end{code}
\begin{code}[hide]
                                     (sym (∖-zeroˡ _))
\end{code}
\end{AgdaSuppressSpace}
\end{AgdaAlign}
%
As with the substitution function from \cref{sec:interpreting-closed}, we do not propagate substitutions into values.
Thus the only difference between the substitution function in \cref{sec:interpreting-closed-intrinsic} and the substitution function above is that the function above has a more liberal notion of what it means for a term to be closed; namely, it is either a plain closed term, or a value.

Using this substitution function we generalize the type of the normalizer from \cref{sec:interpreting-open} to operate on intrinsically typed terms.
Unlike the normalizer in \cref{sec:interpreting-closed-intrinsic}, the normalizer below takes \emph{open terms} as input and normalizes these to weak head normal forms given by the following type:
\begin{code}
  data ValV : Set where
    lam : (x : Name) → ∀[ (FVV ValV ─ x)  ⇒ const ValV ]
    var : Name                            → ValV
    app : ValV → ValV                     → ValV
\end{code}
The normalizer is given by the \af{normalizeV} function:
\begin{AgdaAlign}
\begin{AgdaSuppressSpace}
\begin{code}
  {-# NON_TERMINATING #-}
  normalizeV : ∀[ FVV ValV ⇒ const ValV ]
  normalizeV (app (t₁ ∧ t₂ ∣ φ)) = case (normalizeV t₁) of λ where
    (lam x t)  → normalizeV $ (⦉ val (normalizeV t₂) / x ⦊ t) ∶ FVV _ ∣ ⋯
\end{code}
\begin{code}[hide]
                                                            (∖-idemʳ _ _)
\end{code}
\begin{code}
    v₁         → app v₁ (normalizeV t₂)
  normalizeV (lam x t)  = lam x t
  normalizeV (val v)    = v
  normalizeV (var x φ)  = var x
\end{code}
\end{AgdaSuppressSpace}
\end{AgdaAlign}
The function is case-by-case similar to the function from \cref{sec:interpreting-open}.
However, thanks to its intrinsic typing information, we are guaranteed that (1) normalization only ever applies substitutions that are capture avoiding, since the substitution function only propagates closed terms past $\lambda$ bindings; and (2) normalization may yield values that correspond to open terms.
All without any fiddly renaming.
