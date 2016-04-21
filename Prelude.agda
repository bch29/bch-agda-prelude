module Prelude where

--------------------------------------------------------------------------------
--  Imports
--------------------------------------------------------------------------------

import Level                                 as Level

import Relation.Nullary                      as Nullary
import Relation.Binary                       as Binary
import Relation.Binary.Flip                  as Flip
import Relation.Binary.PropositionalEquality as PropEq
import Algebra                               as Algebra
import Algebra.Structures                    as AlgStructures

import Function                              as Function

import Data.Unit                             as Unit
import Data.Empty                            as Empty
import Data.Nat                              as Nat
import Data.Nat.Properties                   as NatProperties
import Data.Fin                              as Fin
import Data.List                             as List
import Data.List.Any                         as Any
import Data.Vec                              as Vec
import Data.Maybe                            as Maybe
import Data.Product                          as Product
import Data.Sum                              as Sum
import Data.Bool                             as Bool

--------------------------------------------------------------------------------
--  Re-exports
--------------------------------------------------------------------------------

open Level    public
  using (Lift; lift; lower; Level; _⊔_)
  renaming (zero to lzero; suc to lsuc)

open Nullary  public using (¬_; Dec; yes; no)

open Binary   public
  using ( Decidable; IsEquivalence; IsDecEquivalence; Setoid
        ; IsStrictTotalOrder; StrictTotalOrder
        ; IsPreorder; Preorder)

module EqReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open import Relation.Binary.EqReasoning S public
module PreorderReasoning {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where
  open import Relation.Binary.PreorderReasoning P public

open PropEq   public
  using (_≡_; cong; subst; module ≡-Reasoning; Reveal_·_is_; inspect)
  renaming ( refl to ≡refl; sym to ≡sym; trans to ≡trans
           ; setoid to ≡-setoid; [_] to revealed)

open Algebra public
  using (Semigroup; Monoid; CommutativeMonoid; Semiring; CommutativeSemiring)
open AlgStructures public
  using (IsSemigroup; IsMonoid; IsCommutativeMonoid; IsSemiring; IsCommutativeSemiring)

open Function public using (const; id; _∘_; flip; _$_; _⟨_⟩_)

open Unit     public using (⊤; tt)
open Empty    public using (⊥; ⊥-elim)
open Nat      public using (ℕ; suc; zero; _≤_)
open Fin      public using (Fin; suc; zero)
open List     public using (List; []; _∷_; _++_; map; concat; foldr; foldl) renaming ([_] to singleton)
open Any      public using (Any; here; there; any) renaming (index to indexAny)
open Vec      public using (Vec; []; _∷_; tabulate; replicate) renaming (lookup to indexVec)
open Maybe    public using (Maybe; just; nothing; from-just; From-just)
open Product  public
  using (Σ; _×_; _,_; ,_; ∃; ∃₂; curry; uncurry; Σ-syntax)
  renaming (proj₁ to fst; proj₂ to snd)
open Sum      public using (_⊎_) renaming (inj₁ to left; inj₂ to right)
open Bool     public
  using (Bool; true; false; not; _xor_; if_then_else_)
  renaming (T to IsTrue; _∧_ to _&&_; _∨_ to _||_)

--------------------------------------------------------------------------------
--  Semigroup, Monoid and Semiring typeclasses
--------------------------------------------------------------------------------

record HasSemigroup {a} (A : Set a) : Set a where
  constructor mkSemigroup

  infixr 4 _<>_
  field
    {_<>_} : A → A → A
    isSemigroup : IsSemigroup _≡_ _<>_

  open IsSemigroup isSemigroup public

  semigroup : Semigroup _ _
  semigroup = record { isSemigroup = isSemigroup }

open HasSemigroup {{...}} public using (_<>_)

record HasMonoid {a} (A : Set a) : Set a where
  constructor mkMonoid

  field
    {mappend} : A → A → A
    {mempty} : A
    isMonoid : IsMonoid _≡_ mappend mempty

  open IsMonoid isMonoid public

  hasSemigroup : HasSemigroup A
  hasSemigroup = mkSemigroup isSemigroup

  open HasSemigroup hasSemigroup public using (semigroup)

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

open HasMonoid {{...}} public using (mempty; mappend)

instance
  List-monoid : ∀ {a}{A : Set a} → HasMonoid (List A)
  List-monoid = mkMonoid (Monoid.isMonoid (List.monoid _))

  ⊤-monoid : HasMonoid ⊤
  ⊤-monoid = mkMonoid (record
    { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc = λ _ _ _ → ≡refl
      ; ∙-cong = λ _ _ → ≡refl
      }
    ; identity = const ≡refl , const ≡refl })

record HasSemiring {a} (A : Set a) : Set a where
  constructor mkSemiring

  infixl 7 _*_
  infixl 6 _+_

  field
    {_+_ _*_} : A → A → A
    {zro one} : A
    isSemiring : IsSemiring _≡_ _+_ _*_ zro one

  open IsSemiring isSemiring public

  +-hasMonoid = mkMonoid +-isMonoid
  *-hasMonoid = mkMonoid *-isMonoid

  open HasMonoid +-hasMonoid public
    using ()
    renaming (semigroup to +-semigroup; monoid to +-monoid)

  open HasMonoid *-hasMonoid public
    using ()
    renaming (semigroup to *-semigroup; monoid to *-monoid)

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

open HasSemiring {{...}} public using (_+_; _*_; zro; one)

instance
  ℕ-semiring : HasSemiring ℕ
  ℕ-semiring = mkSemiring $
    Algebra.CommutativeSemiring.isSemiring NatProperties.commutativeSemiring

{-# DISPLAY Nat._+_ x y = x + y #-}
{-# DISPLAY Algebra.CommutativeSemiring._+_ _ x y = x + y #-}
{-# DISPLAY Semiring._+_ _ x y = x + y #-}
{-# DISPLAY HasSemiring._+_ _ x y = x + y #-}
{-# DISPLAY Nat._*_ x y = x * y #-}
{-# DISPLAY Algebra.CommutativeSemiring._*_ _ x y = x * y #-}
{-# DISPLAY Semiring._*_ _ x y = x * y #-}
{-# DISPLAY HasSemiring._*_ _ x y = x * y #-}

--------------------------------------------------------------------------------
--  Extra data definitions
--------------------------------------------------------------------------------

_^_ : ∀ {a}{A : Set a}{{_ : HasSemiring A}} → A → ℕ → A
a ^ zero = one
a ^ suc n = a * (a ^ n)

Either : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Either = _⊎_

lmap : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
       → (A → B) → A ⊎ C → B ⊎ C
lmap f (left x) = left (f x)
lmap f (right y) = right y

rmap : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
       → (A → B) → C ⊎ A → C ⊎ B
rmap f (left x) = left x
rmap f (right y) = right (f y)

either : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}
       → (A → C) → (B → C)
       → A ⊎ B → C
either f g (left x) = f x
either f g (right y) = g y

module _ {a b}{A : Set a}{B : Set b} where
  swap-either : A ⊎ B → B ⊎ A
  swap-either = either right left

  swap-either-inverse : ∀ e → (either right left ∘ swap-either) e ≡ e
  swap-either-inverse (left x) = ≡refl
  swap-either-inverse (right y) = ≡refl

record ⊤′ {a} : Set a where
  constructor tt

data ⊥′ {a} : Set a where

instance
  ⊤-instance : ⊤
  ⊤-instance = _

  ⊤′-instance : ∀ {a} → ⊤′ {a}
  ⊤′-instance = _

--------------------------------------------------------------------------------
--  Working with instance arguments
--------------------------------------------------------------------------------

it : ∀ {a}{A : Set a} {{that : A}} → A
it {{x}} = x

toInstanceArg : ∀ {a b}{A : Set a}{B : A → Set b} → (∀ x → B x) → ({{x : A}} → B x)
toInstanceArg f = f it

fromInstanceArg : ∀ {a b}{A : Set a}{B : A → Set b} → (∀ {{x : A}} → B x) → (∀ x → B x)
fromInstanceArg f x = f

--------------------------------------------------------------------------------
--  Equivalence relations
--------------------------------------------------------------------------------

open IsEquivalence {{...}} public

instance
  ≡-equivalence : ∀ {a}{A : Set a} → IsEquivalence {A = A} _≡_
  ≡-equivalence = PropEq.isEquivalence

mkSetoid : ∀ {a ℓ}{A : Set a}{_≈_ : A → A → Set ℓ} → IsEquivalence _≈_ → Setoid _ _
mkSetoid equiv = record { isEquivalence = equiv }

--------------------------------------------------------------------------------
--  Absurdity
--------------------------------------------------------------------------------

record Absurd {a} (A : Set a) : Set a where
  constructor mkAbsurd
  field
    ¬A : ¬ A

  absurd : ∀ {w}{Whatever : Set w} → A → Whatever
  absurd x = ⊥-elim (¬A x)

open Absurd {{...}} public using (absurd)

absurd! : ∀ {a}{A : Set a}{{it's-absurd : Absurd A}} → ∀ {w}{Whatever : Set w}{{absurdity : A}} → Whatever
absurd! {{absurdity = x}} = absurd x

module _ {a ℓ}{A : Set a}{_≈_ : A → A → Set ℓ}{{equiv : IsEquivalence _≈_}} where
  sym-absurd : ∀ {x y} → {{x≈y-absurd : Absurd (x ≈ y)}} → Absurd (y ≈ x)
  sym-absurd {{mkAbsurd ¬x≈y}} = mkAbsurd (¬x≈y ∘ sym)

instance
  ⊥-absurd : Absurd ⊥
  ⊥-absurd = mkAbsurd id

  ⊥′-absurd : Absurd ⊥
  ⊥′-absurd = mkAbsurd (λ ())

  false≡true-absurd : Absurd (false ≡ true)
  false≡true-absurd = mkAbsurd (λ ())

  true≡false-absurd : Absurd (true ≡ false)
  true≡false-absurd = sym-absurd

⊥→ℕ : ⊥ → ℕ
⊥→ℕ = absurd {{⊥-absurd}}

--------------------------------------------------------------------------------
--  Decidable (homogeneous propositional) Equality
--------------------------------------------------------------------------------

record Eq {a} (A : Set a) : Set a where
  field
    isDecEquivalence : IsDecEquivalence {A = A} _≡_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid _ _
  Setoid.Carrier setoid = A
  Setoid._≈_ setoid = _≡_
  Setoid.isEquivalence setoid = isEquivalence

open Eq {{...}} public using (_≟_)

instance
  ℕ-eq : Eq ℕ
  IsDecEquivalence.isEquivalence (Eq.isDecEquivalence ℕ-eq) = it
  IsDecEquivalence._≟_ (Eq.isDecEquivalence ℕ-eq) = Nat._≟_

--------------------------------------------------------------------------------
--  Decidable Ordering
--------------------------------------------------------------------------------

record Ord {a ℓ} (A : Set a) : Set (lsuc (a ⊔ ℓ)) where
  constructor mkOrd

  infix 4 _<_ _>_ _>?_

  field
    {_<_} : A → A → Set ℓ
    isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_

  open IsStrictTotalOrder isStrictTotalOrder public

  _>_ : A → A → Set ℓ
  _>_ = flip _<_

  _>?_ : Decidable _>_
  _>?_ = Flip.decidable _ _<?_

  eq : Eq A
  Eq.isDecEquivalence eq = isDecEquivalence

open Ord {{...}} public using (_<_; _<?_; compare; _>_)

{-# DISPLAY Ord._<_ _ x y = x < y #-}
{-# DISPLAY Ord._>_ _ x y = x > y #-}
{-# DISPLAY StrictTotalOrder._<_ _ x y = x < y #-}

instance
  import Data.Nat.Properties as ℕProp
  open Binary using (StrictTotalOrder)

  ℕ-ord : Ord ℕ
  ℕ-ord = mkOrd $ StrictTotalOrder.isStrictTotalOrder ℕProp.strictTotalOrder

-- allow ordering on known naturals to be resolved by instance search

instance
  z≤n : ∀ {n} → zero ≤ n
  z≤n = Nat.z≤n

  s≤s : ∀ {n m} {{_ : n ≤ m}} → suc n ≤ suc m
  s≤s = Nat.s≤s it

--------------------------------------------------------------------------------
--  Functors, applicatives and monoids
--------------------------------------------------------------------------------

record Functor {ℓ f} (F : Set ℓ → Set f) : Set (lsuc ℓ ⊔ f) where
  field
    fmap : ∀ {A B : Set ℓ} → (A → B) → F A → F B

  _<$>_ = fmap

open Functor {{...}} public using (fmap; _<$>_)

record Applicative {ℓ f} (F : Set ℓ → Set f) : Set (lsuc ℓ ⊔ f) where
  field
    pure : ∀ {A : Set ℓ} → A → F A
    ap : ∀ {A B : Set ℓ}
         → F (A → B) → F A → F B

  functor : Functor F
  Functor.fmap functor f x = ap (pure f) x

record Monad {ℓ f} (F : Set ℓ → Set f) : Set (lsuc ℓ ⊔ f) where
  field
    return : ∀ {A : Set ℓ} → A → F A
    _>>=_ : ∀ {A B : Set ℓ}
           → F A → (A → F B) → F B

  applicative : Applicative F
  Applicative.pure applicative = return
  Applicative.ap applicative f x =
    f >>= λ f′ →
    x >>= λ x′ →
    return (f′ x′)

  open Applicative applicative public using (functor)

open Monad {{...}} public using (return; _>>=_)

join : ∀ {ℓ}{M : Set ℓ → Set ℓ}{{monad : Monad M}} → ∀ {A} → M (M A) → M A
join mmx = mmx >>= id

instance
  List-monad : ∀ {ℓ} → Monad {ℓ} List
  Monad.return List-monad = singleton
  Monad._>>=_ List-monad xs f = List.concat (List.map f xs)

  List-applicative = λ {ℓ} → Monad.applicative {ℓ} List-monad
  List-functor = λ {ℓ} → Monad.functor {ℓ} List-monad

  Vec-functor : ∀ {ℓ n} → Functor (λ A → Vec {ℓ} A n)
  Functor.fmap Vec-functor = Vec.map

--------------------------------------------------------------------------------
--  Numbers
--------------------------------------------------------------------------------

record Number {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : ℕ → Set a
    fromNat : ∀ n → {{constraint : Constraint n}} → A

  NoConstraint : Set a
  NoConstraint = ∀ {n} → Constraint n

open Number {{...}} public using (fromNat)

{-# BUILTIN FROMNAT fromNat #-}

instance
  ℕ-number : Number ℕ
  Number.Constraint ℕ-number _ = ⊤
  Number.fromNat ℕ-number n = n

  Fin-number : ∀ {n} → Number (Fin n)
  Number.Constraint (Fin-number {n}) m = m < n
  Number.fromNat Fin-number m {{n<m}} = Fin.fromℕ≤ n<m
